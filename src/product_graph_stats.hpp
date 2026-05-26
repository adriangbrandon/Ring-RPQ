/*
 * product_graph_stats.hpp
 *
 * Construye el grafo producto completo a partir de un nodo inicial
 * (similar a path_const_s_to_var_o) y, para cada nodo del grafo que
 * lleve a alguna solución, calcula:
 *
 *   - n_solutions  : cuántas soluciones son alcanzables desde ese nodo.
 *   - min_dist     : mínimo número de pasos para llegar a la solución
 *                    más cercana (0 si el propio nodo es solución).
 *   - max_dead_end : máximo número de pasos que hay que dar antes de
 *                    detectar que un camino NO lleva a ninguna solución
 *                    (máxima profundidad de los sub-árboles sin solución).
 *
 * El resultado se devuelve como una lista de adyacencia.
 */

#ifndef PRODUCT_GRAPH_STATS_HPP
#define PRODUCT_GRAPH_STATS_HPP

#include <cstdint>
#include <vector>
#include <unordered_map>
#include <stack>
#include <limits>
#include <chrono>

#include "bwt.hpp"
#include "bwt-C-nose.hpp"
#include "bwt_interval.hpp"
#include "utils.hpp"
#include "RpqAutomata.hpp"
#include "RpqTree.hpp"
#include "query_config.hpp"
#include "parse_query.cpp"
#include "wt_helper.hpp"
#include "selectivity.hpp"

using namespace std::chrono;

// ---------------------------------------------------------------------------
// Tipos de datos
// ---------------------------------------------------------------------------

/// Arista del grafo producto
typedef struct {
    uint64_t tgt;    ///< Índice del nodo destino en adj_lists / node_stats
    uint32_t label;  ///< Predicado que origina la arista
} pg_edge_type;

/// Estadísticas por nodo del grafo producto
typedef struct {
    uint64_t id_state;     ///< Codificación (nodo_grafo | estado_NFA)
    uint64_t n_solutions;  ///< Número de soluciones alcanzables
    uint32_t min_dist;     ///< Pasos mínimos a la solución más cercana
    uint32_t max_dead_end; ///< Máxima profundidad de caminos sin solución
} pg_node_stats_type;

// ---------------------------------------------------------------------------
// Estado interno para el recorrido BWT
// ---------------------------------------------------------------------------
typedef struct {
    bwt_interval interval;
    word_t       current_D;
    uint         level;
    uint32_t     node;
    uint32_t     label;
} pg_interval_state_type;

// ---------------------------------------------------------------------------
// Clase principal
// ---------------------------------------------------------------------------
class product_graph_stats {

    bwt_nose L_S;
    bwt      L_P;

    uint64_t real_max_P;
    uint64_t max_S;
    uint64_t max_P;
    uint64_t max_O;
    uint64_t nTriples;

public:
    product_graph_stats() {}

    product_graph_stats(vector<spo_triple>& D, bool verbose = true) {
        // --- construcción del índice (igual que ring_rpq_paths) ---
        uint64_t i;
        uint64_t d = D.size();
        spo_triple triple_aux;

        max_S = get<0>(D[0]);
        max_P = get<1>(D[0]);
        max_O = get<2>(D[0]);
        for (i = 1; i < D.size(); i++) {
            if (max_S < get<0>(D[i])) max_S = get<0>(D[i]);
            if (max_P < get<1>(D[i])) max_P = get<1>(D[i]);
            if (max_O < get<2>(D[i])) max_O = get<2>(D[i]);
        }
        real_max_P = max_P;

        for (uint64_t j = 0; j < d; j++) {
            triple_aux = D[j];
            D.push_back(spo_triple(get<2>(D[j]), get<1>(D[j]), get<0>(D[j])));
            get<0>(D[j]) = get<0>(triple_aux);
            get<1>(D[j]) = get<1>(D[j]) + real_max_P;
            get<2>(D[j]) = get<2>(triple_aux);
        }
        D.shrink_to_fit();

        max_S = get<0>(D[0]); max_P = get<1>(D[0]); max_O = get<2>(D[0]);
        for (i = 1; i < D.size(); i++) {
            if (max_S < get<0>(D[i])) max_S = get<0>(D[i]);
            if (max_P < get<1>(D[i])) max_P = get<1>(D[i]);
            if (max_O < get<2>(D[i])) max_O = get<2>(D[i]);
        }

        {
            sdsl::bit_vector bv_s(max_S + 1, 0), bv_o(max_O + 1, 0);
            for (i = 0; i < D.size(); i++) { bv_s[get<0>(D[i])] = 1; bv_o[get<2>(D[i])] = 1; }
            for (i = 1; i < max_S + 1; i++) if (!bv_s[i]) D.push_back(spo_triple(i, max_P+1, max_O+1));
            for (i = 1; i < max_O + 1; i++) if (!bv_o[i]) D.push_back(spo_triple(max_O+1, max_P+1, i));
        }
        max_S++; max_O++; max_P++;

        uint64_t n = nTriples = D.size();
        uint64_t alphabet_SO = (max_S < max_O) ? max_O : max_S;
        std::vector<uint32_t> M_O(alphabet_SO + 1, 0), M_P(max_P + 1, 0);
        for (i = 0; i < D.size(); i++) { M_O[get<2>(D[i])]++; M_P[get<1>(D[i])]++; }
        M_O.shrink_to_fit(); M_P.shrink_to_fit();

        // Orden OSP → L_P
        sort(D.begin(), D.end(), [](const spo_triple& a, const spo_triple& b){
            return std::tie(get<2>(a),get<0>(a),get<1>(a)) < std::tie(get<2>(b),get<0>(b),get<1>(b));
        });
        {
            vector<uint64_t> new_C_P;
            uint64_t cur = 1; new_C_P.push_back(0); new_C_P.push_back(cur);
            for (uint64_t c = 2; c <= alphabet_SO; c++) { cur += M_O[c-1]; new_C_P.push_back(cur); }
            new_C_P.push_back(n+1); new_C_P.shrink_to_fit(); M_O.clear();
            sdsl::int_vector<> new_P(n+1); new_P[0] = 0;
            for (i = 1; i <= n; i++) new_P[i] = get<1>(D[i-1]);
            sdsl::util::bit_compress(new_P);
            L_P = bwt(new_P, new_C_P);
        }

        // Orden POS → L_S
        stable_sort(D.begin(), D.end(), [](const spo_triple& a, const spo_triple& b){
            return get<1>(a) < get<1>(b);
        });
        {
            vector<uint64_t> new_C_S;
            uint64_t cur = 1; new_C_S.push_back(0); new_C_S.push_back(cur);
            for (uint64_t c = 2; c <= max_P; c++) { cur += M_P[c-1]; new_C_S.push_back(cur); }
            new_C_S.push_back(n+1); new_C_S.shrink_to_fit(); M_P.clear();
            sdsl::int_vector<> new_S(n+1); new_S[0] = 0;
            for (i = 1; i <= n; i++) new_S[i] = get<0>(D[i-1]);
            sdsl::util::bit_compress(new_S);
            L_S = bwt_nose(new_S, new_C_S);
        }
        if (verbose) cout << "-- product_graph_stats index built" << endl;
    }

    void save(const string& filename) {
        L_S.save(filename + ".bwts"); L_P.save(filename + ".bwtp");
        std::ofstream ofs(filename + ".nTriples");
        ofs << nTriples << "\n" << real_max_P << "\n" << max_S << "\n" << max_P << "\n" << max_O << "\n";
    }

    void load(const string& filename) {
        L_S.load(filename + ".bwts"); L_P.load(filename + ".bwtp");
        std::ifstream ifs(filename + ".nTriples");
        ifs >> nTriples >> real_max_P >> max_S >> max_P >> max_O;
    }

    uint64_t n_labels()  const { return max_P; }
    uint64_t n_triples() const { return nTriples; }

    // -----------------------------------------------------------------------
    // Métodos wrapper públicos: parsean la query, construyen el autómata
    // y llaman a compute() — misma interfaz que ring_rpq_paths.
    // -----------------------------------------------------------------------

    /** s constante, o variable (recorre hacia atrás desde s). */
    void rpq_compute_const_s_to_var_o(
            const std::string& rpq,
            std::unordered_map<std::string, uint64_t>& predicates_map,
            std::vector<word_t>& B_array,
            uint64_t initial_object,
            std::vector<std::vector<pg_edge_type>>& adj_lists,
            std::vector<pg_node_stats_type>& node_stats)
    {
        int64_t iii = rpq.size() - 1;
        std::string query = parse_reverse(rpq, iii, predicates_map, real_max_P);
        RpqAutomata A(query, predicates_map);
        if (A.getNumberStates() >= 16) {
            std::cout << "Error: more than 16 NFA states." << std::endl;
            return;
        }
        auto m = A.getB();
        for (auto& kv : m) L_P.mark<word_t>(kv.first, B_array, (word_t) kv.second);
        auto start = high_resolution_clock::now();
        compute(A, B_array, initial_object, adj_lists, node_stats, start);
        for (auto& kv : m) L_P.unmark<word_t>(kv.first, B_array);
    }

    /** s variable, o constante (recorre hacia adelante desde o). */
    void rpq_compute_var_s_to_const_o(
            const std::string& rpq,
            std::unordered_map<std::string, uint64_t>& predicates_map,
            std::vector<word_t>& B_array,
            uint64_t initial_object,
            std::vector<std::vector<pg_edge_type>>& adj_lists,
            std::vector<pg_node_stats_type>& node_stats)
    {
        int64_t iii = 0;
        std::string query = parse(rpq, iii, predicates_map, real_max_P);
        RpqAutomata A(query, predicates_map);
        if (A.getNumberStates() >= 16) {
            std::cout << "Error: more than 16 NFA states." << std::endl;
            return;
        }
        auto m = A.getB();
        for (auto& kv : m) L_P.mark<word_t>(kv.first, B_array, (word_t) kv.second);
        auto start = high_resolution_clock::now();
        compute(A, B_array, initial_object, adj_lists, node_stats, start);
        for (auto& kv : m) L_P.unmark<word_t>(kv.first, B_array);
    }

    // -----------------------------------------------------------------------
    // API pública principal
    // -----------------------------------------------------------------------

    /**
     * Construye el grafo producto completo empezando desde `initial_object`
     * con el autómata `A`, y calcula para cada nodo:
     *   - n_solutions  : soluciones alcanzables
     *   - min_dist     : pasos mínimos a solución
     *   - max_dead_end : máxima profundidad de caminos sin solución
     *
     * @param A              Autómata RPQ
     * @param B_array        Array de bits del autómata
     * @param initial_object Nodo de inicio en el grafo
     * @param adj_lists      [out] Lista de adyacencia del grafo producto completo
     * @param node_stats     [out] Estadísticas por nodo (indexadas igual que adj_lists)
     * @param start          Tiempo de inicio (para timeout)
     * @return true si se agotó el tiempo (TIME_OUT)
     */
    bool compute(RpqAutomata& A,
                 std::vector<word_t>& B_array,
                 uint32_t initial_object,
                 std::vector<std::vector<pg_edge_type>>& adj_lists,
                 std::vector<pg_node_stats_type>& node_stats,
                 high_resolution_clock::time_point start)
    {
        // -------------------------------------------------------------------
        // DFS en una sola pasada con frames ENTER/EXIT.
        // Al sacar un frame EXIT todos los hijos ya están procesados,
        // lo que permite calcular las estadísticas en la "vuelta" del DFS,
        // simulando el retorno de la recursión.
        // -------------------------------------------------------------------
        std::unordered_map<uint64_t, uint64_t> map_node; // id_state → índice base-0

        word_t initial_D = (word_t) A.getFinalStates();
        bool   timed_out = false;
        high_resolution_clock::time_point stop;

        struct DFSFrame {
            uint64_t parent_idx; // UINT64_MAX si es raíz
            uint32_t edge_label;
            pg_interval_state_type ist;
            bool processed;      // false = ENTER, true = EXIT
        };
        std::stack<DFSFrame> dfs;
        dfs.push({std::numeric_limits<uint64_t>::max(), 0,
                  pg_interval_state_type{
                      bwt_interval(L_P.get_C(initial_object), L_P.get_C(initial_object + 1) - 1),
                      initial_D, 0, initial_object, 0
                  }, false});

        while (!dfs.empty()) {
            auto frame = dfs.top(); dfs.pop();
            auto& ist     = frame.ist;
            auto id_state = encode_pg(ist.node, ist.current_D);

            // --- EXIT: vuelta de la recursión → calcular estadísticas ---
            if (frame.processed) {
                uint64_t my_idx = map_node[id_state];
                auto& st        = node_stats[my_idx];

                if (A.atFinal(ist.current_D, BWD)) {
                    st.n_solutions = 1;
                    st.min_dist    = 0;
                }

                uint32_t max_dead = 0;
                for (const auto& e : adj_lists[my_idx]) {
                    auto& child_st = node_stats[e.tgt];

                    st.n_solutions += child_st.n_solutions;

                    if (child_st.min_dist != std::numeric_limits<uint32_t>::max()) {
                        uint32_t candidate = child_st.min_dist + 1;
                        if (candidate < st.min_dist) st.min_dist = candidate;
                    }

                    uint32_t child_dead = child_st.max_dead_end + 1;
                    if (child_dead > max_dead) max_dead = child_dead;
                }
                st.max_dead_end = max_dead;
                continue;
            }

            // --- ENTER: primera visita al nodo ---
            bool already_visited = (map_node.find(id_state) != map_node.end());
            uint64_t my_idx;

            if (!already_visited) {
                my_idx = adj_lists.size();
                map_node[id_state] = my_idx;
                adj_lists.emplace_back();
                pg_node_stats_type st{};
                st.id_state     = id_state;
                st.n_solutions  = 0;
                st.min_dist     = std::numeric_limits<uint32_t>::max();
                st.max_dead_end = 0;
                node_stats.emplace_back(st);
            } else {
                my_idx = map_node[id_state];
            }

            // Registrar arista desde el padre
            if (frame.parent_idx != std::numeric_limits<uint64_t>::max()) {
                adj_lists[frame.parent_idx].push_back({my_idx, frame.edge_label});
            }

            if (already_visited) continue; // no expandir ni programar EXIT

            // Programar EXIT para cuando todos los hijos hayan terminado
            dfs.push({frame.parent_idx, frame.edge_label, ist, true});

            // Expandir hijos (en orden inverso para preservar orden de visita)
            std::vector<std::pair<pg_interval_state_type, uint32_t>> children;
            expand_node_collect(A, B_array, ist.current_D, ist.level, ist.interval, children);

            for (int ci = (int)children.size() - 1; ci >= 0; --ci) {
                dfs.push({my_idx, children[ci].second, children[ci].first, false});
            }

            stop = high_resolution_clock::now();
            if (duration_cast<microseconds>(stop - start).count() > TIME_OUT) {
                timed_out = true;
                break;
            }
        }


        return timed_out;
    }

    // -----------------------------------------------------------------------
    // Análisis de tunnels
    // -----------------------------------------------------------------------

    /**
     * Un tunnel es un camino maximal en el grafo "vivo" (subgrafo restringido
     * a nodos con n_solutions > 0) donde en cada nodo interno el camino está
     * forzado: el nodo tiene exactamente un hijo vivo (live_out == 1).
     * Esto captura ambos casos:
     *   - Nodo con un único hijo vivo (trivialmente forzado).
     *   - Nodo con varios hijos pero solo uno vivo (los demás tienen n_solutions==0
     *     y mueren tras max_dead_end pasos — ya calculado en node_stats).
     *
     * El parámetro k controla qué ramas muertas se toleran dentro de un tunnel:
     * un nodo v es un k-tunnel node si tiene live_out == 1 Y todos sus hijos
     * muertos (n_solutions == 0) tienen max_dead_end < k.
     *
     *   k = 0          → solo caminos forzados sin ninguna rama muerta.
     *   k = 1          → se toleran hojas muertas inmediatas (max_dead_end == 0).
     *   k = UINT32_MAX → se toleran ramas muertas de cualquier longitud
     *                    (comportamiento equivalente al original).
     *
     * Para que dos aristas consecutivas pertenezcan al MISMO tunnel, el nodo
     * intermedio debe tener también live_in == 1 (solo se puede llegar a él
     * desde un padre, por lo que no hay convergencia de caminos en ese punto).
     *
     * Resultado:
     *   - n_tunnels            : número de tunnels encontrados.
     *   - tunnel_edge_counts   : número de aristas en la espina de cada tunnel.
     *   - n_branch_edges       : aristas vivas en nodos con live_out > 1
     *                            (puntos de bifurcación reales).
     */
    struct TunnelInfo {
        uint64_t              n_tunnels;          ///< Número de tunnels
        std::vector<uint64_t> tunnel_edge_counts; ///< Aristas por tunnel
        uint64_t              n_branch_edges;     ///< Aristas vivas fuera de tunnels
    };

    /**
     * Devuelve el número de aristas del grafo vivo, es decir, las aristas
     * v→u donde tanto v como u tienen n_solutions > 0.
     * Son exactamente las aristas que hay que cubrir para llegar a todas
     * las soluciones (tunnels + bifurcaciones), sin contar las ramas muertas.
     */
    uint64_t live_edges(
        const std::vector<std::vector<pg_edge_type>>& adj_lists,
        const std::vector<pg_node_stats_type>&        node_stats) const
    {
        uint64_t count = 0;
        for (uint64_t v = 0; v < adj_lists.size(); v++) {
            if (node_stats[v].n_solutions == 0) continue;
            for (const auto& e : adj_lists[v])
                if (node_stats[e.tgt].n_solutions > 0) count++;
        }
        return count;
    }

    TunnelInfo analyze_tunnels(
        const std::vector<std::vector<pg_edge_type>>& adj_lists,
        const std::vector<pg_node_stats_type>&        node_stats,
        uint32_t k = std::numeric_limits<uint32_t>::max()) const
    {
        uint64_t n = adj_lists.size();

        // ---------------------------------------------------------------
        // Paso 1: calcular live_out y live_in en el grafo vivo
        // ---------------------------------------------------------------
        std::vector<uint32_t> live_out(n, 0);
        std::vector<uint32_t> live_in(n, 0);

        for (uint64_t v = 0; v < n; v++) {
            if (node_stats[v].n_solutions == 0) continue;
            for (const auto& e : adj_lists[v]) {
                if (node_stats[e.tgt].n_solutions > 0) {
                    live_out[v]++;
                    live_in[e.tgt]++;
                }
            }
        }

        // ---------------------------------------------------------------
        // Predicado: ¿es v un k-tunnel node?
        // Condición 1: v es un nodo vivo y tiene exactamente un hijo vivo.
        // Condición 2: cada hijo muerto u satisface max_dead_end[u] + 1 <= k,
        //              es decir, el coste de explorar esa rama desde v
        //              (1 paso para llegar a u + max_dead_end[u] pasos en u)
        //              no supera k. Equivale a max_dead_end[u] < k.
        // ---------------------------------------------------------------
        auto is_k_tunnel_node = [&](uint64_t v) -> bool {
            if (node_stats[v].n_solutions == 0) return false;
            if (live_out[v] != 1) return false;
            for (const auto& e : adj_lists[v]) {
                if (node_stats[e.tgt].n_solutions == 0 &&
                    node_stats[e.tgt].max_dead_end >= k) {
                    return false; // 1 + max_dead_end[u] > k: rama muerta demasiado larga
                }
            }
            return true;
        };

        // ---------------------------------------------------------------
        // Paso 2: encontrar tunnels
        // Un tunnel comienza en v cuando is_k_tunnel_node(v) y v NO es la
        // continuación de un tunnel previo.  Un nodo se marca como
        // continuación cuando se alcanza como único hijo vivo de su padre
        // Y además live_in[v] == 1 (un solo padre vivo → no hay convergencia).
        // ---------------------------------------------------------------
        TunnelInfo info{0, {}, 0};
        std::vector<bool> is_continuation(n, false);

        for (uint64_t v = 0; v < n; v++) {
            if (node_stats[v].n_solutions == 0) continue;
            if (!is_k_tunnel_node(v))           continue; // no es k-tunnel node
            if (is_continuation[v])             continue; // ya contado en otro tunnel

            // Seguir la cadena desde v
            uint64_t tunnel_len = 0;
            uint64_t cur = v;

            while (is_k_tunnel_node(cur)) {
                // Encontrar el único hijo vivo
                uint64_t nxt = std::numeric_limits<uint64_t>::max();
                for (const auto& e : adj_lists[cur]) {
                    if (node_stats[e.tgt].n_solutions > 0) { nxt = e.tgt; break; }
                }
                if (nxt == std::numeric_limits<uint64_t>::max()) break;

                tunnel_len++;

                // Extender el tunnel a través de nxt solo si live_in[nxt] == 1
                // (nxt solo es alcanzable desde cur → no hay convergencia)
                if (live_in[nxt] == 1) {
                    is_continuation[nxt] = true;
                    cur = nxt;
                } else {
                    break; // nxt es punto de convergencia: el tunnel termina aquí
                }
            }

            if (tunnel_len > 0) {
                info.n_tunnels++;
                info.tunnel_edge_counts.push_back(tunnel_len);
            }
        }

        // ---------------------------------------------------------------
        // Paso 3: contar aristas de bifurcación (live_out > 1)
        // ---------------------------------------------------------------
        for (uint64_t v = 0; v < n; v++) {
            if (node_stats[v].n_solutions == 0) continue;
            if (live_out[v] > 1) info.n_branch_edges += live_out[v];
        }

        return info;
    }

    // -----------------------------------------------------------------------
    // Utilidades de consulta
    // -----------------------------------------------------------------------

    /** Devuelve {nodos, aristas} del grafo producto construido. */
    std::pair<uint64_t, uint64_t>
    get_nodes_edges(const std::vector<std::vector<pg_edge_type>>& adj_lists) const {
        uint64_t edges = 0;
        for (const auto& al : adj_lists) edges += al.size();
        return {adj_lists.size(), edges};
    }

    /** Imprime el grafo producto con estadísticas por stdout. */
    void print(const std::vector<std::vector<pg_edge_type>>& adj_lists,
               const std::vector<pg_node_stats_type>& node_stats) const {
        uint node; uint8_t state;
        for (uint64_t i = 0; i < adj_lists.size(); i++) {
            const auto& st = node_stats[i];
            std::tie(node, state) = decode_pg(st.id_state);
            cout << "Node " << i
                 << "  (graph_node=" << node << ", nfa_state=" << state << ")"
                 << "  n_sol=" << st.n_solutions
                 << "  min_dist=";
            if (st.min_dist == std::numeric_limits<uint32_t>::max())
                cout << "INF";
            else
                cout << st.min_dist;
            cout << "  max_dead=" << st.max_dead_end
                 << "  edges→[";
            for (const auto& e : adj_lists[i])
                cout << e.tgt << "(lbl=" << e.label << ") ";
            cout << "]\n";
        }
    }

private:
    // -----------------------------------------------------------------------
    // Helpers internos
    // -----------------------------------------------------------------------

    inline uint64_t encode_pg(uint32_t id, word_t state) const {
        return ((uint64_t)id << (sizeof(word_t)*8)) | (state & ((0x1 << (sizeof(word_t)*8)) - 1));
    }

    inline std::pair<uint32_t, word_t> decode_pg(uint64_t id_state) const {
        uint32_t id  = (uint32_t)(id_state >> (sizeof(word_t)*8));
        word_t state = (word_t)(id_state & ((0x1 << (sizeof(word_t)*8)) - 1));
        return {id, state};
    }

    // Extrae predicados activos y genera los nodos hijo del grafo producto,
    // devolviéndolos en un vector para que el DFS los procese.
    void expand_node_collect(RpqAutomata& A,
                             std::vector<word_t>& B_array,
                             word_t current_D,
                             uint level,
                             bwt_interval& I_p,
                             std::vector<std::pair<pg_interval_state_type, uint32_t>>& children)
    {
        std::vector<std::pair<uint64_t, std::pair<uint64_t, uint64_t>>> pred_vec;
        L_P.all_active_p_values_in_range_test<word_t>(I_p.left(), I_p.right(),
                                                       B_array, current_D, pred_vec);
        for (const auto& pv : pred_vec) {
            auto interval = L_P.backward_step_test(I_p.left(), I_p.right(),
                                                    pv.first,
                                                    pv.second.first,
                                                    pv.second.second);
            uint64_t c = L_S.get_C(pv.first);
            auto subj_vec = L_S.all_values_in_range(c + interval.first, c + interval.second);
            word_t new_D  = (word_t) A.next(current_D, pv.first, BWD);

            for (const auto& s : subj_vec) {
                const auto lb = L_P.get_C(s);
                const auto rb = L_P.get_C(s + 1) - 1;
                pg_interval_state_type child_ist{
                    bwt_interval(lb, rb), new_D, level + 1,
                    static_cast<uint32_t>(s), static_cast<uint32_t>(pv.first)
                };
                children.push_back({child_ist, static_cast<uint32_t>(pv.first)});
            }
        }
    }

};

#endif // PRODUCT_GRAPH_STATS_HPP

