/*
 * triple_bwt_rpq.hpp
 * Copyright (C) 2021 Diego Arroyuelo
 * 
 * This is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * This software is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef RING_RPQ_PATHS
#define RING_RPQ_PATHS

#include <cstdint>
#include <chrono>
#include <codecvt>
#include <set>
#include <unordered_set>
#include <cstdio>
#include <cstdlib>
#include <sdsl/init_array.hpp>

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

#define ELEMENTS 0
#define RUN_QUERY 0

using namespace std::chrono;

typedef struct {
    bwt_interval interval;
    word_t current_D;
    uint level;
    uint node;
    uint label;
} interval_state_type;

typedef struct {
    uint64_t tgt;
    uint32_t label;
} edge_type;

typedef struct {
    uint64_t id_state; //id+state
    uint32_t label;
} id_state_label_type;

typedef struct {
    uint64_t id_state; //id+state
    uint64_t out_degree = 0;
} id_state_degree_type;

typedef struct {
    uint64_t node_pmr; //node in pmr
    uint64_t out_degree;
} info_type;

typedef struct {
    uint64_t element;
    std::vector<std::pair<uint64_t, uint64_t>> solutions;
} element_solution_type;

template<class Container = std::stack<interval_state_type>>
class ring_rpq_paths {
    bwt_nose L_S;
    bwt L_P;

    uint64_t real_max_P;

    uint64_t max_S;
    uint64_t max_P;
    uint64_t max_O;
    uint64_t nTriples;  // number of triples

public:


    ring_rpq_paths() { ; }


    // Assumes the triples have been stored in a vector<spo_triple>
    ring_rpq_paths(vector<spo_triple>& D, bool verbose = true)
    {
        uint64_t i, pos_c;
        vector<spo_triple>::iterator it, triple_begin, triple_end;
        uint64_t n;

        // for every triple, adds its reverse (using a predicate
        // shifted by max_P, so 1 becomes max_P+1 in the reverse,
        // and so on)

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

        if (verbose) cout << "  > Adding inverted edges";
        for (uint64_t i = 0; i < d; i++) {
            triple_aux = D[i];
            D.push_back(spo_triple(get<2>(D[i]), get<1>(D[i]), get<0>(D[i])));
            get<0>(D[i]) = get<0>(triple_aux);
            get<1>(D[i]) = get<1>(D[i]) + real_max_P;
            get<2>(D[i]) = get<2>(triple_aux);
        }
        D.shrink_to_fit();

        if (verbose) cout << "... [done]" << endl;
        max_S = get<0>(D[0]);
        max_P = get<1>(D[0]);
        max_O = get<2>(D[0]);

        for (i = 1; i < D.size(); i++) {
            if (max_S < get<0>(D[i])) max_S = get<0>(D[i]);
            if (max_P < get<1>(D[i])) max_P = get<1>(D[i]);
            if (max_O < get<2>(D[i])) max_O = get<2>(D[i]);
        }

        {
            bit_vector bv_s(max_S + 1, 0);
            for (i = 0; i < D.size(); i++) {
                bv_s[get<0>(D[i])] = 1;
            }

            bit_vector bv_o(max_O + 1, 0);
            for (i = 0; i < D.size(); i++) {
                bv_o[get<2>(D[i])] = 1;
            }

            uint64_t _c = 0;
            for (i = 1; i < max_S + 1; i++) {
                if (!bv_s[i]) {
                    D.push_back(spo_triple(i, max_P + 1, max_O + 1));
                    _c++;
                }
            }
            //cout << _c << " nodes are no subjects" << endl;

            _c = 0;
            for (i = 1; i < max_O + 1; i++) {
                if (!bv_o[i]) {
                    D.push_back(spo_triple(max_O + 1, max_P + 1, i));
                    _c++;
                }
            }

            //cout << _c << " nodes are no objects" << endl;
        }

        max_S++;
        max_O++;
        max_P++;

        triple_begin = D.begin();
        triple_end = D.end();

        if (verbose) cout << "  > Triples set = " << D.size() * sizeof(spo_triple) << " bytes" << endl;
        fflush(stdout);


        n = nTriples = triple_end - triple_begin;

        if (verbose) cout << "  > Determining number of elements per symbol";
        fflush(stdout);
        uint64_t alphabet_SO = (max_S < max_O) ? max_O : max_S;

        std::vector<uint32_t> M_O(alphabet_SO + 1, 0), M_P(max_P + 1, 0);

        for (i = 0; i < D.size(); i++) {
            M_O[std::get<2>(D[i])]++;
            M_P[std::get<1>(D[i])]++;
        }

        M_O.shrink_to_fit();
        M_P.shrink_to_fit();

        if (verbose) cout << "... [done]\n  > Sorting out triples in OSP order" << flush;
        // Sorts the triples in OSP order
        sort(D.begin(), D.end(), [](const spo_triple& a,
                                    const spo_triple& b) { return std::tie(std::get<2>(a), std::get<0>(a), std::get<1>(a))
                                                                  < std::tie(std::get<2>(b), std::get<0>(b), std::get<1>(b));});
        if (verbose) cout << "... [done]" << endl;

        //Building BWT_P

        {
            vector<uint64_t> new_C_P;
            if (verbose) cout << "  > Building C_P";
            uint64_t cur_pos = 1;
            new_C_P.push_back(0);  // Dummy value
            new_C_P.push_back(cur_pos);
            for (uint64_t c = 2; c <= alphabet_SO; c++) {
                cur_pos += M_O[c-1];
                new_C_P.push_back(cur_pos);
            }
            new_C_P.push_back(n+1);
            new_C_P.shrink_to_fit();
            M_O.clear();
            if (verbose) cout << "... [done]" << endl;
            if (verbose) cout << "  > Building bwtp" << flush;
            int_vector<> new_P(n+1);
            new_P[0] = 0;
            for (i=1; i<=n; i++)
                new_P[i] = std::get<1>(D[i-1]);
            util::bit_compress(new_P);

            L_P = bwt(new_P, new_C_P);
        }

        if (verbose) cout << "... [done]\n  > Stable sorting out triples in POS order" << flush;
        stable_sort(D.begin(), D.end(), [](const spo_triple& a,
                                           const spo_triple& b) {return std::get<1>(a) < std::get<1>(b);});
        if (verbose) cout << "... [done]" << endl;

        //Building BWT_S
        {
            vector<uint64_t> new_C_S;
            if (verbose) cout << "  > Building C_S";
            uint64_t cur_pos = 1;
            new_C_S.push_back(0);  // Dummy value
            new_C_S.push_back(cur_pos);
            for (uint64_t c = 2; c <= max_P; c++) {
                cur_pos += M_P[c-1];
                new_C_S.push_back(cur_pos);
            }
            new_C_S.push_back(n+1);
            new_C_S.shrink_to_fit();
            M_P.clear();
            if (verbose) cout << "... [done]" << endl;
            if (verbose) cout << "  > Building bwts" << flush;
            int_vector<> new_S(n+1);
            new_S[0] = 0;
            for (i=1; i<=n; i++)
                new_S[i] = std::get<0>(D[i-1]);
            util::bit_compress(new_S);

            L_S = bwt_nose(new_S, new_C_S);
            if (verbose) cout << "... [done]" << endl;
        }


        if (verbose) cout << "-- Index constructed successfully" << endl;
    };

    // Size of the index in bytes
    uint64_t size() {
        //cout << "L_O: " << (float)L_O.size()*8/nTriples << endl;
        //cout << "L_S: " << (float)L_S.size()/nTriples << " bytes per Triple" << endl;
        //cout << "L_P: " << (float)L_P.size()/nTriples << " bytes per triple" << endl;

        //cout << "L_S.size() = " << L_S.size() << " bytes" << endl;
        //cout << "L_P.size() = " << L_P.size() << " bytes" << endl;
        //cout << "nTriples = " << nTriples << endl;
        return L_S.size() + L_P.size();
    }

    uint64_t n_triples() {
        return nTriples;
    }

    uint64_t n_labels() {
        return max_P;
    }

    void save(string filename) {
        L_S.save(filename + ".bwts");
        L_P.save(filename + ".bwtp");

        std::ofstream ofs(filename + ".nTriples");
        ofs << nTriples << endl;
        ofs << real_max_P << endl;
        ofs << max_S << endl;
        ofs << max_P << endl;
        ofs << max_O << endl;
    };

    void load(string filename) {
        //cout << "Loading L_S" << endl; fflush(stdout);
        L_S.load(filename + ".bwts");
        //cout << "Loading L_P" << endl; fflush(stdout);
        L_P.load(filename + ".bwtp");
        //cout << "Loading done" << endl; fflush(stdout);
        std::ifstream ifs(filename + ".nTriples");
        ifs >> nTriples;
        ifs >> real_max_P;
        ifs >> max_S;
        ifs >> max_P;
        ifs >> max_O;
    };

    uint64_t pred_selectivity(uint64_t pred_id) {
        return L_S.get_C(pred_id + 1) - L_S.get_C(pred_id);
    };


    inline uint64_t pred_reverse(uint64_t pred_id) const{
        return (pred_id > real_max_P) ? pred_id - real_max_P : pred_id + real_max_P;
    }



private:

    inline interval_state_type& last_element(std::stack<interval_state_type> &stack){
        return stack.top();
    }


    inline interval_state_type first_element(std::stack<interval_state_type> &stack){
        return stack.top();
    }


    inline interval_state_type& last_element(std::queue<interval_state_type> &queue){
        return queue.back();
    }

    inline interval_state_type first_element(std::queue<interval_state_type> &queue){
        return queue.front();
    }




    uint64_t next_step_const_to_var(RpqAutomata &A, std::vector<word_t> &B_array,
                             word_t current_D, uint level, bwt_interval &I_p,
                             Container &ist_container){

        uint64_t out_degree = 0; //number of nodes in the product graph pointed out by the current node
        //PART1: Finding predicates from the object whose range in L_p is I_p
        std::vector<std::pair<uint64_t, std::pair<uint64_t, uint64_t>>> pred_vec;
        L_P.all_active_p_values_in_range_test<word_t>(I_p.left(), I_p.right(), B_array,
                                                      current_D, pred_vec);

        std::pair<uint64_t, uint64_t> interval;
        uint64_t c;
        word_t new_D;
        //PART2: For each predicate, the values in L_S are obtained by using a backward step
        for (uint64_t i = 0; i < pred_vec.size(); i++) {
            interval = L_P.backward_step_test(I_p.left(), I_p.right(), pred_vec[i].first,
                                              pred_vec[i].second.first,
                                              pred_vec[i].second.second);
            c = L_S.get_C(pred_vec[i].first);
            std::vector<uint64_t> subj_vec;
            subj_vec = L_S.all_values_in_range(c + interval.first, c + interval.second);
            new_D = (word_t) A.next(current_D, pred_vec[i].first, BWD);

            //PART3: Map the range of each subject to the range of objects
            for (const auto &s : subj_vec) {
                const auto lb = L_P.get_C(s);
                const auto rb = L_P.get_C(s + 1) - 1;
                ist_container.push(interval_state_type{bwt_interval(lb, rb),new_D, level+1,
                    static_cast<uint32_t>(s), static_cast<uint32_t>(pred_vec[i].first)});
                ++out_degree;
            }
        }
        return out_degree;

    }

    //aqui é onde teño que desgranar os estados
    uint64_t next_step_const_to_var_v2(RpqAutomata &A, std::vector<word_t> &B_array,
                             word_t current_D, uint level, bwt_interval &I_p,
                             Container &ist_container){

        uint64_t out_degree = 0; //number of nodes in the product graph pointed out by the current node
        //PART1: Finding predicates from the object whose range in L_p is I_p
        std::vector<std::pair<uint64_t, std::pair<uint64_t, uint64_t>>> pred_vec;
        L_P.all_active_p_values_in_range_test<word_t>(I_p.left(), I_p.right(), B_array,
                                                      current_D, pred_vec);

        std::pair<uint64_t, uint64_t> interval;
        uint64_t c;
        word_t new_D;
        //PART2: For each predicate, the values in L_S are obtained by using a backward step
        for (uint64_t i = 0; i < pred_vec.size(); i++) {
            interval = L_P.backward_step_test(I_p.left(), I_p.right(), pred_vec[i].first,
                                              pred_vec[i].second.first,
                                              pred_vec[i].second.second);
            c = L_S.get_C(pred_vec[i].first);
            std::vector<uint64_t> subj_vec;
            subj_vec = L_S.all_values_in_range(c + interval.first, c + interval.second);
            new_D = (word_t) A.next(current_D, pred_vec[i].first, BWD);

            auto aux = new_D;
            std::vector<word_t> nfa_states;
            while (aux) {
                auto q_id = sdsl::bits::lo(new_D);
                word_t mask = (0x1 << q_id);
                nfa_states.push_back(q_id);
                aux = aux & ~mask;
            }

            //PART3: Map the range of each subject to the range of objects
            for (const auto &s : subj_vec) {
                const auto lb = L_P.get_C(s);
                const auto rb = L_P.get_C(s + 1) - 1;
                for (auto ns : nfa_states) {
                    ist_container.push(interval_state_type{bwt_interval(lb, rb), ns, level+1,
                    static_cast<uint32_t>(s), static_cast<uint32_t>(pred_vec[i].first)});
                    ++out_degree;
                }

            }
        }
        return out_degree;

    }



    void push_merge_interval(Container& ist_container, uint32_t node, uint32_t label, word_t D, uint level){

        const auto lb = L_P.get_C(node);
        const auto rb = L_P.get_C(node + 1) - 1;

        if(ist_container.empty()){
            ist_container.push(interval_state_type{bwt_interval(lb, rb),D, level, node, label});
            return;
        }
        //The previous interval is contiguous to element's interval and
        //both have equal NFA state
        auto& last = last_element(ist_container);
        if(last.interval.right()+1 == lb && last.current_D == D){
            last.interval.set_right(rb);
        }else{
            ist_container.push(interval_state_type{bwt_interval(lb, rb),D, level});
        }
    }


    uint64_t encode(uint32_t id, word_t state) {
        return ((uint64_t) id << (sizeof(word_t)*8)) | (state & ((0x1 << (sizeof(word_t)*8)) - 1));
    }

    std::pair<uint32_t, word_t> decode(uint64_t id_state) {
        std::pair<uint32_t, word_t> res;
        res.first = (uint32_t) (id_state >> (sizeof(word_t)*8));
        res.second = (word_t) (id_state & ((0x1 << (sizeof(word_t)*8)) - 1));
        return res;
    }

    uint check_visited_node(uint64_t id_state, std::unordered_map<uint64_t, info_type> &map_id) {
        auto it = map_id.find(id_state);
        if(it == map_id.end()) {
            return 0;  //not visited
        }
        return 1 + (it->second.node_pmr > 0); //1 => visited but not in the PMR; 2 => visited and in the PMR
    }

    void add_visited_node(uint64_t id_state, std::unordered_map<uint64_t, info_type> &map_id) {
        info_type info{0, 0};
        map_id.insert({id_state, info});
    }

    uint64_t add_PMR_node(uint64_t id_state, std::unordered_map<uint64_t, info_type> &map_id,
                      std::vector<id_state_degree_type> &states,
                      std::vector<std::vector<edge_type>> &adj_lists) {
        auto it = map_id.find(id_state);
        adj_lists.emplace_back();
        it->second.node_pmr = adj_lists.size();
        id_state_degree_type isd;
        isd.id_state = id_state;
        isd.out_degree = it->second.out_degree;
        states.emplace_back(isd);
        return it->second.node_pmr;
    }

    void set_degree_node(uint64_t id_state, uint64_t out_degree, std::unordered_map<uint64_t, info_type> &map_id) {
        auto it = map_id.find(id_state);
        it->second.out_degree = out_degree;
    }


    void add_adj_list(uint64_t src, uint64_t tgt, id_state_label_type isl,
                          std::vector<std::vector<edge_type>> &adj_lists) {
        adj_lists[src-1].emplace_back(edge_type{tgt-1, isl.label});
    }

    bool traverse_node(RpqAutomata &A,
                             word_t D, uint level, uint32_t s, uint32_t p,
                             std::unordered_map<uint64_t, info_type> &map_id,
                             std::vector<id_state_label_type> &path,
                             uint64_t &start_path,
                             std::vector<id_state_degree_type> &states,
                             std::vector<std::vector<edge_type>> &adj_lists) {
        auto id_state = encode(s, D);
        auto vs = check_visited_node(id_state, map_id);
        if(!vs) { //not visited node
            add_visited_node(id_state, map_id);
            path[level] = id_state_label_type{id_state, p};
            if (A.atFinal(D, BWD)) {
                //building path in PMR

                uint64_t tgt, src;
                if(start_path > 0) {
                    src =  map_id[path[start_path-1].id_state].node_pmr;
                }else {
                    src = add_PMR_node(path[start_path].id_state, map_id, states, adj_lists);
                    ++start_path;
                }
                for(uint64_t pi = start_path; pi <= level; ++pi) {
                    tgt = add_PMR_node(path[pi].id_state, map_id, states, adj_lists);
                    add_adj_list(src, tgt, path[pi], adj_lists);
                    src = tgt;
                }
                start_path = level+1;
            }
            return true;
        }
        if (vs == 2) { //visited node and in PMR
            //building path in PMR
            uint64_t src = map_id[path[start_path-1].id_state].node_pmr; //prev materialized node
            uint64_t tgt;
            for(uint64_t pi = start_path; pi < level; ++pi) {
                tgt = add_PMR_node(path[pi].id_state, map_id, states, adj_lists);
                add_adj_list(src, tgt, path[pi], adj_lists);
                src = tgt;
            }
            tgt = map_id[id_state].node_pmr;
            add_adj_list(src, tgt, id_state_label_type{id_state, p}, adj_lists);
            start_path = level+1;
        } //Otherwise: visited node but not in PMR => No solution is reacheable [nothing to do]*/
        return false;
    }

    bool traverse_node_v2(RpqAutomata &A,
                             word_t D, uint level, uint32_t s, uint32_t p,
                             std::unordered_map<uint64_t, info_type> &map_id,
                             std::vector<id_state_label_type> &path,
                             uint64_t &start_path,
                             std::vector<id_state_degree_type> &states,
                             std::vector<std::vector<edge_type>> &adj_lists) {
        auto aux = D;
        //TODO: penso que en D solo deberia haber un bit activo

        auto id_state = encode(s, D);
        auto vs = check_visited_node(id_state, map_id);
        if(!vs) { //not visited node
            add_visited_node(id_state, map_id);
            path[level] = id_state_label_type{id_state, p};
            if (A.atFinal(D, BWD)) {
                //building path in PMR

                uint64_t tgt, src;
                if(start_path > 0) {
                    src =  map_id[path[start_path-1].id_state].node_pmr;
                }else {
                    src = add_PMR_node(path[start_path].id_state, map_id, states, adj_lists);
                    ++start_path;
                }
                for(uint64_t pi = start_path; pi <= level; ++pi) {
                    tgt = add_PMR_node(path[pi].id_state, map_id, states, adj_lists);
                    add_adj_list(src, tgt, path[pi], adj_lists);
                    src = tgt;
                }
                start_path = level+1;
            }
            return true;
        }
        if (vs == 2) { //visited node and in PMR
            //building path in PMR
            uint64_t src = map_id[path[start_path-1].id_state].node_pmr; //prev materialized node
            uint64_t tgt;
            for(uint64_t pi = start_path; pi < level; ++pi) {
                tgt = add_PMR_node(path[pi].id_state, map_id, states, adj_lists);
                add_adj_list(src, tgt, path[pi], adj_lists);
                src = tgt;
            }
            tgt = map_id[id_state].node_pmr;
            add_adj_list(src, tgt, id_state_label_type{id_state, p}, adj_lists);
            start_path = level+1;
        } //Otherwise: visited node but not in PMR => No solution is reacheable [nothing to do]*/
        return false;
    }


    bool path_const_s_to_var_o(RpqAutomata &A,
                               std::vector<word_t> &B_array,
                               uint32_t initial_object,
                               std::vector<std::vector<edge_type>> &adj_lists,
                               std::vector<id_state_degree_type> &states,
                               bool const_to_var,
                               high_resolution_clock::time_point start) {

        high_resolution_clock::time_point stop;
        double total_time = 0.0;
        duration<double> time_span;

        word_t current_D;  // palabra de maquina D, con los estados activos (ojo que word_t son 16 bits)
        //TODO: necesito bitmap inizializable a 0 para cada nodo por agora uso o map_id
        // tamaño automata = m
        // tamaño array<64> = (2^m+63) / 64
        //initializable_array<word_t> D_array(4 * (max_O + 1), 0);

        //TODO: container agora ten que conter intervalo + currentD (e o mesmo) necesitarei saber o object?
        Container ist_container; //contains intervals with NFA states
        std::unordered_map<uint64_t, info_type> map_id;
        current_D = (word_t) A.getFinalStates();
        ist_container.push(interval_state_type{bwt_interval(L_P.get_C(initial_object),
                                                            L_P.get_C(initial_object + 1) - 1), current_D, 0,
                                                                initial_object, 0});

        /*auto id_state = encode(initial_object, current_D);
        add_visited_node(id_state, map_id);
        if (A.atFinal(current_D, BWD)) {
            add_PMR_node(id_state, map_id, states, adj_lists);
        }*/
        std::vector<id_state_label_type> path(256);
        //path.emplace_back(id_state_label_type{id_state, 0});
        uint64_t start_path = 0;
        while (!ist_container.empty()) {
            auto ist_top = first_element(ist_container);
            ist_container.pop();
            if(ist_top.level+1 == path.size()) path.resize(2*path.size());
            if(ist_top.level < start_path) start_path = ist_top.level;
            if(traverse_node(A, ist_top.current_D, ist_top.level, ist_top.node, ist_top.label,
                map_id, path, start_path, states, adj_lists)) {
                auto out_degree = next_step_const_to_var(A, B_array,ist_top.current_D, ist_top.level, ist_top.interval, ist_container);
                set_degree_node(encode(ist_top.node, ist_top.current_D), out_degree, map_id);
            }

            stop = high_resolution_clock::now();
            time_span = duration_cast<microseconds>(stop - start);
            total_time = time_span.count();
            if (total_time > TIME_OUT) {
                //std::cout << "Time: " << total_time << std::endl;
                return true;
            }
        }
        return false;
    };

     bool path_const_s_to_var_o_v2(RpqAutomata &A,
                               std::vector<word_t> &B_array,
                               uint32_t initial_object,
                               std::vector<std::vector<edge_type>> &adj_lists,
                               std::vector<id_state_degree_type> &states,
                               bool const_to_var,
                               high_resolution_clock::time_point start) {

        high_resolution_clock::time_point stop;
        double total_time = 0.0;
        duration<double> time_span;

        word_t current_D;  // palabra de maquina D, con los estados activos (ojo que word_t son 16 bits)
        //TODO: necesito bitmap inizializable a 0 para cada nodo por agora uso o map_id
        // tamaño automata = m
        // tamaño array<64> = (2^m+63) / 64
        //initializable_array<word_t> D_array(4 * (max_O + 1), 0);

        //TODO: container agora ten que conter intervalo + currentD (e o mesmo) necesitarei saber o object?
        Container ist_container; //contains intervals with NFA states
        std::unordered_map<uint64_t, info_type> map_id;
        current_D = (word_t) A.getFinalStates();// solo hai un activo , asi que non hai problema
        ist_container.push(interval_state_type{bwt_interval(L_P.get_C(initial_object),
                                                            L_P.get_C(initial_object + 1) - 1), current_D, 0,
                                                                initial_object, 0});

        /*auto id_state = encode(initial_object, current_D);
        add_visited_node(id_state, map_id);
        if (A.atFinal(current_D, BWD)) {
            add_PMR_node(id_state, map_id, states, adj_lists);
        }*/
        std::vector<id_state_label_type> path(256);
        //path.emplace_back(id_state_label_type{id_state, 0});
        uint64_t start_path = 0;
        while (!ist_container.empty()) {
            auto ist_top = first_element(ist_container);
            ist_container.pop();
            if(ist_top.level+1 == path.size()) path.resize(2*path.size());
            if(ist_top.level < start_path) start_path = ist_top.level;
            if(traverse_node(A, ist_top.current_D, ist_top.level, ist_top.node, ist_top.label,
                map_id, path, start_path, states, adj_lists)) {
                auto out_degree = next_step_const_to_var_v2(A, B_array,ist_top.current_D, ist_top.level, ist_top.interval, ist_container);
                set_degree_node(encode(ist_top.node, ist_top.current_D), out_degree, map_id);
            }

            stop = high_resolution_clock::now();
            time_span = duration_cast<microseconds>(stop - start);
            total_time = time_span.count();
            if (total_time > TIME_OUT) {
                //std::cout << "Time: " << total_time << std::endl;
                return true;
            }
        }
        return false;
    };




public:


    std::pair<uint64_t, uint64_t> get_nodes_edges(std::vector<std::vector<edge_type>> &adj_lists) {
        uint64_t PMR_nodes = adj_lists.size();
        uint64_t PMR_edges = 0;
        for(const auto &al : adj_lists) {
            PMR_edges += al.size();
        }
        return {PMR_nodes, PMR_edges};
    }

    void print_PMR(std::vector<std::vector<edge_type>> &adj_lists,
                   std::vector<id_state_degree_type> &states) {

        for(auto i = 0; i < adj_lists.size(); ++i) {
            auto p = decode(states[i].id_state);
            std::cout << "Id: " << i << " node=" << p.first << " DFA-state=" << p.second << " out-degree=" << states[i].out_degree << std::endl;
            std::cout << "List: [ ";
            for(const auto &e : adj_lists[i]) {
                std::cout << "{" << e.tgt << ", " << e.label << "} ";
            }
            std::cout << "]" << std::endl;
            std::cout << std::endl;
        }
    }


   std::pair<uint64_t, uint64_t> compress_PMR(std::vector<std::vector<edge_type>> &adj_lists,
                      std::vector<id_state_degree_type> &states) {
        std::vector<uint32_t> tunnel;
        std::stack<uint32_t> stack_nodes;
        stack_nodes.emplace(0);
        uint32_t n;
        uint64_t nodes_edges_in_tunnels = 0, tunnels = 0;
        std::vector<bool> visited(adj_lists.size(), false);
        while(!stack_nodes.empty()) {
            n = stack_nodes.top();
            stack_nodes.pop();
            //check if we can add it to a tunnel
            if(states[n].out_degree <= 1) {
                tunnel.push_back(n);
            }
            if(states[n].out_degree == 0 || states[n].out_degree > 1){ //end of a tunnel
                if(tunnel.size() > 2) { //we can compress it
                    nodes_edges_in_tunnels += tunnel.size()-1;
                    ++tunnels;
                }
                tunnel.clear();
            }
            //visit
            visited[n] = true;
            for(const auto &m : adj_lists[n]) {
                if(!visited[m.tgt]) stack_nodes.emplace(m.tgt);
            }
        }
        return {nodes_edges_in_tunnels, tunnels};
    }

void rpq_path_const_s_to_var_o(const std::string &rpq,
                              unordered_map<std::string, uint64_t> &predicates_map,  // ToDo: esto debería ser una variable miembro de la clase
                              std::vector<word_t> &B_array,
                              uint64_t initial_object,
                              std::vector<std::vector<edge_type>> &adj_lists,
                              std::vector<id_state_degree_type> &states) {

        std::string query, str_aux;

        int64_t iii = rpq.size() - 1;
        query = parse_reverse(rpq, iii, predicates_map, real_max_P);

        RpqAutomata A(query, predicates_map);
        if(A.getNumberStates() >= 16) {
            std::cout << "Error: more than 16 NFA states." << std::endl;
            return;
        }

        std::unordered_map<uint64_t, uint64_t> m = A.getB();
        for (std::unordered_map<uint64_t, uint64_t>::iterator it = m.begin(); it != m.end(); it++) {
            L_P.mark<word_t>(it->first, B_array, (word_t) it->second);
        }

        high_resolution_clock::time_point start;
        double total_time = 0.0;
        duration<double> time_span;
        start = high_resolution_clock::now();

        path_const_s_to_var_o(A, B_array, initial_object,
            adj_lists, states, true, start);

        for (std::unordered_map<uint64_t, uint64_t>::iterator it = m.begin(); it != m.end(); it++) {
            L_P.unmark<word_t>(it->first, B_array);
        }
    };

    void rpq_path_var_s_to_const_o(const std::string &rpq,
                              unordered_map<std::string, uint64_t> &predicates_map,  // ToDo: esto debería ser una variable miembro de la clase
                              std::vector<word_t> &B_array,
                              uint64_t initial_object,
                              std::vector<std::vector<edge_type>> &adj_lists,
                              std::vector<id_state_degree_type> &states) {

        std::string query, str_aux;
        int64_t iii = 0;
        query = parse(rpq, iii, predicates_map, real_max_P);

        RpqAutomata A(query, predicates_map);
        if(A.getNumberStates() >= 16) {
            std::cout << "Error: more than 16 NFA states." << std::endl;
            return;
        }

        std::unordered_map<uint64_t, uint64_t> m = A.getB();
        for (std::unordered_map<uint64_t, uint64_t>::iterator it = m.begin(); it != m.end(); it++) {
            L_P.mark<word_t>(it->first, B_array, (word_t) it->second);
        }

        high_resolution_clock::time_point start;
        double total_time = 0.0;
        duration<double> time_span;
        start = high_resolution_clock::now();

        path_const_s_to_var_o(A, B_array, initial_object,
            adj_lists, states, false, start);

        for (std::unordered_map<uint64_t, uint64_t>::iterator it = m.begin(); it != m.end(); it++) {
            L_P.unmark<word_t>(it->first, B_array);
        }
    };

    void rpq_path_const_s_to_var_o_v2(const std::string &rpq,
                              unordered_map<std::string, uint64_t> &predicates_map,  // ToDo: esto debería ser una variable miembro de la clase
                              std::vector<word_t> &B_array,
                              uint64_t initial_object,
                              std::vector<std::vector<edge_type>> &adj_lists,
                              std::vector<id_state_degree_type> &states) {

        std::string query, str_aux;

        int64_t iii = rpq.size() - 1;
        query = parse_reverse(rpq, iii, predicates_map, real_max_P);

        RpqAutomata A(query, predicates_map);
        if(A.getNumberStates() >= 16) {
            std::cout << "Error: more than 16 NFA states." << std::endl;
            return;
        }

        std::unordered_map<uint64_t, uint64_t> m = A.getB();
        for (std::unordered_map<uint64_t, uint64_t>::iterator it = m.begin(); it != m.end(); it++) {
            L_P.mark<word_t>(it->first, B_array, (word_t) it->second);
        }

        high_resolution_clock::time_point start;
        double total_time = 0.0;
        duration<double> time_span;
        start = high_resolution_clock::now();

        path_const_s_to_var_o_v2(A, B_array, initial_object,
            adj_lists, states, true, start);

        for (std::unordered_map<uint64_t, uint64_t>::iterator it = m.begin(); it != m.end(); it++) {
            L_P.unmark<word_t>(it->first, B_array);
        }
    };

    void rpq_path_var_s_to_const_o_v2(const std::string &rpq,
                              unordered_map<std::string, uint64_t> &predicates_map,  // ToDo: esto debería ser una variable miembro de la clase
                              std::vector<word_t> &B_array,
                              uint64_t initial_object,
                              std::vector<std::vector<edge_type>> &adj_lists,
                              std::vector<id_state_degree_type> &states) {

        std::string query, str_aux;
        int64_t iii = 0;
        query = parse(rpq, iii, predicates_map, real_max_P);

        RpqAutomata A(query, predicates_map);
        if(A.getNumberStates() >= 16) {
            std::cout << "Error: more than 16 NFA states." << std::endl;
            return;
        }

        std::unordered_map<uint64_t, uint64_t> m = A.getB();
        for (std::unordered_map<uint64_t, uint64_t>::iterator it = m.begin(); it != m.end(); it++) {
            L_P.mark<word_t>(it->first, B_array, (word_t) it->second);
        }

        high_resolution_clock::time_point start;
        double total_time = 0.0;
        duration<double> time_span;
        start = high_resolution_clock::now();

        path_const_s_to_var_o_v2(A, B_array, initial_object,
            adj_lists, states, false, start);

        for (std::unordered_map<uint64_t, uint64_t>::iterator it = m.begin(); it != m.end(); it++) {
            L_P.unmark<word_t>(it->first, B_array);
        }
    };




};


typedef ring_rpq_paths<> ring_rpq_paths_dfs;

#endif
