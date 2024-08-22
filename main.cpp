#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <fstream>
#include <chrono>
#include <utility>


using namespace __gnu_pbds;
using    namespace std;

#define FAST ios::sync_with_stdio(0), cin.tie(0), cout.tie(0);
#define ordered_set tree<int, null_type,less<>, rb_tree_tag,tree_order_statistics_node_update>
#define ordered_multiset tree<int, null_type,less_equal<>, rb_tree_tag,tree_order_statistics_node_update>

vector<string> data = {"chordal", "eulerian", "highlyirregular12", "perfect", "planar", "selfcomp", "simgraph", "strongregular"};
vector<string> data_st = {"strongregular_4", "strongregular_10", "strongregular_15", "strongregular_28", "strongregular_41", "strongregular_227", "strongregular_180", "strongregular_3854"};
vector<string> data_CFI = {"CFI_data", "cfi-rigid-r2", "cfi-rigid-t2", "cfi-rigid-d3", "cfi-rigid-z2", "cfi-rigid-z3", "cfi-rigid-s2", "sat_cfi_dim"}, data_stgr;
vector<string> DAT = data_CFI;
int ind = 0;
string prefix, fold = "CFI/";
string directory = prefix + "graph/" + fold + DAT[ind], output_directory = prefix + "graph_output/" + fold + DAT[ind] + " test_output.txt", Folder = DAT[ind];
ofstream fp(output_directory);

vector<vector<long long>> same;

template <typename T>
void makeCombiUtil(vector<vector<T> >& ans, vector<T>& tmp, int n, int left, int k){
    if (k == 0) {
        ans.emplace_back(tmp);
        return;
    }
    for (int i = left; i <= n; ++i){
        tmp.emplace_back(i);
        makeCombiUtil(ans, tmp, n, i + 1, k - 1);
        tmp.pop_back();
    }
}

vector<vector<int> > makeCombi(int n, int k){
    vector<vector<int> > ans;
    vector<int> tmp;
    makeCombiUtil(ans, tmp, n, 1, k);
    return ans;
}

void recursive_fill(vector<vector<long long>>& arr, vector<long long>& tmp, int k){
    if (k == (int)same.size()){
        arr.emplace_back(tmp);
        return;
    }
    for(auto it:same[k]){
        tmp.emplace_back(it);
        recursive_fill(arr, tmp, k + 1);
        tmp.pop_back();
    }
}
void fill(vector<vector<long long>>& arr){
    vector<long long> tmp;
    recursive_fill(arr, tmp, 0);
}

template <typename T>
T random(T md){
    auto now = std::chrono::high_resolution_clock::now();
    auto seed = now.time_since_epoch().count();
    srand(seed);
    T b = (T)(rand() % (md));
    return b;
}

template <typename T>
class Sgraph{
public:
    struct edge {
        long long from;
        long long to;
        T cost;
    };

    vector<edge> edges{};
    vector<vector<long long>> g;
    long long n{};
    long long m{};

    // weights:
    vector<long long> node_weight;

    // rank and position of node nodes based on their weights:
    vector<long long> rank;
    vector<long long> pos;

    // stores the beginning and the end of each same rank:
    vector<pair<long long, long long>> tmp1;
    vector<pair<long long, long long>> tmp2;

    // values needed to determine the bound of the code:
    long long nb_ranks{};
    long long distinct_ranks{};
    vector<long long> automorph_rank;

//////////////////////  function   //////////////////////

// Constructors:
    Sgraph() = default;
    ~Sgraph() = default;

    explicit Sgraph(long long _n): n(_n), nb_ranks(1ll), distinct_ranks(_n), m(0ll){
        node_weight.resize(_n, 0ll);
        rank.resize(_n, 1ll);
        automorph_rank.resize(_n + 1, 0ll);
        pos.resize(_n);
        g.resize(_n);
        edges.clear();
        tmp1.clear();
        tmp2.clear();
        tmp1.emplace_back(0, _n - 1ll);
        for(long long i = 0; i < _n; i++) pos[i] = i;
    }

    void init(long long a){
        n = a;
        m = 0ll;
        automorph_rank.resize(a + 1, 0ll);
        g.resize(a);
        node_weight.resize(a, 0);
        edges.clear();
        rank.resize(a, 1);
        pos.resize(a);
        tmp1.emplace_back(0, n - 1);
        nb_ranks = 1ll;
        distinct_ranks = a;
        for(long long i = 0; i < a; i++) pos[i] = i;
    }

    void clear(){
        automorph_rank.clear();
        edges.clear();
        g.clear();
        node_weight.clear();
        rank.clear();
        pos.clear();
        tmp1.clear();
        tmp2.clear();
    }
    Sgraph& operator=(const Sgraph& other) = default;


    long long add(long long from, long long to, T cost = 1){
        assert(0 <= from && from < n && 0 <= to && to < n);
        auto id = (long long) edges.size();
        m++;
        g[from].emplace_back(id);
        g[to].emplace_back(id);
        edges.push_back({from, to, cost});
        return id;
    }



// ShortestPath variants:
    vector<long long> shortestPath(long long src, long long id){
        queue<long long> elem;
        elem.emplace(src);
        long long target, lvl = 0;
        vector<long long> check(m, 0ll), node_lvl(n, -1ll);
        if (id >= 0ll) check[id] = 1;
        else{
            node_lvl[-1ll - id] = -2ll;
            for(auto itx:g[-1ll - id]) check[itx] = 1ll;
        }
        node_lvl[src] = 0ll;
        while (!elem.empty()) {
            target = elem.front();
            elem.pop();
            for (auto it: g[target]) {
                long long v = edges[it].to ^ edges[it].from ^ target;
                if (check[it]) continue;
                check[it] = 1ll;
                if (node_lvl[v] == -1ll) {
                    elem.emplace(v);
                    node_lvl[v] = node_lvl[target] + 1ll;
                    lvl = node_lvl[v];
                }
            }
        }
        node_lvl[src] = lvl;
        return node_lvl;
    }

    vector<long long> shortestPath(long long src){
        queue<long long> elem;
        elem.emplace(src);
        long long target, lvl;
        vector<long long> check(m, 0ll), node_lvl(n, -1ll);
        node_lvl[src] = 0ll;
        while (!elem.empty()) {
            target = elem.front();
            elem.pop();
            for (auto it: g[target]) {
                long long v = edges[it].to ^ edges[it].from ^ target;
                if (check[it]) continue;
                check[it] = 1ll;
                if (node_lvl[v] == -1ll) {
                    elem.emplace(v);
                    node_lvl[v] = node_lvl[target] + 1ll;
                    lvl = node_lvl[v];
                }
            }
        }
        node_lvl[src] = lvl;
        return node_lvl;
    }


    bool automorphism_test(const vector<long long>& arr){
        vector<long long> node(n, 0ll);
        auto ref = (long long)g[arr[0]].size();
        for(auto it:g[arr[0]]) node[edges[it].to ^ arr[0]^ edges[it].from] = 1ll;
        for(auto it:arr) {
            long long test = 0;
            for (auto itx: g[it]) {
                long long v = edges[itx].to ^ it ^ edges[itx].from;
                if (node[v]) test++;
            }
            if (test != ref) return false;
        }
        return true;
    }


// Metric:
    long long metric(const vector<vector<long long>>& layer){
        long long tot = 0ll, ref, lvl = (long long)layer.size();
        for (long long j = 0; j <= lvl; j++) {
            ref = 0ll;
            for (long long i = 0; i < (long long) layer[j].size(); i++) ref += (layer[j][i] * (i + 1ll));
            tot += (ref * (j + 1ll));
        }
        return tot;
    }

// Algo:
    vector<long long> advanced_node_weight_PT(long long limit, int dim){
        vector<long long> ans, dist_rank, count_rank(n + 1, 0ll);
        long long rk = 0ll, count = 0ll;
        for(auto it:pos){
            if (rank[it] != rk){
                if (!automorph_rank[rank[it]]) dist_rank.emplace_back(it);
                rk = rank[it];
            }
            count_rank[rank[it]]++;
        }
        int N = (int)dist_rank.size(), indicator = 0;
        vector<vector<int>> combination;
        for(int j = min(dim, N); j <= N; j++){
            combination = makeCombi(N, j);
            for(const auto& sample_combination:combination){
                Sgraph<long long> copy(*this);
                for(auto it:sample_combination){
                    long long candidate = dist_rank[it - 1], rank_candidate;
                    rank_candidate = rank[candidate];
                    copy.rank[candidate] += count_rank[rank_candidate] - 1ll;
                    copy.automorph_rank[rank[candidate]] = 1;
                    for(int i = 0; i < n; i++){
                        if (copy.pos[i] == candidate){
                            swap(copy.pos[i], copy.pos[copy.rank[candidate] - 1ll]);
                            break;
                        }
                    }
                    for(auto& couple:copy.tmp1){
                        if (couple.second == copy.rank[candidate] - 1ll){
                            couple.second--;
                            break;
                        }
                    }
                    copy.nb_ranks++;
                }
                long long counter = 0ll, old = 1ll;
                while(old != copy.nb_ranks && copy.nb_ranks != copy.distinct_ranks){
                    old = copy.nb_ranks;
                    counter++;
                    copy.node_weight_PT(1ll);
                    if (counter > limit) break;
                }
                if (copy.nb_ranks == copy.distinct_ranks || indicator + 1 == (int)combination.size()){
                    fp << "Ideal ranks size : " << sample_combination.size() << "// ";
                    for(auto it:sample_combination) fp << rank[dist_rank[it - 1]] << ' ';
                    fp << endl;
                    same.clear();
                    same.resize(sample_combination.size());
                    vector<pair<int, int>> target_ranks(n + 1, {0, -1});
                    int a = 0;
                    for(int i : sample_combination){
                        target_ranks[rank[dist_rank[i - 1]]] = {1, a};
                        a++;
                    }
                    for(auto it:pos){
                        if (target_ranks[rank[it]].first) same[target_ranks[rank[it]].second].emplace_back(it);
                    }
                    vector<vector<long long>> Same;

                    fill(Same);
                    vector<long long> nd_weight[Same.size()];
                    vector<pair<long long, int>> score;
                    int index = 0;
                    for(const auto& it:Same){
                        Sgraph<long long> cop(*this);
                        int iw = 0;
                        for(auto candidate:it) {
                            cop.rank[candidate] += (long long) same[iw].size() - 1ll;
                            for (int i = 0; i < n; i++) {
                                if (cop.pos[i] == candidate) {
                                    swap(cop.pos[i], cop.pos[cop.rank[candidate] - 1ll]);
                                    break;
                                }
                            }

                            for (auto &couple: cop.tmp1) {
                                if (couple.second == cop.rank[candidate] - 1ll) {
                                    couple.second--;
                                    break;
                                }
                            }
                            cop.nb_ranks++;
                            iw++;
                        }
                        counter = 0ll, old = 1ll;
                        while(old != cop.nb_ranks && cop.nb_ranks != cop.distinct_ranks){
                            old = cop.nb_ranks;
                            counter++;
                            ans = cop.node_weight_PT(1ll);
                            if (counter > limit) break;
                        }

                        nd_weight[index] = ans;
                        if (ans.empty()) nd_weight[index] = cop.node_weight_PT(1ll);
                        long long tot = 0ll;
                        for(long long i = 0; i < n; i++) tot += (nd_weight[index][i] * (i + 1ll));
                        score.emplace_back(tot, index);
                        index++;

                    }
                    ans.clear();
                    sort(score.begin(), score.end());
                    for(auto itw:score){
                        for(auto itww:nd_weight[itw.second]) ans.emplace_back(itww);
                    }
                    return ans;
                }
                indicator++;
            }
            break;
        }
        return ans;
    }


    vector<pair<long long, long long>> PT(const vector<long long>& src){
        vector<pair<long long, long long>> weights;
        vector<long long> check_node(n, 0ll);
        for(auto it:src){
            weights.emplace_back(0ll, it), check_node[it] = 1ll;
        }
        for(long long ver = 0ll; ver < src.size(); ver++) {
            long long tot_weight = 0ll;
            for(long long nd = 0ll; nd <= g[src[ver]].size(); nd++) {
                long long lvl = 0ll, target, ix = 0;
                vector<long long> check(m, 0ll), val = rank, same_lvl(n, 0ll), node_lvl, node(n, 0ll);
                if (nd < g[src[ver]].size()) {
                    if (!check[g[src[ver]][nd]] && check_node[edges[g[src[ver]][nd]].to ^ edges[g[src[ver]][nd]].from ^ src[ver]])
                        check[g[src[ver]][nd]] = 1ll, node_lvl = shortestPath(src[ver], g[src[ver]][nd]);
                    else continue;
                }
                else node_lvl = shortestPath(src[ver]);
                queue<long long> elem;
                lvl = node_lvl[src[ver]];
                node_lvl[src[ver]] = 0ll;
                vector<vector<long long>> EOT(lvl + 1);
                elem.emplace(src[ver]);
                node[src[ver]] = 1ll;
                while (!elem.empty()) {
                    target = elem.front();
                    elem.pop();
                    EOT[node_lvl[target]].emplace_back(target);
                    if (node_lvl[target] != ix) {
                        for (auto it: EOT[ix]) {
                            val[it] += same_lvl[it];
                            for (auto itx: g[it]) {
                                long long v = edges[itx].to ^ edges[itx].from ^ it;
                                if (node_lvl[it] < node_lvl[v]) val[v] += same_lvl[it];
                            }
                        }
                        ix++;
                    }
                    for (auto it: g[target]) {
                        if (check[it]) continue;
                        long long v = edges[it].to ^ edges[it].from ^ target;
                        check[it] = 1ll;
                        if (node_lvl[target] == node_lvl[v]) {
                            same_lvl[target] += val[v];
                            same_lvl[v] += val[target];
                        } else {
                            val[v] += val[target];
                            if (!node[v]) {
                                elem.emplace(v);
                                node[v] = 1ll;
                            }
                        }
                    }
                }

                for (auto it: EOT[ix]) {
                    val[it] += same_lvl[it];
                    for (auto itx: g[it]) {
                        long long v = edges[itx].to ^ edges[itx].from ^ it;
                        if (node_lvl[it] < node_lvl[v]) val[v] += same_lvl[it];
                    }
                }

                for (long long j = lvl - 1; j >= 0l; j--) {
                    for (auto &it: EOT[j]){
                        for(auto xx:g[it]){
                            long long c = edges[xx].to ^ edges[xx].from ^ it;
                            if (node_lvl[c] > node_lvl[it]) val[it] += val[c];
                        }
                    }
                }

                for (long long j = 0; j <= lvl; j++) {
                    for (auto &it: EOT[j]) it = val[it] * (same_lvl[it] + 1ll);
                    sort(EOT[j].begin(), EOT[j].end());
                }
                tot_weight += metric(EOT);
            }
            node_weight[src[ver]] += tot_weight;
            weights[ver].first = node_weight[src[ver]];
        }
        sort(weights.begin(), weights.end());
        return weights;
    }

    vector<long long> node_weight_PT(long long t){
        vector<pair<long long, long long>> weights;
        vector<long long> ans, same_rank;
        long long current_rank, lvl, old, no_change, tot;
        while(t){
            tot = (long long) tmp1.size();
            no_change = 0ll;
            if (!tot) break;
            for(auto it:tmp1){
                if (it.first == it.second){
                    automorph_rank[rank[pos[it.first]]] = 1;
                    continue;
                }
                same_rank.clear();
                lvl = it.first + 1;
                current_rank = lvl;
                for(long long i = it.first; i <= it.second; i++) same_rank.emplace_back(pos[i]);
                weights = PT(same_rank);
                for(long long i = it.first; i <= it.second; i++) pos[i] = weights[i - it.first].second;
                old = it.first;
                rank[pos[old]] = lvl;
                node_weight[pos[it.first]] += weights[0].first;
                for(long long i = it.first + 1; i <= it.second; i++){
                    if (weights[i - it.first].first != weights[i - 1 - it.first].first){
                        if (i - old != 1) tmp2.emplace_back(old, i - 1);
                        nb_ranks++;
                        lvl += (i - old);
                        old = i;
                    }
                    node_weight[pos[i]] += weights[i - it.first].first;
                    rank[pos[i]] = lvl;
                }
                if (it.second != old){
                    if (it.first == old) {
                        if (automorphism_test(same_rank)) {
                            automorph_rank[rank[pos[old]]] = 1;
                            distinct_ranks -= ((long long) same_rank.size() - 1ll);
                            continue;
                        }
                        no_change++;
                    }
                    tmp2.emplace_back(old, it.second);
                }

            }
            if (no_change == tot){
                cout << "busted !:! " << nb_ranks << ' ' << n << ' ' << distinct_ranks << "/" << m << endl;
                tmp2.clear();
                break;
            }
            cout << t << ' ' << nb_ranks << ' ' << n << ' ' << distinct_ranks << " " << m << endl;
            tmp1 = tmp2;
            tmp2.clear();
            t--;
        }
        vector<long long> stock[n];
        for(long long i = 0; i < n; i++){
            stock[rank[i] - 1].emplace_back(node_weight[i]);
        }
        for(auto& it:stock){
            sort(it.begin(), it.end());
            for(auto itx:it) ans.emplace_back(itx);
        }
        return ans;
    }

};

template<typename T>
class PTNN{
public:
    map<string, vector<string>> store;
    vector<long long> no;
    vector<long long> yes;
    vector<long long> tot;
    string directory;
    long long N{};

/////////////////  Function  ////////////////////

    PTNN() = default;
    ~PTNN() = default;

    explicit PTNN(string dir): directory(std::move(dir)){
        string f, x;
        for (const auto &entry: filesystem::directory_iterator(directory)) {
            if (entry.is_regular_file()) {
                f = entry.path().filename().string();
                x = f;
                auto it = x.end();
                it--;
                while(*it != '-' && *it != '_'){
                    x.erase(it);
                    it = x.end();
                    it--;
                }
                x.erase(it);
                store[x].emplace_back(f);
            }
        }
        N = (long long)store.size();
        no.resize(N, 0);
        yes.resize(N, 0);
        tot.resize(N, 0);
    }

    bool preprocess(const Sgraph<long long>& g1, const Sgraph<long long>& g2){
        long long nb = g1.n;
        if (nb != g2.n || g1.edges.size() != g2.edges.size()) return false;
        long long G1[nb], G2[nb];
        for(long long i = 0; i < nb; i++){
            G1[i] = (long long)g1.g[i].size();
            G2[i] = (long long)g2.g[i].size();
        }
        sort(G1, G1 + nb);
        sort(G2, G2 + nb);
        for(long long i = 0; i < nb; i++){
            if (G1[i] != G2[i]) return false;
        }
        return true;
    }

    Sgraph<long long> read(const std::string &file) {
        std::ifstream f;
        try {
            f.open(file);
            if (!f.is_open()) {
                throw std::runtime_error("Failed to open file");
            }

            long long nb, m, x, y;
            if (!(f >> nb >> m)) {
                throw std::runtime_error("Failed to read the number of vertices and edges");
            }
            Sgraph<long long> g(nb);

            for (long long i = 0; i < m; i++) {
                if (!(f >> x >> y)) {
                    throw std::runtime_error("Failed to read edge");
                }
                if (x < 0 || x >= nb || y < 0 || y >= nb) {
                    throw std::runtime_error("Invalid vertex index");
                }
                g.add(x, y);
            }
            f.close();
            return g;
        } catch (const std::exception& e) {
            std::cerr << "Exception: " << e.what() << std::endl;
            Sgraph<long long> g1(0);
            return g1;
        }
    }

    void iso_test(const string& folder){
        map<long long, long long> limits;
        long long o = -1, YES = 0, NO = 0, TOT = 0;;
        auto starts = std::chrono::high_resolution_clock::now();
        for(const auto& itx:store){
            o++;
            //if (o != 16) continue;
            vector<string> files = itx.second;
            auto start = std::chrono::high_resolution_clock::now();
            long long n = (long long)files.size(), total = (n * (n - 1)) / 2, ref = 0;
            vector<long long> G[n], advanced_G[n];
            vector<long long> rank[n], done(n, 0);
            vector<Sgraph<long long>> g(n), copy(n), copi(n);

            for(long long i = 0; i < n; i++){
                g[i] = read(directory + "/" +  files[i]);
                G[i] = g[i].node_weight_PT(1);
            }
            for (long long i = 0; i < n; i++) {
                for (long long j = i + 1; j < n; j++) {
                    tot[o]++;
                    ref = 0;
                    if (G[i].size() != G[j].size()) ref = 1;
                    else{
                        for(long long w = 0; w < G[i].size(); w++){
                            if (G[i][w] != G[j][w]){
                                ref = 1;
                                break;
                            }
                        }
                    }
                    if (!ref){

                        if (!done[i]){
                            advanced_G[i] = g[i].advanced_node_weight_PT((long long)log2(g[i].n), 1);
                            done[i] = 1;
                        }
                        if (!done[j]){
                            advanced_G[j] = g[j].advanced_node_weight_PT((long long)log2(g[j].n), 1);
                            done[j] = 1;
                        }
                        if (advanced_G[i].size() != advanced_G[j].size()) ref = 1;
                        else{
                            for(long long w = 0; w < advanced_G[i].size(); w++){
                                if (advanced_G[i][w] != advanced_G[j][w]){
                                    ref = 1;
                                    break;
                                }
                            }
                        }
                    }
                    if (ref) no[o]++;
                    else yes[o]++;
                }
            }
            YES += yes[o], NO += no[o], TOT += tot[o];
            fp << o + 1 << " / " << store.size() << '\n';
            auto end = std::chrono::high_resolution_clock::now();
            auto duration = (std::chrono::duration_cast<std::chrono::seconds>(end - start)).count();
            auto durationss = (std::chrono::duration_cast<std::chrono::seconds>(end - starts)).count();
            fp << "Total time         : " << (durationss / 3600) << " : " << ((durationss % 3600) / 60) << " : " << ((durationss % 3600) % 60) << '\n';
            fp << "Total non isomorph : " << setprecision(10) << 100.0 * ((float)NO / (float)TOT) << "%" << '\n';
            fp << "Total isomorph     : " << setprecision(10) << 100.0 * ((float)YES / (float)TOT) << "%" << '\n';
            fp << endl;

        }
        fp << folder << " : " << setprecision(10) << 100.0 << "%" << endl;
        auto ends = std::chrono::high_resolution_clock::now();
        auto durations = (std::chrono::duration_cast<std::chrono::seconds>(ends - starts)).count();
        fp << "time         : " << (durations / 3600) << " : " << ((durations % 3600) / 60) << " : " << ((durations % 3600) % 60) << endl;
        fp << "non isomorph : " << setprecision(10) << 100.0 * ((float)NO / (float)TOT) << "%" << endl;
        fp << "isomorph     : " << setprecision(10) << 100.0 * ((float)YES / (float)TOT) << "%" << endl;
        fp << endl;
    }

};




void solve() {

    // Define directories
    PTNN<long long> gnn(directory);
    gnn.iso_test(Folder);

}
int main(){
    FAST;
    solve();
}