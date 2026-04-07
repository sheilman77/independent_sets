#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using std::binary_search;
using std::cerr;
using std::cout;
using std::move;
using std::size_t;
using std::string;
using std::uint32_t;
using std::uint64_t;
using std::unordered_map;
using std::vector;

namespace {

void sort_unique_shrink(vector<uint32_t>& v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    v.shrink_to_fit();
}

class TreeIndependentSetVerifier {
public:
    TreeIndependentSetVerifier(uint32_t exact_limit, uint32_t final_limit)
        : exact_limit_(exact_limit),
          final_limit_(final_limit),
          spf_(final_limit + 1),
          rooted_by_total_(exact_limit + 1),
          forest_by_product_(exact_limit + 1) {}

    vector<uint32_t> run(bool verbose = true) {
        build_spf();
        build_exact_tables(verbose);

        vector<char> achievable(final_limit_ + 1, 0);

        // Exact values up to exact_limit_.
        for (uint32_t a = 1; a <= exact_limit_ && a <= final_limit_; ++a) {
            if (!rooted_by_total_[a].empty()) {
                achievable[a] = 1;
            }
        }

        // Coverage step: if (A,B) is an exact rooted state then
        // (2^k A + B, 2^k A) is also a rooted state for every k >= 0.
        for (uint32_t A = 1; A <= exact_limit_; ++A) {
            if (rooted_by_total_[A].empty()) {
                continue;
            }
            for (uint32_t B : rooted_by_total_[A]) {
                uint64_t mul = 1;
                while (true) {
                    const uint64_t n = mul * static_cast<uint64_t>(A) + B;
                    if (n > final_limit_) {
                        break;
                    }
                    achievable[static_cast<uint32_t>(n)] = 1;
                    mul <<= 1;
                }
            }
        }

        vector<uint32_t> residual;
        for (uint32_t n = 1; n <= final_limit_; ++n) {
            if (!achievable[n]) {
                residual.push_back(n);
            }
        }

        size_t residual_above_exact = 0;
        for (uint32_t n : residual) {
            if (n > exact_limit_) {
                ++residual_above_exact;
            }
        }

        if (verbose) {
            cerr << "after coverage: " << residual.size() << " uncovered values\n";
            cerr << "after coverage: " << residual_above_exact
                 << " uncovered values above the exact bound\n";
        }

        // Exact recursive check on the remaining residual values above exact_limit_.
        size_t recovered = 0;
        for (uint32_t n : residual) {
            if (n <= exact_limit_) {
                continue;
            }
            if (tree_constructible(n)) {
                achievable[n] = 1;
                ++recovered;
            }
        }

        if (verbose) {
            cerr << "recursive exact check recovered " << recovered
                 << " of those residual values\n";
        }

        vector<uint32_t> missing;
        for (uint32_t n = 1; n <= final_limit_; ++n) {
            if (!achievable[n]) {
                missing.push_back(n);
            }
        }
        return missing;
    }

private:
    uint32_t exact_limit_;
    uint32_t final_limit_;

    // Smallest-prime-factor sieve, built up to final_limit_.
    vector<uint32_t> spf_;

    // Exact tables up to exact_limit_.
    // rooted_by_total_[A] = sorted list of B such that (A,B) is a rooted state.
    // forest_by_product_[p] = sorted list of y such that y is a forest-product
    //                        partner for p, i.e. there is a forest of rooted trees
    //                        with product A-values p and product B-values y.
    vector<vector<uint32_t>> rooted_by_total_;
    vector<vector<uint32_t>> forest_by_product_;

    // On-demand divisor cache for the recursive checker.
    unordered_map<uint32_t, vector<uint32_t>> divisors_cache_;

    // Memoization for the recursive exact checker above exact_limit_.
    unordered_map<uint64_t, uint8_t> rooted_memo_;
    unordered_map<uint64_t, uint8_t> forest_memo_;

    static uint64_t pack(uint32_t a, uint32_t b) {
        return (static_cast<uint64_t>(a) << 32) | b;
    }

    void build_spf() {
        spf_[1] = 1;
        for (uint32_t i = 2; i <= final_limit_; ++i) {
            if (spf_[i] != 0) {
                continue;
            }
            spf_[i] = i;
            if (static_cast<uint64_t>(i) * i > final_limit_) {
                continue;
            }
            for (uint64_t j = static_cast<uint64_t>(i) * i; j <= final_limit_; j += i) {
                if (spf_[j] == 0) {
                    spf_[j] = i;
                }
            }
        }
    }

    const vector<uint32_t>& divisors(uint32_t n) {
        auto it = divisors_cache_.find(n);
        if (it != divisors_cache_.end()) {
            return it->second;
        }

        vector<std::pair<uint32_t, int>> factorization;
        uint32_t x = n;
        while (x > 1) {
            const uint32_t p = spf_[x];
            int e = 0;
            while (x % p == 0) {
                x /= p;
                ++e;
            }
            factorization.push_back({p, e});
        }

        vector<uint32_t> divs{1};
        for (const auto& [p, e] : factorization) {
            const size_t current = divs.size();
            uint32_t pe = 1;
            for (int i = 1; i <= e; ++i) {
                pe *= p;
                for (size_t j = 0; j < current; ++j) {
                    divs.push_back(divs[j] * pe);
                }
            }
        }
        std::sort(divs.begin(), divs.end());
        auto [inserted, _] = divisors_cache_.emplace(n, move(divs));
        return inserted->second;
    }

    void build_exact_tables(bool verbose) {
        forest_by_product_[1].push_back(1);  // empty forest
        forest_by_product_[1].shrink_to_fit();

        const auto t0 = std::chrono::steady_clock::now();
        size_t num_rooted_states = 0;

        for (uint32_t p = 1; p <= exact_limit_; ++p) {
            if (p > 1) {
                if (!rooted_by_total_[p].empty()) {
                    sort_unique_shrink(rooted_by_total_[p]);
                }

                const uint32_t limit_for_y = exact_limit_ - p;
                vector<uint32_t> candidates;

                const auto& divs = divisors(p);
                size_t guess = 0;
                for (uint32_t d : divs) {
                    if (d > 1) {
                        guess += std::min<size_t>(rooted_by_total_[d].size(), 8);
                    }
                }
                candidates.reserve(guess);

                for (uint32_t d : divs) {
                    if (d == 1) {
                        continue;
                    }
                    const uint32_t q = p / d;
                    const auto& rooted_options = rooted_by_total_[d];
                    const auto& forest_options = forest_by_product_[q];
                    if (rooted_options.empty() || forest_options.empty()) {
                        continue;
                    }
                    for (uint32_t v : rooted_options) {
                        const uint32_t max_w = limit_for_y / v;
                        for (uint32_t w : forest_options) {
                            if (w > max_w) {
                                break;
                            }
                            candidates.push_back(v * w);
                        }
                    }
                }

                sort_unique_shrink(candidates);
                forest_by_product_[p] = move(candidates);
            }

            num_rooted_states += forest_by_product_[p].size();
            for (uint32_t y : forest_by_product_[p]) {
                const uint32_t a = p + y;
                if (a <= exact_limit_) {
                    rooted_by_total_[a].push_back(p);
                }
            }

            if (verbose && (p % 10000 == 0 || p == exact_limit_)) {
                const auto t1 = std::chrono::steady_clock::now();
                const double sec = std::chrono::duration<double>(t1 - t0).count();
                cerr << "exact DP: p=" << p << ", rooted states=" << num_rooted_states
                     << ", elapsed=" << sec << " s\n";
            }
        }

        for (uint32_t a = 1; a <= exact_limit_; ++a) {
            if (!rooted_by_total_[a].empty()) {
                sort_unique_shrink(rooted_by_total_[a]);
            }
        }
    }

    bool exact_rooted_state(uint32_t A, uint32_t B) const {
        if (A > exact_limit_) {
            return false;
        }
        const auto& v = rooted_by_total_[A];
        return binary_search(v.begin(), v.end(), B);
    }

    bool exact_forest(uint32_t p, uint32_t y) const {
        if (p > exact_limit_) {
            return false;
        }
        const auto& v = forest_by_product_[p];
        return binary_search(v.begin(), v.end(), y);
    }

    bool rooted_state(uint32_t A, uint32_t B) {
        if (A <= exact_limit_) {
            return exact_rooted_state(A, B);
        }
        if (B == 0 || B >= A) {
            return false;
        }
        // For nontrivial rooted states one always has A - B <= B, except for (2,1),
        // which is already covered by the exact table.
        if (A > 2 && B < (A + 1) / 2) {
            return false;
        }

        const uint64_t key = pack(A, B);
        auto it = rooted_memo_.find(key);
        if (it != rooted_memo_.end()) {
            return it->second != 0;
        }

        const bool ans = forest(B, A - B);
        rooted_memo_.emplace(key, static_cast<uint8_t>(ans));
        return ans;
    }

    bool forest(uint32_t p, uint32_t y) {
        if (p <= exact_limit_) {
            return exact_forest(p, y);
        }
        if (p == 1 && y == 1) {
            return true;
        }
        if (y == 0 || y >= p) {
            return false;
        }

        const uint64_t key = pack(p, y);
        auto it = forest_memo_.find(key);
        if (it != forest_memo_.end()) {
            return it->second != 0;
        }

        const auto& p_divs = divisors(p);
        const auto& y_divs = divisors(y);

        bool ans = false;
        for (uint32_t d : p_divs) {
            if (d == 1) {
                continue;
            }
            // Any rooted child state (d,v) must satisfy v >= ceil(d/2), so if d > 2y
            // there cannot be a divisor v of y with v < d and v >= ceil(d/2).
            if (d > 2ULL * y) {
                break;
            }

            const uint32_t q = p / d;
            const uint32_t min_v = (d + 1) / 2;
            for (uint32_t v : y_divs) {
                if (v < min_v) {
                    continue;
                }
                if (v >= d) {
                    break;
                }
                if (!rooted_state(d, v)) {
                    continue;
                }
                if (forest(q, y / v)) {
                    ans = true;
                    break;
                }
            }
            if (ans) {
                break;
            }
        }

        forest_memo_.emplace(key, static_cast<uint8_t>(ans));
        return ans;
    }

    bool tree_constructible(uint32_t n) {
        if (n <= exact_limit_) {
            return !rooted_by_total_[n].empty();
        }
        for (uint32_t B = (n + 1) / 2; B < n; ++B) {
            if (rooted_state(n, B)) {
                return true;
            }
        }
        return false;
    }
};

}  // namespace

int main(int argc, char** argv) {
    uint32_t exact_limit = 100000;
    uint32_t final_limit = 1500000;
    string output_path;

    if (argc >= 2) {
        exact_limit = static_cast<uint32_t>(std::stoul(argv[1]));
    }
    if (argc >= 3) {
        final_limit = static_cast<uint32_t>(std::stoul(argv[2]));
    }
    if (argc >= 4) {
        output_path = argv[3];
    }

    TreeIndependentSetVerifier verifier(exact_limit, final_limit);
    const vector<uint32_t> missing = verifier.run(true);

    cout << "missing_count=" << missing.size() << '\n';
    cout << "largest_missing=" << (missing.empty() ? 0 : missing.back()) << '\n';

    if (!missing.empty()) {
        cout << "first20=";
        for (size_t i = 0; i < std::min<size_t>(20, missing.size()); ++i) {
            if (i != 0) {
                cout << ',';
            }
            cout << missing[i];
        }
        cout << '\n';

        cout << "last20=";
        const size_t start = missing.size() > 20 ? missing.size() - 20 : 0;
        for (size_t i = start; i < missing.size(); ++i) {
            if (i != start) {
                cout << ',';
            }
            cout << missing[i];
        }
        cout << '\n';
    }

    if (!output_path.empty()) {
        std::ofstream out(output_path);
        for (uint32_t n : missing) {
            out << n << '\n';
        }
    }

    return 0;
}
