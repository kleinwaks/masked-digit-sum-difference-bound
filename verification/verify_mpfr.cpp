#include <algorithm>
#include <cstddef>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

#include <mpfr.h>

namespace {
constexpr int B = 17032;
constexpr int Q = 2 * B + 1;
constexpr int GENS[] = {1518, 1524, 1587, 2024, 2032, 2116};
constexpr int EXPECTED_MASK_SIZE = 3121;
constexpr int EXPECTED_SUM_SIZE = 18730;
constexpr int EXPECTED_DIFF_SIZE = 32369;
constexpr int EXPECTED_DIFFERENCE_COVER = 13066;
constexpr int EXPECTED_CONDUCTOR = 28922;
constexpr int EXPECTED_C1 = 14351;
constexpr int CONDUCTOR_SEARCH_LIMIT = 40000;
constexpr const char* LAMBDA_DECIMAL =
    "0.000321149844434550835903084464712287774157626054669874186964";
constexpr const char* CERTIFIED_THETA = "1.19102809";
constexpr mpfr_prec_t PRECISION_BITS = 384;

struct Mpfr {
    mpfr_t v;
    Mpfr() { mpfr_init2(v, PRECISION_BITS); }
    ~Mpfr() { mpfr_clear(v); }
    Mpfr(const Mpfr&) = delete;
    Mpfr& operator=(const Mpfr&) = delete;
};

[[noreturn]] void fail(const std::string& message) {
    throw std::runtime_error(message);
}

void require(bool condition, const std::string& message) {
    if (!condition) fail(message);
}

void print_mpfr(const char* label, mpfr_srcptr x, int digits = 70) {
    std::cout << label;
    mpfr_out_str(stdout, 10, static_cast<std::size_t>(digits), x, MPFR_RNDN);
    std::cout << '\n';
}

std::vector<unsigned char> semigroup_members(int limit) {
    std::vector<unsigned char> reachable(static_cast<std::size_t>(limit + 1), 0);
    reachable[0] = 1;
    for (int n = 0; n <= limit; ++n) {
        if (!reachable[static_cast<std::size_t>(n)]) continue;
        for (int g : GENS) {
            if (n + g <= limit) reachable[static_cast<std::size_t>(n + g)] = 1;
        }
    }
    return reachable;
}

int conductor(const std::vector<unsigned char>& reachable) {
    constexpr int multiplicity = GENS[0];
    for (int n = 0; n + multiplicity <= static_cast<int>(reachable.size()); ++n) {
        bool all = true;
        for (int j = 0; j < multiplicity; ++j) {
            if (!reachable[static_cast<std::size_t>(n + j)]) {
                all = false;
                break;
            }
        }
        if (all) return n;
    }
    fail("reachability limit too small to determine conductor");
}

}  // namespace

int main() {
    try {
        const auto reachable = semigroup_members(CONDUCTOR_SEARCH_LIMIT);
        std::vector<int> mask;
        for (int n = 0; n <= B; ++n) {
            if (reachable[static_cast<std::size_t>(n)]) mask.push_back(n);
        }

        const int INF = std::numeric_limits<int>::max();
        std::vector<unsigned char> sum_present(static_cast<std::size_t>(2 * B + 1), 0);
        std::vector<int> diff_cost(static_cast<std::size_t>(2 * B + 1), INF);

        for (int a : mask) {
            for (int b : mask) {
                sum_present[static_cast<std::size_t>(a + b)] = 1;
                const int idx = a - b + B;
                diff_cost[static_cast<std::size_t>(idx)] =
                    std::min(diff_cost[static_cast<std::size_t>(idx)], a + b);
            }
        }

        const int sum_size = static_cast<int>(
            std::count(sum_present.begin(), sum_present.end(), static_cast<unsigned char>(1)));
        const int diff_size = static_cast<int>(std::count_if(
            diff_cost.begin(), diff_cost.end(), [INF](int x) { return x != INF; }));
        const int c1 = diff_cost[static_cast<std::size_t>(B + 1)];
        const int cond = conductor(reachable);
        int difference_cover = 0;
        while (difference_cover + 1 <= B &&
               diff_cost[static_cast<std::size_t>(B + difference_cover + 1)] != INF) {
            ++difference_cover;
        }

        require(static_cast<int>(mask.size()) == EXPECTED_MASK_SIZE, "wrong mask size");
        require(!mask.empty() && mask.front() == 0 && mask.back() == B,
                "wrong mask endpoints");
        require(sum_size == EXPECTED_SUM_SIZE, "wrong sum support size");
        require(diff_size == EXPECTED_DIFF_SIZE, "wrong difference support size");
        require(difference_cover == EXPECTED_DIFFERENCE_COVER,
                "wrong initial difference cover");
        require(c1 == EXPECTED_C1, "wrong kappa(1)");
        require(cond == EXPECTED_CONDUCTOR, "wrong conductor");

        std::cout << "Exact combinatorial reconstruction: PASS\n";
        std::cout << "B=" << B << " base=" << Q
                  << " |M|=" << mask.size()
                  << " |M+M|=" << sum_size
                  << " |M-M|=" << diff_size
                  << " cover=" << difference_cover
                  << " conductor=" << cond
                  << " kappa(1)=" << c1 << "\n";

        // lambda_lo <= the exact terminating decimal lambda <= lambda_hi.
        Mpfr lambda_lo, lambda_hi;
        require(mpfr_set_str(lambda_lo.v, LAMBDA_DECIMAL, 10, MPFR_RNDD) == 0,
                "failed to parse lower lambda endpoint");
        require(mpfr_set_str(lambda_hi.v, LAMBDA_DECIMAL, 10, MPFR_RNDU) == 0,
                "failed to parse upper lambda endpoint");

        // Lower bound P_-(exp(-lambda)); upper bound P_+(exp(-lambda)).
        Mpfr pminus_lo, pplus_hi, positive, exponent, term;
        mpfr_set_zero(pminus_lo.v, 0);
        mpfr_set_zero(pplus_hi.v, 0);

        for (int c : diff_cost) {
            if (c == INF) continue;
            mpfr_mul_ui(positive.v, lambda_hi.v, static_cast<unsigned long>(c), MPFR_RNDU);
            mpfr_neg(exponent.v, positive.v, MPFR_RNDN);
            mpfr_exp(term.v, exponent.v, MPFR_RNDD);
            mpfr_add(pminus_lo.v, pminus_lo.v, term.v, MPFR_RNDD);
        }

        for (int s = 0; s <= 2 * B; ++s) {
            if (!sum_present[static_cast<std::size_t>(s)]) continue;
            mpfr_mul_ui(positive.v, lambda_lo.v, static_cast<unsigned long>(s), MPFR_RNDD);
            mpfr_neg(exponent.v, positive.v, MPFR_RNDN);
            mpfr_exp(term.v, exponent.v, MPFR_RNDU);
            mpfr_add(pplus_hi.v, pplus_hi.v, term.v, MPFR_RNDU);
        }

        Mpfr log_pminus_lo, log_pplus_hi, f_lo, log_q_hi, ratio_lo, theta_lo;
        mpfr_log(log_pminus_lo.v, pminus_lo.v, MPFR_RNDD);
        mpfr_log(log_pplus_hi.v, pplus_hi.v, MPFR_RNDU);
        mpfr_sub(f_lo.v, log_pminus_lo.v, log_pplus_hi.v, MPFR_RNDD);
        require(mpfr_sgn(f_lo.v) > 0, "certified log-ratio is not positive");

        Mpfr q_mpfr;
        mpfr_set_ui(q_mpfr.v, static_cast<unsigned long>(Q), MPFR_RNDN);
        mpfr_log(log_q_hi.v, q_mpfr.v, MPFR_RNDU);
        mpfr_div(ratio_lo.v, f_lo.v, log_q_hi.v, MPFR_RNDD);
        mpfr_add_ui(theta_lo.v, ratio_lo.v, 1, MPFR_RNDD);

        Mpfr target_hi;
        require(mpfr_set_str(target_hi.v, CERTIFIED_THETA, 10, MPFR_RNDU) == 0,
                "failed to parse target theta");

        print_mpfr("Pminus lower  = ", pminus_lo.v);
        print_mpfr("Pplus upper   = ", pplus_hi.v);
        print_mpfr("F lower       = ", f_lo.v);
        print_mpfr("theta lower   = ", theta_lo.v);
        std::cout << "claimed conservative bound = " << CERTIFIED_THETA << '\n';

        require(mpfr_cmp(theta_lo.v, target_hi.v) > 0,
                "interval lower bound does not exceed claimed value");

        std::cout << "PASS: directed-rounding MPFR computation proves C_3a > "
                  << CERTIFIED_THETA << "\n";
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "FAIL: " << e.what() << '\n';
        return 1;
    }
}
