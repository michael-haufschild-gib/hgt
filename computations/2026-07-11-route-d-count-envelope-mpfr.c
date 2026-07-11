#include <stdio.h>
#include <mpfr.h>

/*
 * Rigorous directed-rounding certificate for the Route D endpoint test
 *
 *   F(T0) < N0 + 2,
 *
 * where
 *
 *   M(T) = T/(2*pi) * log(T/(2*pi*e)),
 *   E(T) = 0.10076*log(T) + 0.24460*log(log(T)) + 8.08292,
 *   F(T) = M(T) + E(T),
 *   T0 = 3000175332800,
 *   N0 = 12363153437138.
 *
 * Every lower endpoint is computed with MPFR_RNDD and every upper endpoint
 * with MPFR_RNDU.  The main term is evaluated as
 *
 *   T/(2*pi) * (log(T/(2*pi)) - 1)
 *
 * to avoid introducing a redundant exponential evaluation.
 */

int main(void) {
    const mpfr_prec_t prec = 256;
    mpfr_t T, threshold;
    mpfr_t pi_lo, pi_hi, den_lo, den_hi, a_lo, a_hi;
    mpfr_t loga_lo, loga_hi, b_lo, b_hi, M_lo, M_hi;
    mpfr_t logT_lo, logT_hi, loglogT_lo, loglogT_hi;
    mpfr_t c1_lo, c1_hi, c2_lo, c2_hi, c3_lo, c3_hi;
    mpfr_t t1_lo, t1_hi, t2_lo, t2_hi, E_lo, E_hi;
    mpfr_t F_lo, F_hi, slack_lo, slack_hi, headroom_lo, headroom_hi;

    mpfr_inits2(prec, T, threshold, pi_lo, pi_hi, den_lo, den_hi,
        a_lo, a_hi, loga_lo, loga_hi, b_lo, b_hi, M_lo, M_hi,
        logT_lo, logT_hi, loglogT_lo, loglogT_hi,
        c1_lo, c1_hi, c2_lo, c2_hi, c3_lo, c3_hi,
        t1_lo, t1_hi, t2_lo, t2_hi, E_lo, E_hi,
        F_lo, F_hi, slack_lo, slack_hi, headroom_lo, headroom_hi, (mpfr_ptr) 0);

    mpfr_set_str(T, "3000175332800", 10, MPFR_RNDN);
    mpfr_set_str(threshold, "12363153437140", 10, MPFR_RNDN);

    mpfr_const_pi(pi_lo, MPFR_RNDD);
    mpfr_const_pi(pi_hi, MPFR_RNDU);
    mpfr_mul_ui(den_lo, pi_lo, 2, MPFR_RNDD);
    mpfr_mul_ui(den_hi, pi_hi, 2, MPFR_RNDU);
    mpfr_div(a_lo, T, den_hi, MPFR_RNDD);
    mpfr_div(a_hi, T, den_lo, MPFR_RNDU);
    mpfr_log(loga_lo, a_lo, MPFR_RNDD);
    mpfr_log(loga_hi, a_hi, MPFR_RNDU);
    mpfr_sub_ui(b_lo, loga_lo, 1, MPFR_RNDD);
    mpfr_sub_ui(b_hi, loga_hi, 1, MPFR_RNDU);
    mpfr_mul(M_lo, a_lo, b_lo, MPFR_RNDD);
    mpfr_mul(M_hi, a_hi, b_hi, MPFR_RNDU);

    mpfr_log(logT_lo, T, MPFR_RNDD);
    mpfr_log(logT_hi, T, MPFR_RNDU);
    mpfr_log(loglogT_lo, logT_lo, MPFR_RNDD);
    mpfr_log(loglogT_hi, logT_hi, MPFR_RNDU);

    mpfr_set_ui(c1_lo, 2519, MPFR_RNDN);
    mpfr_div_ui(c1_lo, c1_lo, 25000, MPFR_RNDD);
    mpfr_set_ui(c1_hi, 2519, MPFR_RNDN);
    mpfr_div_ui(c1_hi, c1_hi, 25000, MPFR_RNDU);
    mpfr_set_ui(c2_lo, 1223, MPFR_RNDN);
    mpfr_div_ui(c2_lo, c2_lo, 5000, MPFR_RNDD);
    mpfr_set_ui(c2_hi, 1223, MPFR_RNDN);
    mpfr_div_ui(c2_hi, c2_hi, 5000, MPFR_RNDU);
    mpfr_set_ui(c3_lo, 202073, MPFR_RNDN);
    mpfr_div_ui(c3_lo, c3_lo, 25000, MPFR_RNDD);
    mpfr_set_ui(c3_hi, 202073, MPFR_RNDN);
    mpfr_div_ui(c3_hi, c3_hi, 25000, MPFR_RNDU);

    mpfr_mul(t1_lo, c1_lo, logT_lo, MPFR_RNDD);
    mpfr_mul(t1_hi, c1_hi, logT_hi, MPFR_RNDU);
    mpfr_mul(t2_lo, c2_lo, loglogT_lo, MPFR_RNDD);
    mpfr_mul(t2_hi, c2_hi, loglogT_hi, MPFR_RNDU);
    mpfr_add(E_lo, t1_lo, t2_lo, MPFR_RNDD);
    mpfr_add(E_lo, E_lo, c3_lo, MPFR_RNDD);
    mpfr_add(E_hi, t1_hi, t2_hi, MPFR_RNDU);
    mpfr_add(E_hi, E_hi, c3_hi, MPFR_RNDU);

    mpfr_add(F_lo, M_lo, E_lo, MPFR_RNDD);
    mpfr_add(F_hi, M_hi, E_hi, MPFR_RNDU);
    mpfr_sub(slack_lo, threshold, F_hi, MPFR_RNDD);
    mpfr_sub(slack_hi, threshold, F_lo, MPFR_RNDU);
    mpfr_sub(headroom_lo, threshold, M_hi, MPFR_RNDD);
    mpfr_sub(headroom_hi, threshold, M_lo, MPFR_RNDU);

    mpfr_printf("M_interval=[%.60RDf, %.60RUf]\n", M_lo, M_hi);
    mpfr_printf("E_interval=[%.60RDf, %.60RUf]\n", E_lo, E_hi);
    mpfr_printf("F_interval=[%.60RDf, %.60RUf]\n", F_lo, F_hi);
    mpfr_printf("slack_N0plus2_minus_F=[%.60RDf, %.60RUf]\n", slack_lo, slack_hi);
    mpfr_printf("maximum_admissible_E=[%.60RDf, %.60RUf]\n", headroom_lo, headroom_hi);
    printf("A0_certified_false=%s\n", mpfr_sgn(slack_hi) < 0 ? "true" : "false");

    mpfr_clears(T, threshold, pi_lo, pi_hi, den_lo, den_hi,
        a_lo, a_hi, loga_lo, loga_hi, b_lo, b_hi, M_lo, M_hi,
        logT_lo, logT_hi, loglogT_lo, loglogT_hi,
        c1_lo, c1_hi, c2_lo, c2_hi, c3_lo, c3_hi,
        t1_lo, t1_hi, t2_lo, t2_hi, E_lo, E_hi,
        F_lo, F_hi, slack_lo, slack_hi, headroom_lo, headroom_hi, (mpfr_ptr) 0);
    return 0;
}
