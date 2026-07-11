#include <acb_dirichlet.h>

/*
 * Certified Route D height extension using Arb's Turing-method zero count.
 *
 * Published input (Platt--Trudgian):
 *   T0 = 3000175332800
 *   N(T0) = N0 = 12363153437138
 *   every zero through T0 is simple and on the critical line.
 *
 * New exact endpoint:
 *   T1 = T0 + 111/256 = 768044885196911/256.
 *
 * Arb's acb_dirichlet_zeta_nzeros counts all nontrivial zeta zeros with
 * 0 < Im(rho) <= T1, including multiplicity, by Turing's method.  The two
 * neighboring calls to acb_dirichlet_zeta_zero independently isolate the
 * first and second zeros after the published count.
 */

int main(void) {
    const slong count_prec = 192;
    const slong zero_prec = 256;
    fmpq_t endpoint;
    fmpz_t n1, n2, expected, counted;
    arb_t t1, count;
    acb_t z1, z2;
    int count_unique, count_correct, first_below, second_above, certified;

    fmpq_init(endpoint);
    fmpz_init(n1);
    fmpz_init(n2);
    fmpz_init(expected);
    fmpz_init(counted);
    arb_init(t1);
    arb_init(count);
    acb_init(z1);
    acb_init(z2);

    fmpq_set_si(endpoint, 768044885196911L, 256L);
    arb_set_fmpq(t1, endpoint, count_prec);

    fmpz_set_str(n1, "12363153437139", 10);
    fmpz_set_str(n2, "12363153437140", 10);
    fmpz_set_str(expected, "12363153437139", 10);

    acb_dirichlet_zeta_nzeros(count, t1, count_prec);
    acb_dirichlet_zeta_zero(z1, n1, zero_prec);
    acb_dirichlet_zeta_zero(z2, n2, zero_prec);

    count_unique = arb_get_unique_fmpz(counted, count);
    count_correct = count_unique && fmpz_equal(counted, expected);
    first_below = arb_lt(acb_imagref(z1), t1);
    second_above = arb_gt(acb_imagref(z2), t1);
    certified = count_correct && first_below && second_above;

    flint_printf("T1=");
    arb_printn(t1, 90, ARB_STR_MORE);
    flint_printf("\nN_T1=");
    arb_printn(count, 90, ARB_STR_MORE);
    flint_printf("\nzero_N0_plus_1=");
    acb_printn(z1, 100, ARB_STR_MORE);
    flint_printf("\nzero_N0_plus_2=");
    acb_printn(z2, 100, ARB_STR_MORE);
    flint_printf("\nN_T1_exactly_N0_plus_1=%s\n", count_correct ? "true" : "false");
    flint_printf("first_new_zero_below_T1=%s\n", first_below ? "true" : "false");
    flint_printf("second_new_zero_above_T1=%s\n", second_above ? "true" : "false");
    flint_printf("certificate_pass=%s\n", certified ? "true" : "false");

    acb_clear(z2);
    acb_clear(z1);
    arb_clear(count);
    arb_clear(t1);
    fmpz_clear(counted);
    fmpz_clear(expected);
    fmpz_clear(n2);
    fmpz_clear(n1);
    fmpq_clear(endpoint);
    flint_cleanup();
    return certified ? 0 : 1;
}
