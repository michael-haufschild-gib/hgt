# Theory of Arithmetic Producers (TAP)

- **ID:** TAP
- **Stage:** 1-in-progress
- **Type:** programme (CONJECTURE → THEOREM (Lean) loop)
- **Source:** docs/reports/review-2011/obstacles-summary.md §2.9
- **Statement:** develop the theory of arithmetic producers: which comparisons of sizes exist over ℤ, what they cost, at which place, and which twins they separate; answer Q1–Q8, build T1–T5.

## Goal
README: formal/GaloisForLFunctions/ArithmeticProducerTheory/README.md. Lean folder
formal/GaloisForLFunctions/ArithmeticProducerTheory/, umbrella ArithmeticProducerTheory.lean.
Non-circularity: no producer may compute its price from ψ, M or the zeros.

## Gates
- [x] 0 → 1  in-progress: README draft, questions, tools, criteria fixed
- [ ] 1 → 2  every pillar with a paper proof
- [ ] 2 → 3  every pillar formalized, wired, checked

## Conjecture table
| # | Conjecture | Status | Lean |
|---|---|---|---|
| C1 | (Q1) A differential operator of finite order on R[X_σ] linear over ψ_a(R[X_σ]), a regular in R, is a multiplication; ∂_i is ψ_a-linear iff a = 0 in R | proved | `HasOrderLE.eq_mul_of_expand_linear`, `pderiv_expand_linear_iff`, `derivation_eq_zero_of_expand` |
| C1b | (Q1) D∘ψ_a = c·ψ_a∘D (a ≥ 2 regular) iff D = Σ r_i X_i∂_i with c r_i = a r_i; over a domain c = a | proved | `isCompatible_iff`, `IsCompatible.scalar_eq` |
| C2 | (Q1) The ψ-linear operators over ℤ: digit operators are ψ_{a^(k+1)}-linear over every ring, X_i∂_i = Σ a^k·digit_k + a^K·quot_K, digit_k = Hasse–Euler operator binom(X∂, p^k) in characteristic p (Lucas), of no finite order where a is regular | proved | `digitOp_expand_mul`, `euler_eq_sum_digitOp`, `quotOp_expand_mul`, `digitOp_eq_hasseEuler`, `hasOrderLE_hasseEuler`, `not_hasOrderLE_digitOp`, `diag_expand_linear_iff` |
| C1c | (Q1) Pointwise-local operators are the differential operators (infinite domain); local + ψ_a-linear ⇒ multiplication; the ψ_a-periodic diagonal operators cut out exactly the Frobenius fibre ideal (X_i^a − c_i^a), which is the fat point ((X_i − c_i)^p) in characteristic p | proved | `isLocal_iff_hasOrderLE`, `IsLocal.eq_mul_of_expand_linear`, `mem_fibreIdeal_iff`, `fibreIdeal_eq_span`, `fibreIdeal_eq_span_pow_of_charP` |
| C3 | (T5) one-sided transfer along a positive dilation kernel K f = Σ a_j f(λ_j x) with gain ρ(s) = Σ a_j λ_j^s: f ≤ g + Kf, g ≤ A x^s, ρ(s) < 1 ⇒ f ≤ A/(1−ρ(s)) x^s; constant exact; neutral exponents (ρ = 1) carry no transfer and are removed only by an o(·) a priori bound; barycentric stencils contract all of (0,1) | proved | `le_rpow_of_le_add_dilate`, `le_rpow_of_le_add_dilate_of_isLittleO`, `transfer_constant_attained`, `rpow_eq_sum_dilate_of_gain_eq_one`, `dilationGain_lt_one_of_barycentric`, `isBarycentric_two_scales` |
| C3b | (T5, criterion 4) prime instance: for a positive stencil with ρ(1) ≤ 1, ρ < 1 on (½,1), the one-sided spectrum (either sign) of the centred gap of θ(x) − x is exactly Θ; a priori input = PNT only; every Jensen gap of θ on a barycentric stencil is a one-sided meter | proved | `signed_theta_sub_le_of_primeErrorGap_le`, `zetaZeroAbscissa_le_of_signed_theta`, `primeErrorGap_upper_spectrum_iff`, `thetaJensenGap_upper_spectrum_iff` |
| C3c | (T2) archimedean component of the δ-structure: derivation x log x = generator of x ↦ x^a at a = 1, carry = entropy ∈ [0,(x+y)log 2]; finite carries (Kummer) ≤ archimedean carry; rigidity: completely additive L with carry of n·L(n) ≥ −K(m+n) is c·log; other weightings have carry unbounded both ways | proved | `hasDerivAt_powerCarry`, `log_choose_le_entropyCarry`, `entropyCarry_sub_log_le_log_choose` (two-sided balance, slack log(m+n+1)), `eq_mul_log_of_carry_ge`, `carry_bddBelow_iff`, `exists_carry_lt_and_gt`, `prime_dvd_add_pow_sub` |
| C4 | (Q4) Hasse–Weil for z^(n+1) = c·x(1−x)^a from the two pairings; purity at every embedding of the value ring | proved | `abs_card_puncturedKummerPoints_sub_le`, `norm_map_jacobiSum_sq`, `norm_jacobiSum_le_sqrt` |
| C5 | (criterion 1) calibration: Kummer Hasse–Weil (C4), Riemann–Roch with exact constants (C7), Chebyshev comparison with log slack (C3c) | proved in these forms; no abstract comparison theorem | see C4, C7, C3c |
| C6 | (T4, criterion 2) twin suite | hosted: SSIC `TheTwinTestSuite`; TAP adds the weight twin | `exists_carry_lt_and_gt` |
| C7 | (Q2) sections of degree ≤ d on the torus of k primes = lattice points of the simplex Σ α_i log p_i ≤ d; Riemann–Roch d^k ≤ k!·Π w_i·N(d) ≤ (d+Σw_i)^k; duality: interior points = N(d − Σ w_i) (canonical degree Σ log p_i); graph of ψ_a injective below d₁ < a·w_i; diagonal count product > sum once k!Πw(d₁+d₂+Σw)^k < (d₁d₂)^k | proved (finite torus); full square: count is marginal (⌊X⌋⌊Y⌋ ≤ ⌊XY⌋), kernel = collisions only | `card_simplexPoints_bounds`, `card_filter_pos_simplexPoints`, `graph_injOn`, `card_image_add_lt_card_product`, `mem_simplexPoints_log` |
| C8 | (Q3) which comparisons survive the product formula | partial | FE against second moment: `sq_eq_of_mul_eq_of_sum_sq_le`, `sum_norm_sq_jacobiSum`, `norm_jacobiSum_sq_of_meanValue` (zero slack over 𝔽_q; over ℤ the slack is the mean-value error) |

## Approach
Order: open items of README §10. Next: joint δ-structure (item 2), the second term on the full square (item 3), then item 1.

Hosted elsewhere, not to be rebuilt here: T3 cooperative reduction and pole plane (GCW), sublattice elimination (SAC), T4 twin suite (SSIC `TheTwinTestSuite`), priced stencils (ZCG `dilationSymbol_eq_zero_of_zeta_eq_zero`, RHTower `ChebyshevMajorant`, AOSP), diamagnetic inequalities (SSHA, SAEI), Selberg ledger (RAC), Beurling twins (RHTower).

Findings:
- Q1: Leibniz and ψ-linearity cannot coexist where the Frobenius degree is regular; ψ-linear operators over ℤ are the digit operators (nonlocal), Hasse derivatives mod p; they cut out the fibre, a distinct points, not a fat point. Infinitesimal replacement: d/ds, Frobenius scalar a.
- Chebyshev: comparison slack ≤ log(m+n+1); all loss is reading slack (alternating priced stencil → positive stencil).
- Bombieri count on k primes fires at degree of order Σ log p_i; on all primes it is marginal and kernels are collisions.
- C5 (abstract comparison) dropped: the abstract statement is empty; the content is the slack table of README §5.

## Log
- 2026-11-20 — card created; README first draft written.
