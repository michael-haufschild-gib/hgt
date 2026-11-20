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
| C4 | (Q4) Hasse–Weil for z^(n+1) = c·x(1−x)^a from the two pairings; purity at every embedding of the value ring | proved | `abs_card_puncturedKummerPoints_sub_le`, `norm_map_jacobiSum_sq`, `norm_jacobiSum_le_sqrt` |
| C5 | (criterion 1) abstract comparison (zeros ≤ poles for a size) with Stepanov and Chebyshev as instances | open | — |
| C6 | (T4, criterion 2) twin suite: one interface, axiom ladder (integer norms / integer count / FE / coefficients) | open | — |
| C7 | (Q2) Riemann–Roch count with Γ constants | open | — |
| C8 | (Q3) which comparisons survive the product formula | partial | FE against second moment: `sq_eq_of_mul_eq_of_sum_sq_le`, `sum_norm_sq_jacobiSum`, `norm_jacobiSum_sq_of_meanValue` (zero slack over 𝔽_q; over ℤ the slack is the mean-value error) |

## Approach
Order: C7 (Riemann–Roch count with Γ, sections with heights), C5 (comparison + instances), C6 (twin suite), rest of C8, then T2, T3.

Findings so far (Q1): Leibniz and ψ-linearity cannot coexist where the Frobenius degree is regular; ψ-linear operators exist over ℤ (digit operators, nonlocal) and reduce to Hasse derivatives mod p. Stepanov over 𝔽_q uses ψ_q(f) = f^q twice: for ψ-linear multiplicity, and for values at fixed points (h(x)^N); only the first has a lift.

## Log
- 2026-11-20 — card created; README first draft written.
