# Li's criterion: finite range, density and syndetic structure of failures

- **ID:** LI-SIGN-STRUCT-20261010
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Opus RH loop rows 727, 763, 777, 778 (`1-in-progress/rh-goal-loop-opus-2026-09-29.md`); STATUS MUST-901, MUST-904, MUST-905
- **Statement:** (i) `Re 2λ_n ≥ 0` for every `n ≤ 68`, unconditionally. (ii) If RH fails, both signs of `Re 2λ_n` occur on `≥ cN − K` of the `n < N` and in every window `[a, a+L)` with `a ≥ N₁`. (iii) RH ⟺ the negative indices have lower density zero ⟺ for every `L` there are arbitrarily late runs of `L` nonnegative coefficients.

## Goal
Determine what a failure of Li's criterion must look like. (i) partially discharges the criterion from the verified band `γ² ≥ 431/2` alone. (ii) and (iii) show that the failure set cannot be sparse.

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven (paper in the loop rows)
- [x] 2 → 3 formalized: `RHTower.re_xiLiPaired_nonneg_of_le_68` (`LiFirstCoefficientsNonneg`), `RHTower.exists_density_re_xiLiPaired_neg_and_pos_of_not_riemannHypothesis`, `RHTower.exists_window_re_xiLiPaired_neg_and_pos_of_not_riemannHypothesis`, `RHTower.riemannHypothesis_iff_liminf_density_re_xiLiPaired_neg_zero`, `RHTower.riemannHypothesis_iff_arbitrarily_late_nonneg_runs` (`LiSignDensity`). Built with `lake build`, standard axioms only, wired into `GaloisForLFunctions.RHTower`.
- [ ] 3 → 4 not intended (user directive: no stage 4)

## Approach
- (i) Termwise. With `w = e^{x+iθ}`, `Re(2 − wⁿ − w⁻ⁿ) = 2 − 2cosh(nx)cos(nθ)`. Off the line, `|x| ≤ |θ| ≤ |γ|/(γ² − ¼)`. Combined with `cos y·cosh y ≤ 1` on `[0, π/2]`, every term is nonnegative while `n|θ| ≤ 3π/2`.
- (ii) Dominant part `Re 2λ_n = −Rⁿ Σ_{ρ∈D} m_ρRe(u_ρⁿ) + o(Rⁿ)`, with `D` the Cayley roots of maximal modulus `R > 1` and `u_ρ` non-real and unimodular. The shifted first and second moments of finite cosine sums (`exists_card_filter_gt_and_lt_shift`) have constants independent of the window start.

## No-go closure
- **Exact killing mechanism (for producers):** these are receiver-structure theorems. `L`, `N₁`, `c`, `K` depend on the unknown top off-line configuration, so no finite computation certifies RH.
- **Strongest positive survivor:** the syndetic/density structure above, in Lean. Recurrence along squares or shifted primes (Bohr sets meet every set of Bohr recurrence) remains [P]: Mathlib has no Weyl equidistribution.
- **New insight:** Li is an identity-recurrence receiver. It detects every finite off-line configuration without independence hypotheses (loop row 773), unlike the phase-targeted CCM parity receiver (CANNOT-502).

## Log
- 2026-10-10: rows 727, 777, 778 formalized; card created in 3-formalized.

## Squares (2026-10-10, MUST-908)

`RHTower/LiSignAlongSquares` (465 lines, standard axioms, wired into `RHTower.lean`):
- `exists_density_re_xiLiPaired_sq_neg_of_not_riemannHypothesis`: off the critical line, `Re 2λ_{(Tk)²} < 0` for at least `cN` of the `k < N`.
- `riemannHypothesis_iff_eventually_re_xiLiPaired_sq_nonneg`: RH ⟺ eventual nonnegativity along the squares.

Reusable pieces:
- `eventually_norm_sum_pow_sq_le`: quadratic Weyl sums are `o(N)` off the roots of unity.
- `exists_pow_eq_one_or_not_root`: a common period of a finite family's roots of unity.
- `exists_card_filter_gt_of_mean_sq`: positive density from `o(N)` first and second moments.
- `exists_card_filter_pow_sq_gt`: cosine sums along `T²k²`.

This closes the squares item of the earlier [P] list. Primes remain [P].

## Polynomials and the obstruction (2026-10-10, MUST-909)

`RHTower/LiSignAlongPolynomials` (579 lines, standard axioms, wired):
- `riemannHypothesis_iff_eventually_re_xiLiPaired_poly_nonneg`: for `P ∈ ℕ[X]` of degree `≥ 1` with no constant term, RH ⟺ eventual nonnegativity of `λ_{P(m)}`.
- `re_sum_liTerm_rootFamily_pos`: the Ramanujan-sum countermodel for sequences that avoid `0 mod b`.

Reusable pieces:
- `eventually_norm_sum_zpow_le`: polynomial Weyl sums.
- `exists_card_filter_seq_gt`: density along any divisible index family.

Primes remain [P].

## Conjugate second moment: progressions up to modulus 45 (MUST-923, 2026-10-11)

Module `formal/GaloisForLFunctions/RHTower/LiSignConjugateMoment.lean` (550 lines, standard axioms, wired into `RHTower`).

- `exists_card_filter_seq_gt_conj`: positive density for a conjugation-closed unit family with `Re u_i^e > 0`. No conditions on the products `u_iu_j`, `u_iū_j`.
- `sum_mul_resonantRe_conj_ge`: the conjugate resonant part is a fibre sum of squares over `i ↦ u_i^Q`.
- `riemannHypothesis_iff_eventually_re_xiLiPaired_of_value_le`: Li along any `P` with `|P(x₀)| ≤ 22`.
- `riemannHypothesis_iff_eventually_re_xiLiPaired_progression_le_45`: every progression of modulus `≤ 45`.
- Sharpness: `halfTurnPair_re_liTerm_eq_four` with `abs_arg_halfTurnRoot_twentyThree_le` shows the band angle alone cannot decide `46k + 23`.
- `abs_re_tsum_liTerm_add_dominant_le` (in `LiSignDensity`) now states `i ∈ D ↔ ‖v i‖ = R`.

Open [P]: odd moduli up to 89, and even moduli up to 88 with `b ≢ a/2`.

## Exact reach below modulus 90 (MUST-926, 2026-10-11)

Module `formal/GaloisForLFunctions/RHTower/LiSignProgressionsSharp.lean` (540 lines, standard axioms, wired). `riemannHypothesis_iff_eventually_re_xiLiPaired_progression_lt_90`: for `1 ≤ a ≤ 89`, every `b` except (`a ∣ 2b`, `a ∤ b`). With the half-turn and modulus-100 pairs, the band-angle classification of progressions is complete below 90.

## Exact abstract classification (MUST-929, 2026-10-11)

`formal/GaloisForLFunctions/RHTower/LiSignBohrRecurrence.lean` (437 lines, standard axioms, wired): `liThinning_iff_isBohrRecurrent`. Li thinning along `A` for all abstract families ⟺ `A` is a set of Bohr recurrence.
