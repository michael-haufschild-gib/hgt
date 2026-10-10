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
