# CHMD: the cross-sign bonus identity of the Lévy form

- **ID:** chmd-odd-cross-sign-bonus-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional
- **Source:** user request 2026-10-16 ("formalize: for one-signed odd tests, Λ∞(Θv) = Λ∞(Θ|v|) + 4∬_{s,t>0} g(s)g(t)ω(s+t) with g = Θ|v|"); continuation of MUST-1562
- **Statement:** (1) pointwise: for `f ≤ 0` on `(−∞,0]`, `f ≥ 0` on `[0,∞)`, `x > 0`: `(f(u)−f(u+x))² = (|f(u)|−|f(u+x)|)² + 4·1_{(−x,0)}(u)|f(u)||f(u+x)|`. (2) `jumpEnergy f = jumpEnergy |f| + 4·crossSignBonusL |f|` (ℝ≥0∞), `Λ_∞(f) = Λ_∞(|f|) + 4·crossSignBonus |f|` (`C²_c`). (3) `crossSignBonus g = ∬_{s,t>0} ω(s+t) g(s) g(t)` (product Lebesgue measure on the quadrant) for continuous even `g ≥ 0`, via Tonelli and the shear `(s,t) ↦ (s+t, −s)`. (4) Doob gauge: `Λ_∞(Θv) = Λ_∞(Θ|v|) + 4·bonus(Θ|v|)` for odd `v ≥ 0` on `[0,∞)`; on the cone with support in `(−log 2, log 2)`: `Λ_∞(Θ|v|) + 4·bonus(Θ|v|) ≤ E(v)`; `bonus(Θ|v|)` in quadrant form.
- **Status:** STATUS MUST-1565. One leaf (`CHMDOddCrossSignBonus`; 26 declarations), standard axioms; `lake env lean` clean; `lake build --old` green; wired.

## Gates
- [x] 0 → 1, [x] 1 → 2, [x] 2 → 3 (`weilLevyForm_eq_abs_add_bonus`, `crossSignBonus_eq_quadrant`, `levy_phiDoob_eq_abs_add_bonus`, `levy_abs_add_bonus_le_sourceEnergy_of_odd_oneSigned`)
- [ ] 3 → 4

## Paper proof
Pointwise: on `(−x, 0)` the two values have opposite signs, `(−|a| − |b|)² = (|a|−|b|)² + 4|a||b|`;
elsewhere both lie on one side of the origin and `|f(u) − f(u+x)| = ||f(u)| − |f(u+x)||`. Integrate in
`u` (both terms continuous with compact support), then in `x` against `ω`; the parametric integrals
are measurable because the planar integrands are strongly measurable (`integral_prod_right'`),
so the lintegral of the sum splits. Finiteness of the jump energy of a `C²_c` test makes both
summands finite and gives the real identity. For the quadrant form, write the inner integral as a
lintegral of the indicator of `{0 < x, −x < u < 0}`, apply Tonelli, and pull back along the shear
`(s,t) ↦ (s+t, −s)` (a composition of `(s,t) ↦ (s, s+t)`, the swap, and negation in one
coordinate, each Lebesgue-preserving): the region becomes the open quadrant, the kernel
`jumpKernel(s+t) = ω(s+t)`, and `g(−s) = g(s)` by evenness.

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDOddCrossSignBonus.lean` — see STATUS MUST-1565 for the declaration list.

## Next
Compare `4·bonus(g)` with the pole mass `2C(g)²`: `bonus(g) ≥ (∫_{s>0} g(s)e^{−s/2})²` from
`ω(s+t) ≥ e^{−(s+t)/2}`; the remaining prime-free target on the cone is
`weilArchRe(g) + 4·bonus(g) ≥ 2C(g)²` for nonnegative even `g` of support `≤ 2 log 2`.
