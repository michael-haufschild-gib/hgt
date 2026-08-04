# MR unit 3 closed: the κ-criterion; Littlewood region licensed (2026-08-04)

Card: `docs/drafts/pipeline/1-in-progress/mr-splice-wide-range-mean-square.md` (full inequality
chain there).

Audit result: both MR-note routes for the corridor reduce to a formalized zero-free region
`σ ≥ 1 − c/(log t)^κ` with **κ < 1**:
- (B)'s [4,L11] absorption: `log P ≳ (log T)^{(1+κ)/2}` vs rough saving `log P = o(log X)` —
  simultaneous iff κ < 1; Littlewood's loglog-refined κ=1 passes with `(loglog X)^{-c}` saving
  (enough: MRBilinear is Tendsto→0, no rate).
- Formalized reality: corpus strip AND vendored `PNTPlus.ZetaZeroFree` are both κ = 9
  (`Ico (1 − A/(log|t|)⁹) 1`; `MediumPNT` error `exp(−c(log x)^{1/10})`). DLVP (κ=1) is nowhere
  formalized and would not suffice anyway.
- Spot checks: κ=9 → log P ≥ (log T)⁵ impossible; κ=2/3 → `(log X)^{-1/6+o(1)}` saving.

**Licensed next analytic build (tier 1): the Littlewood region.** Chain: Weyl differencing for
`∑_{n≤N} n^{it}` ⇒ `ζ(1+it) ≪ log t/loglog t` (and near-1 growth) ⇒ 3-4-1-style region
`σ ≥ 1 − c·loglog t/log t`. mathlib owns van der Corput for oscillatory integrals; sum version
via Abel summation. PNTPlus's ZetaBounds/Perron layer is the natural base to extend.

Route-B scoreboard: units 1 (PrimePowerSupport), 2 (PrimePowerLargeValuesCount) built and
axiom-clean; unit 3 (this audit) closed; unit 4 (sharp-cutoff Halász sup from
MoebiusUniformFrequency) not region-gated, still open; unit 5 numeric re-certification pending
the region tier choice.
