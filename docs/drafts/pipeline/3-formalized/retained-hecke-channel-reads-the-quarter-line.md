# The retained Hecke channel reads the quarter line

- **ID:** F0311-Q3-4.2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0311/fable.md` §4.2; loop card `1-in-progress/fable-0311-q3-breakthrough-questions.md`
- **Statement:** At every upper Mayer resonance `s`, the retained `T₂` boundary channel
  `u_s = core_s(2)·1_{(0,1)}` has co-isometry defect
  `D_s(u_s) = ‖u_s‖²_LP − ‖I_{½−s̄} u_s‖²_LP = |core_s(2)|² ∫₀¹ (1 − b^{1−4 Re s}) w(b) db`,
  which is `> 0` iff `Re s < ¼`, `= 0` iff `Re s = ¼`, `< 0` iff `Re s > ¼`. Reflected resonances
  `s ↦ ½ − s̄` carry opposite signs.

## Answer to §4.2

Yes, in the corpus's sign functional for PM (the Lewis co-isometry defect `D_s`). The full resonant
period has `D_s ≤ 0` on both sides and `= 0` only on `Re s = ¼`: it detects the line but not the side.
The single boundary channel that `T₂` retains — the coefficient `core_s(2)`, the unique `c` with
`T₂ core_s − c·1_{(0,1)} ∈ L²(da/a)`, nonzero at every resonance — carries the signed defect, with the
sign of `¼ − Re s`. The reading is exact and unconditional at every resonance; it records the side of
the line on which the resonance lies and does not force it onto the line. Arithmetic enters only
through `core_s(2) ≠ 0` (the Euler factor of `T₂` cannot cancel the channel); the sign itself is the
exponent `4 Re s − 2` that the inversion `I_{½−s̄}` assigns to the upper cusp.

## Paper proof

Let `w(b) = (b + 1/b)^{−6} b^{−1/2}`, `σ = Re s`, `s' = ½ − s̄`, `c = core_s(2)`.

1. `‖u_s‖²_LP = |c|² ∫₀¹ w`.
2. `(I_{s'} u_s)(a) = a^{−2s'} c·1_{a>1}`, `|a^{−2s'}| = a^{2σ−1}`. Substituting `a = 1/b`
   (`∫_{(0,∞)} g = ∫_{(0,∞)} b^{−2} g(1/b)`) and `w(1/b) = b w(b)`:
   `‖I_{s'} u_s‖²_LP = |c|² ∫₀¹ b^{2−4σ} b^{−2} b w(b) db = |c|² ∫₀¹ b^{1−4σ} w(b) db`.
3. Integrability on `(0,1)`: `w(b) ≤ b^{11/2}` (since `(b + 1/b)^{−6} ≤ b^6`), so `b^e w(b) ≤ 1` for
   `e ≥ −11/2`; here `e = 1 − 4σ > −1`.
4. `D_s(u_s) = |c|² Φ(σ)`, `Φ(σ) = ∫₀¹ (1 − b^{1−4σ}) w`. On `(0,1)`, `1 − b^{1−4σ}` is `> 0` for
   `σ < ¼`, `< 0` for `σ > ¼`, `≡ 0` for `σ = ¼`; a strictly positive integrable function has positive
   interval integral. `c ≠ 0` (`mayerPeriodCore_two_ne_zero`), so `|c|² > 0`.
5. `Re(½ − s̄) = ½ − σ`: the reflected resonance lies on the other side.

## Lean

`formal/GaloisForLFunctions/RenormalizedIntersectionTheory/MayerScattering/TheRetainedHeckeChannelReadsTheQuarterLine.lean`:
`heckeBoundaryChannel`, `channelProfile`, `lewisCriticalWeight_inv`, `lewisCriticalWeight_le`,
`integrableOn_rpow_mul_weight`, `lewisCriticalNormSq_heckeBoundaryChannel`,
`lewisCriticalNormSq_inversion_heckeBoundaryChannel`, `lewisCoIsometryDefect_heckeBoundaryChannel`,
`channelProfile_pos`, `channelProfile_neg`, `channelProfile_quarter`, `channelProfile_sign`,
**`retainedHeckeChannel_defect_sign`**, `retainedHeckeChannel_unique`,
`retainedHeckeChannel_defect_reflect`.

Checked with `lake --old env lean` (exit 0, no errors); transitive axioms of
`retainedHeckeChannel_defect_sign` and `retainedHeckeChannel_defect_reflect`: `propext`,
`Classical.choice`, `Quot.sound`. Wired into `RenormalizedIntersectionTheory.lean`.

## Log
- 2026-11-04 — paper proof and Lean formalization completed
