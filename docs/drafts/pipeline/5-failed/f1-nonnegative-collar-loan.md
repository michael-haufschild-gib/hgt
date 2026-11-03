# Nonnegative collar loans fail at the first fold

- **ID:** F1-CL
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** [F1 tower assembly](../1-in-progress/f1-window-tower-assembly.md).
- **Modules:** `WindowTowerOfSpecZ/TheCubicWindowHasExactJumpMoments.lean`,
  `WindowTowerOfSpecZ/TheFirstFoldPaysANegativeFrozenDirection.lean`.
- **Statement:** The uniform first-stage collar loan is false. A real C² witness supported in `[-21/20,0]` has `Q₁(H)<0<Q(H)`.

## Exact witness and proof

Let `f(x)=x max(1−4x²,0)`, `E=∫f²=2/105`, and `C(t)=∫f(x)f(x+t)dx`.
For `0≤t≤1`,
`C(t)=2/105−2t²/5+2t³/3−2t⁵/5+4t⁷/35`; for `t>1`, `C(t)=0`.
Direct integration gives
`∫₀¹C=0`, `∫₀¹(E−C)/t=(457/210)E`,
`∫₀¹t(E−C)=(7/12)E`, and `∫₀¹t²(E−C)=(47/120)E`.

Write `Γ=gammaBracket(0)`, `ω=archLevyDensity`, `Ω(y)=∫ᵧ∞ω` and
`J=2∫₀∞(E−C(t))ω(t)dt`. The existing kernel estimates imply

`(457/210+1/2−7/288−47/1920+2Ω(1))E ≤ J ≤ (457/210+1/2+2Ω(1))E`.

Indeed, on `(0,1]`,
`1/2+t/4−t²/48−t³/32 ≤ tω(t) ≤ 1/2+t/4`;
the tail is exactly `2Ω(1)E`. Existing antiderivative bounds give
`log2+π/4−1/4+1/96 ≤ Ω(1) ≤ 251/200`; moreover `−269/50<Γ<−26/5`.
Consequently `ΓE+J<−(29/2100)E`.

Only prime `2` contributes. Rational log bounds give
`C(log2)≤−33E/100` and `w₂=log2/√2≥49/100`.
Oddness kills the cosh pairing. Since `∫xf(x)dx=1/30`,
`|sinhPairing(f)|≤cosh(1/4)/30` and `cosh(1/4)²≤16/15`,
the pole cost is at most `(7/225)E`. Thus the exact complete value satisfies

`Q(f)=ΓE+J−2w₂C(log2)−sinhPairing(f)²/2 > E/100`.

The frozen value `Q(f)+2w₂C(log2)` is strictly below `−29E/2100`.
Compact-source mollification preserves both the complete energy and `C(log2)`.
For sufficiently narrow mollifiers, both signs persist and the support lies in
`[-21/40,21/40]`. Translation by `−21/40` gives the asserted window test.
Since `log2<21/20<log3`, locality identifies its complete form with stage `2`;
the exact stage recurrence identifies its negative frozen value with stage `1`.

## No-go and positive survivor

- **Refuted candidate:** `Q₁(H)≥Ω(21/20−log2)∫collarWeight·H²` for every first-stage test.
  Its right side is nonnegative; this witness has negative left side.
- **Positive survivor:** The *same* test has strictly positive complete Weil energy.
  Prime `2` repairs its negative frozen direction through a negative lag correlation.
- **New insight:** A stage proof must retain `w(F−C)`. Requiring frozen nonnegativity,
  even before charging any collar mass, already excludes positive complete tests.
- **Scope:** This rejects the sufficient collar loan, not the exact signed tower route or RH.
- **Lean status:** Both modules pass `lake --old env lean`.
  `exists_first_stage_negative_frozen_positive_complete` proves the joint survivor;
  `exists_first_stage_positive_exit_loan_failure` proves the loan failure.
  The raw cubic bounds and both smooth-witness theorems have transitive axioms exactly
  `propext`, `Classical.choice`, `Quot.sound`. Both modules are wired into `WindowTowerOfSpecZ.lean`.
