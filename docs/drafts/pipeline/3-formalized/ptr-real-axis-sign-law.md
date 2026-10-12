# The real-axis sign law (B') for critical points of Ξ

- **ID:** ptr-real-axis-sign-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional partial producer for one half of an exact RH split
- **Source:** PTR loop rows 158 and 289–290 (λ = ∞ endpoint of the producer family `Ξ + iλΞ'`)
- **Statement:**
  - Every real critical point `t₀` of `Ξ` with `Ξ(t₀) ≠ 0` outside all off-line cones
    `|Im ρ − t₀| < |Re ρ − ½|` has `Ξ(t₀)Ξ''(t₀) < 0`.
  - Failure heights in `[20, V]` have measure at most `2·offLineMoment(V+1)`, which is at most
    `67(V+1)/500` eventually.

## Context
Row 158 (paper): RH ⟺ (A) `ξ' ≠ 0` on `Re s > ½` ∧ (B') no real critical point with `ΞΞ'' ≥ 0` off the
zero set. The corpus has the window form of the split (`XiDerivOffLineCount`), Speiser disks for (A)
(`XiDerivSpeiserDisk`) and the non-strict cone criterion (`XiHorizontalSliceConeCriterion`). (B') itself is
strict.

## Gates
- [x] 0 → 1, [x] 1 → 2, [x] 2 → 3: `RHTower/XiRealCriticalPointSignLaw.lean` (310 lines), standard axioms,
  olean built, wired, lint clean for the module.

## Result
MUST-1313. (B') holds unconditionally at every critical point outside the cones of off-line zeros, hence on
at least 86.6% of heights.

**Open:** the remaining (B') failures are exactly critical points inside cones of off-line zeros. Ruling them
out needs a reason why a shallow off-line pair cannot create a nonzero local minimum of `|Ξ|`. That is the
same RH core.

## Log
- 2026-10-12 — created and formalized (PTR loop rows 289–290).
