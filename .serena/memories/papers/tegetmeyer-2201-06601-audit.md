# arXiv:2201.06601 (Tegetmeyer, "Proof of the Riemann Hypothesis") — audited, closed

Card: `docs/drafts/pipeline/3-formalized/tegetmeyer-2201-06601-fractional-part-rh-audit.md`

## Verdict
The paper does not prove RH. Its analytic ingredients are correct; its two load-bearing steps are
false. Everything true is now Lean-certified, and each false step has an unconditional Lean
refutation. Axiom audit on every capstone: `[propext, Classical.choice, Quot.sound]`.

## New modules (all wired into the area umbrellas)
- `GaloisForLFunctions/HTGeometry/RealBaseCpowPolar.lean` — `re`/`im` of `(x:ℂ)^w` for `x > 0`.
- `GaloisForLFunctions/HTGeometry/LogTrigPowerPrimitives.lean` — `cosLogPrimitive`,
  `sinLogPrimitive`, `cosLogSecondPrimitive`, `sinLogSecondPrimitive`, their `HasDerivAt` laws and
  evaluated interval integrals. General exponent `c`; the paper's four cases are `c = -a`, `c = a-1`.
- `GaloisForLFunctions/HTGeometry/LogPhaseNoLimit.lean` — a nonzero harmonic is periodic and
  nonconstant, so `A cos(b log x) + B sin(b log x)` has no limit at `+∞`; amplified version
  `x^d · (…)`, `d > 0`; `N^d` has no finite limit.
- `GaloisForLFunctions/HTGeometry/LogTrigPowerPrimitiveGrowth.lean` — second primitives diverge;
  `|primitive| ≤ x^c·K`; boundary term `{N}P(N) → 0`; jump-free partial integration has no limit.
- `GaloisForLFunctions/HTGeometry/FractionalPartPartialIntegration.lean` — the corrected identity
  `∫_1^{m+1} {x} f = ∑_{k<m} P(k+2) - (W(m+1) - W 1)` for any kernel with two primitives on the
  positive ray, plus its cos/sin instances.
- `GaloisForLFunctions/RHTower/ZetaFractionalPartTrigEquations.lean` — eq (1),(2) in the paper's
  multiplied form; polar split; the two real integrals equal `re`/`-im` of `1/(s-1) - ζ(s)/s`;
  the four explicit values at a zero in the open strip.
- `GaloisForLFunctions/RHTower/ZetaFractionalPartUnitIntervalExpansion.lean` — truncated integrals
  expanded over unit intervals; they converge; the jump-free expression does not.
- `GaloisForLFunctions/RHTower/ZetaReflectionMultiplierExplicit.lean` — `reflectionMultiplier` in
  `π`/`Γ` coordinates `= Γ_ℝ(1-s)/Γ_ℝ(s)`; nonzero on the open strip; `Γ_ℝ(-2) = 0`; and
  `¬ ∀ s, ζ s = 0 ↔ ζ (1-s) = 0` via `ζ(-2) = 0`, `ζ(3) ≠ 0`.
- `GaloisForLFunctions/RHTower/CriticalLineExtractionGap.lean` — `C = (a/b)S ∧ C = ((1-a)/b)S`
  forces only `a = 1/2 ∨ (C = 0 ∧ S = 0)`; the bare implication to `a = 1/2` is false; the two
  limits the paper equates do not exist.

## Reused, not reproved
- `RHTower.FractionalPartZeta.integral_Ioi_one_fract_cpow_of_re_pos` — the integral representation
  on `Re s > 0` (already owned, via Abel summation + analytic continuation).
- `RHTower.ReflectionCocycleClass.riemannZeta_one_sub_eq_zero_iff` — open-strip zero symmetry.

## The four errors
1. Partial integration with `u = {x}`, `u' = 1`. `{x}` drops by `1` at every integer, so the
   classical formula is invalid on `[1,N]`; the correct expansion carries `∑_{k} P(k)`.
2. The surviving expression `{N}P(N) - (W(N) - W(1))` has no limit: `W` grows like `N^(1-a)` times
   a harmonic whose amplitude never vanishes for `b ≠ 0`. The integral it evaluates does converge.
3. `lim cos(b log N)`, `lim sin(b log N)`, `lim N^a` are all nonexistent (`b ≠ 0`, `a > 0`), so
   eqs (21)–(28) manipulate undefined objects.
4. Even granting the two proportionality relations, `a = 1/2` needs `S ≠ 0`, which is never
   established (and is unavailable, by 3).
