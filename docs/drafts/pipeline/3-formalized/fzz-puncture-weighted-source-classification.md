# FZZ puncture universal weighted-source classification

- **ID:** FZZ-P-WSC
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + UNIVERSAL BOUNDARY + POSITIVE SURVIVOR
- **Parent:** FZZ-P-GSL
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION] [UNIVERSAL BOUNDARY] [POSITIVE SURVIVOR]` For every target energy and arbitrary scalar source, a nonzero puncture `L²` point mode exists exactly when source divided by spectral distance is `L²` and source is nonzero almost everywhere; state is unique.

## Goal

Close scalar local occurrence problem without choosing a source family. Replace repeated power,
affine, fractional, and logarithmic examples by exact arbitrary-source criterion.

This does not identify literal FZZ/GFZZ source map or derive a zeta-selective global node law.

## Gates

- [x] 0 → 1 in-progress: arbitrary-source conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: canonical quotient, uniqueness, nonzero criterion
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claim

For `E : ℝ` and arbitrary `v : ℝ → ℂ`, define

`f_E,v(x) = -v(x)/(x-E)`

and require `f ∈ L²(ℝ)` with `(x-E)f(x)+v(x)=0` almost everywhere. A nonzero solution exists iff

`f_E,v ∈ L²(ℝ)` and `v ≠ 0` almost everywhere.

Whenever it exists, every solution equals `f_E,v` almost everywhere. No separate measurability
hypothesis on `v` is needed: `MemLp f_E,v` includes the relevant strong measurability.

## Complete paper proof

Singleton `{E}` has Lebesgue measure zero. For almost every `x`, `x-E ≠ 0`; dividing the equation
there gives `f(x)=-v(x)/(x-E)`. Thus every solution is the canonical quotient almost everywhere.
Conversely, canonical quotient satisfies equation away from `{E}`. It is an admissible state exactly
when it belongs to `L²`. Division by nonzero `x-E` preserves pointwise vanishing away from `{E}`,
so canonical state is zero almost everywhere iff source is zero almost everywhere. Combining these
facts proves exact iff and uniqueness.

## Hostile review and priority verdict

- Range criterion for multiplication operator is classical functional analysis.
- Exact arbitrary-source specialization, Lean closure, and subsumption of route's full local
  threshold ladder are new to project; external priority remains provisional.
- Model is scalar representative equation, not full interacting self-adjoint FZZ Hamiltonian.
- Source can be engineered to satisfy criterion at every chosen energy, so local occurrence is
  intrinsically nonselective.
- Result does not prove literal winding-condensate source has required weighted vanishing.
- Literature audit found general Friedrichs/rank-one spectral analyses but no exact route-specific
  arbitrary-source Lean theorem or FZZ occurrence classification.

Verdict: multiplication-operator range law `[REDISCOVERED]`; exact route-wide universal closure and
formal subsumption `[NEW] [CLASSIFICATION]`, external priority provisional.

## No-go closure

- **Killed shortcut:** further chosen local germ families can solve source-independent occurrence
  burden. Universal criterion already decides every scalar source.
- **Sharp positive survivor:** nonzero `v` with `v/(x-E) ∈ L²`; state is forced uniquely.
- **Sharp obstruction:** any source whose weighted quotient fails `L²` admits no nonzero point mode.
- **New insight:** local occurrence invariant is exactly weighted resolvent membership, not Taylor,
  fractional, or logarithmic order separately. Earlier thresholds are corollaries.
- **Remaining core:** identify literal FZZ/GFZZ source coefficient-faithfully, test its weighted
  quotient, then derive global zeta-selective node set without fitting target zeros.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/FZZCigarPunctureWeightedSourceClassification.lean`
- Canonical state: `fzzPunctureWeightedResolventState`
- Equation and uniqueness: `fzzPunctureWeightedSourceEigenEquation`,
  `fzzPunctureWeightedSourceEigenEquation_state_unique`
- Nonzero equivalence: `fzzPunctureWeightedResolventState_ae_zero_iff`
- Universal occurrence law: `fzzPunctureWeightedSourcePointMode_iff`
- Zero-source exclusion: `not_fzzPunctureWeightedSourcePointMode_zero`
- Prior threshold recovery: `fzzPunctureWeightedSourcePointMode_fractional_iff`,
  `fzzPunctureWeightedSourcePointMode_criticalLog_iff`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.FZZCigarPunctureWeightedSourceClassification`
  passed (`11599/11599`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from corpus affine, fractional, and critical-log classifications.
- 2026-08-27 — universal weighted-source iff, uniqueness, nonzero law, and earlier-family
  subsumption paper-proved and formalized.
