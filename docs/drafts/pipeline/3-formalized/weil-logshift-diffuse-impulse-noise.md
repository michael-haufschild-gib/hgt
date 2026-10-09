# Almost-sure divergence under diffuse single-coordinate noise

Status: formalized and kernel-audited. Corpus-only research, 2026-10-09. Latest global lint has nine unrelated HTGeometry umbrella-reachability errors.

## Target

Upgrade the native at-most-one-exception impulse law to an almost-everywhere statement. There should be a common threshold `K` such that, for every bounded center, every `k≥K`, and every measure `μ` on real amplitudes with `MeasureTheory.NullSingletonClass μ`, almost every amplitude produces moment tails unbounded at every real shift, hence signed nonsummability at every shift. No probability normalization or sigma-finiteness is needed for this statement.

Specialize to Lebesgue measure restricted to a nonempty positive interval inside an arbitrary precision bound. With any prescribed exact prefix and any strictly positive profile, a single late coordinate can receive a strictly upward random error, all other coordinates remain exact, and almost every permitted amplitude gives global moment divergence. Record positivity of the interval's volume so this is nonvacuous.

## Local corpus audit

- `research 'impulse measure' --mode lexical --module WeilLogShift --no-refresh --json`: fts5, zero matches.
- Broadened `research 'impulse exceptional' --any --mode lexical --module WeilLogShift --no-refresh --json`: 18 matches, nine eligible, five modules. Native source argument is `exists_weilLogShiftRecoveryImpulse_exceptional_subsingleton` in `WeilLogShiftImpulseLineObstruction.lean:83`.
- Exhaustive source scan of WeilLogShift leaves for `NoAtoms`, `∀ᵐ`, almost-sure, diffuse, and atomless found no existing noise theorem. Existing MeasureTheory namespace opens alone do not establish this result.
- Installed Lean source `Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean:42` proves `Set.Subsingleton.measure_zero` under `NullSingletonClass μ`. The class means every singleton has zero measure. The old name `NoAtoms` is deprecated in this toolchain; do not use its deprecated module or alias.
- Same local file provides a restriction instance `Measure.restrict.instNullSingletonClass` and `Set.Countable.ae_notMem`. API applicability still needs a scratch Lean audit before implementation.

## Dependency-closed paper proof

1. Native impulse theorem supplies `K` and states that, on every late impulse line around every bounded center, the set of amplitudes failing global tail unboundedness is subsingleton.
2. A measure vanishing on all singleton sets vanishes on this exceptional set by the installed `Set.Subsingleton.measure_zero` theorem. This uses no measurability assumption on the exception set.
3. By the definition of almost everywhere, global tail unboundedness holds almost everywhere for that measure. Native nowhere-bounded-to-nowhere-summable theorem supplies signed nonsummability jointly at all real shifts.
4. Lebesgue measure restricted to `Ioo 0 (ε k)` still vanishes on singletons. Positive `ε k` makes this a nonempty interval of positive finite measure. Almost every amplitude is in the interval, so it is strictly positive and smaller than the desired coordinate tolerance.
5. Choose `k≥max(K,M)`. A physical impulse changes only coordinate `k`; its error equals the amplitude there and zero everywhere else. Thus the arbitrary positive profile is respected and every prefix observation is unchanged. Step 3 applies on the same restricted measure.

This is a direct measure consequence of the corpus's exact exceptional-fibre law. It does not infer almost-sure behavior from Baire genericity and does not claim a measure on the whole infinite-dimensional history space.

## Next steps

- Verify current local measure and `ae_iff`/restriction/interval-volume APIs in `/tmp` Lean.
- Formalize general null-exception and almost-everywhere theorems, then the exact-prefix arbitrary-precision interval-noise corollary.
- Compile/export only new leaves sequentially, wire umbrella, audit every public declaration, refresh index, run lint, clean owned scratch files.

## Current log — 2026-10-09

- Fresh corpus query `diffuse impulse` (`--any --mode lexical --module WeilLogShift --no-refresh --json`) returned 19 matches, 11 eligible, six modules: existing impulse and feasible-set APIs, no diffuse-noise theorem.
- New leaves reserved: `WeilLogShiftDiffuseImpulse.lean` and `WeilLogShiftArbitraryPrecisionNoise.lean`; both paths were absent before implementation.
- Scratch concrete proofs verify the intended common-threshold almost-everywhere result, positive finite interval volume, and almost-everywhere interval membership. Auxiliary polymorphic API `have` checks for `ae_iff` and `measure_mono_null` require two universe levels in this toolchain; correcting those checks before final audit.
- Use `NullSingletonClass`, not the deprecated `NoAtoms` alias. No measurability of the exceptional set, normalization of the measure, or sigma-finiteness assumption is needed for the null-singleton argument.

### Formal implementation checkpoint

Both `WeilLogShiftDiffuseImpulse.lean` and `WeilLogShiftArbitraryPrecisionNoise.lean` now compile and export cleanly with the required leaf-only `lake --old env lean` command. Five public theorems cover null exceptions for every diffuse measure, joint almost-everywhere nowhere boundedness and signed nonsummability, measure-zero bounded/summable exceptions, and arbitrary-precision single-coordinate interval noise. The common-threshold precision theorem needs only nonnegative tolerances globally and positive tolerance at the selected late coordinate; all others may be zero. It proves positive finite permitted interval volume. Both leaves are wired into the umbrella. Exhaustive axiom audit, index refresh, and lint remain before moving this card.

The subsequent exact accumulated quadratic-exponent column growth conjecture is now formalized; its paper argument and final audit are recorded in `docs/drafts/pipeline/3-formalized/weil-logshift-quadratic-column-growth.md`.

## Final verification — 2026-10-09

Both leaf modules compiled/exported cleanly, sequentially, with `lake --old env lean <leaf> -o <olean>`. No full or umbrella build. All five public theorems passed the exhaustive scratch `#print axioms` audit, each using exactly `propext`, `Classical.choice`, and `Quot.sound`; no warnings or errors. Both umbrella imports are unique. Index refresh succeeded and all five public theorem rows were checked individually. No old API changed and no analytic assumption or new axiom was introduced.

Latest formal lint exited 1 with nine unrelated HTGeometry umbrella-reachability errors and no finding in the new leaves:

- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.AmbientMaps
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.NonnegativeWeights
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.PicardUFD
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.PolynomialChartIntersection
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ReesCoefficientKernel
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.SourceFiltrationProper
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.UnitCocycle
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ZeroLocusInterface
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular

The measure result covers every real amplitude measure vanishing on points, without sigma-finiteness or normalization. The concrete restricted-Lebesgue corollary includes positive finite permitted interval volume and proves exact observations away from the selected late coordinate, arbitrary nonnegative precision bounds with one positive permitted coordinate, and any prescribed exact prefix. The strictly positive profile corollary selects that coordinate beyond the native threshold and prefix. This completes the paper target and its stronger nonnegative-profile variant.

The quadratic-growth follow-up was subsequently formalized and moved to `3-formalized`. Its next exposed task is finite factorial-power regularization, recorded separately in `1-in-progress`.
