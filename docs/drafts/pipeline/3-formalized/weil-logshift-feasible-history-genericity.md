# Generic divergence in the actual feasible history topology

Status: formalized and kernel-audited. Corpus only, 2026-10-09. Global lint has two unrelated HTGeometry umbrella-reachability errors.

## Target

For a bounded center `c`, any real precision profile `ε`, and prefix length `M`, let
`F(c,ε,M) = {h : BCF | (∀ j, |h j-c j| ≤ ε j) ∧ ∀ j<M, h j=c j}`.
Use its inherited supremum metric, not a parameter-space topology. A common native threshold `K` should ensure: if some `k≥K` also satisfies `k≥M` and `ε k>0`, nowhere moment-tail bounded histories form a dense residual subset of `F`. Signed summability at even one real shift and eventual moment boundedness at even one shift are meagre exceptions. For every strictly positive profile this applies to every finite prefix. No boundedness, decay-rate, or regularity condition on `ε` is needed. If `ε≥0`, the center belongs to `F`, so the result is nonvacuous.

## Corpus audit

Local query `research 'feasible precision history topology' --any --mode lexical --module WeilLogShift --no-refresh --json`: fts5, 103 matches, 38 eligible, 20 modules. Hits include arbitrary-precision parameter genericity, old exponential precision, and bounded cube results. Exhaustive WeilLogShift source search for `PrecisionHistorySet`, `FeasibleHistory`, and feasible-history descriptions found no actual feasible-set theorem. `WeilLogShiftBoundedHistory` is a product of intervals; its existing genericity uses product topology. `WeilLogShiftWeightedGenericity` uses the supremum parameter ball. Neither supplies this inherited feasible-history topology claim by a continuous-image argument.

## Dependency-closed paper proof

1. Evaluation at each coordinate is continuous in BCF. Each coordinate error constraint is closed, as is each prefix equality. Their intersection `F` is closed, hence complete.
2. Choose the common threshold from `exists_weilLogShiftRecoveryImpulse_two_amplitude_alternative` and a permitted coordinate `k≥max(K,M)` with `e=ε k>0`.
3. Fix any `h∈F`, radius `η>0`, and `a=h k-c k`, with `|a|≤e`. Put `δ=min(1/2,η/(4e))`. Then `0<δ≤1` and `2δe<η`.
4. Let `t±=δ*(±e-a)`. For each sign, the changed error is `(1-δ)*a±δe`, whose absolute value is at most `e`. All other coordinates stay unchanged. Since `k≥M`, prefix equalities persist. Both impulses are feasible. Moreover `|t±|≤2δe`, and the native unit impulse has norm at most one, so each history is within `η` of `h`.
5. The two amplitudes differ by `2δe>0`; native two-amplitude alternative makes at least one impulse nowhere bounded. Thus the nowhere-bounded set is dense in the actual feasible set.
6. Every origin tail excursion set is open by moment continuity and dense by step 5. Countable Baire intersection gives a dense residual origin-unbounded set. Native origin-to-all-shifts transfer yields the claimed all-real-shift property.
7. Native signed nonsummability follows from nowhere boundedness. Complements of these residual sets make existence of an eventually bounded or summable moment sequence at even one shift meagre.

No external source, numerical experiment, analytic premise, or openness claim for weight multiplication is used.

## Implementation plan

- `WeilLogShiftPrecisionFeasibleSet.lean`: feasible set, closedness, center membership, coordinate convexity estimate, direct density via two physical impulses.
- `WeilLogShiftPrecisionFeasibleGenericity.lean`: open excursions, Baire residuality, arbitrary positive profile corollaries, signed nonsummability and meagre exceptions.
- Wire both into RHTower, compile/export each leaf in sequence, audit all public declarations in a scratch file, refresh index and run formal lint. Preserve unrelated work.

## Log

- Previous arbitrary-weight parameter genericity fully compiled and axiom-audited; its card is in `3-formalized`.
- Current proof removes the parameter-topology limitation by proving density directly in the feasible set.

### Implementation checkpoint

- `WeilLogShiftPrecisionFeasibleSet.lean` compiles and exports cleanly. Its near-history theorem preserves every coordinate except the selected permitted late coordinate, strengthening bare density.
- `WeilLogShiftPrecisionFeasibleGenericity.lean` written and compiling. Both new leaves wired uniquely into the umbrella. Scratch API checks passed; this toolchain uses `abs_add_le` (not `abs_add`). No heartbeat limits changed.
- The general theorem requires only one sufficiently late positive tolerance beyond the prefix. All other tolerances can vanish; boundedness of the tolerance profile is unnecessary. Center membership separately proves nonvacuity whenever all tolerances are nonnegative.

## Final verification — 2026-10-09

- Both leaves compiled and exported cleanly using `lake --old env lean <leaf> -o <olean>`, one foreground process at a time. No full or umbrella build.
- Scratch `#print axioms` audit covers all 16 public declarations (13 theorems, two definitions, one abbreviation). Every declaration uses exactly `propext`, `Classical.choice`, and `Quot.sound`; no errors or warnings.
- Both imports are unique in `RHTower.lean`. Index refresh succeeded, and all 16 public declarations occur exactly once in the matching `LEAN_API.md` module rows.
- Latest authoritative lint exited 1 with only two unrelated HTGeometry umbrella-reachability errors: `LaurentCechVanishing` and `QKrawtchoukCompanionTriangular`. Neither new leaf has a lint finding. Unrelated modules were not modified.
- Paper proof and exact stronger nearby-single-coordinate theorem are formalized. Main claim concerns actual feasible histories with inherited supremum topology, not the parameter topology of the preceding increment. No boundedness assumption on the precision profile was introduced.

## Next corpus-derived conjecture

The native exceptional-amplitude set is subsingleton. Installed Lean proves that every subsingleton has zero measure under `MeasureTheory.NullSingletonClass`. This should give almost-everywhere global unboundedness for diffuse single-coordinate noise, including arbitrarily small positive interval noise preserving every other observation. Independent paper proof and local novelty audit are recorded in `docs/drafts/pipeline/1-in-progress/weil-logshift-diffuse-impulse-noise.md`; Lean work is pending there. This measure claim is derived from the exact fibre law, not inferred from Baire genericity.
