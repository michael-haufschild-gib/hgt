# Rigidity of finite factorial regularity on impulse lines

Status: formalized and kernel-audited. Corpus-only research, 2026-10-09. Global lint findings are recorded below.

## Target

Define finite factorial majorant membership for a real sequence `f` by
`P(f) := ∃ m : ℕ, ∃ A D : ℝ, ∃ N : ℕ, ∀ n≥N, |f(n)|≤D*exp(A*n)*(n!)^m`.

There should be a common native threshold `K` such that, for every bounded center and every `k≥K`, the amplitude set
`{t : ℝ | ∃ y : ℝ, P(moment_y(impulse(center,k,t)))}`
is subsingleton. The shift, factorial order, exponential rate, prefactor, and cutoff may all vary with the amplitude. Do not fix them before comparing amplitudes or weaken the conclusion to countably many exceptions.

As consequences, every measure vanishing on points assigns this exceptional set measure zero, and almost every amplitude has no finite factorial majorant at any real shift. Every factorial-and-exponentially normalized signed moment series is then nonsummable, jointly for all shifts and all normalization parameters.

## Corpus audit

- `research 'factorial majorant impulse' --any --mode lexical --module WeilLogShift --no-refresh --json`: fts5, 39 matches, 25 eligible, 15 modules. Returned current envelope and native impulse results; no factorial-regularity exceptional-fibre theorem.
- Exhaustive WeilLogShift source scan for `FactorialMajorant`, factorial/subsingleton, factorial/some-shift, and factorial/origin found no such class or theorem.
- `WeilLogShiftUniformBallGenericity.lean:54–71` was read: for `y≠0`, native `eventually_mul_pairedLogKernel_le_of_abs_lt` with origin and multiplier one gives eventual `pairedLogKernel 0 n≤pairedLogKernel y n`. The common recovery coefficient then gives `|moment_0(h,n)|≤|moment_y(h,n)|` eventually. This works directly from the moment definition and kernel positivity.
- `WeilLogShiftImpulseLineObstruction.lean:41–47` supplies the exact affine difference identity
  `moment_y(line(t),n)-moment_y(line(u),n)=(t-u)*Response(y,n,k)`.
- Current factorial regularization leaves compile. Their exported response theorem rules out every eventual majorant `D*exp(A*n)*(n!)^m` at every shift under one common threshold.
- Existing `Set.Subsingleton.measure_zero` under `MeasureTheory.NullSingletonClass` was verified in the preceding diffuse-noise increment. Use that current class, not the deprecated `NoAtoms` alias.

## Dependency-closed paper proof

1. `P` contains the zero sequence and is closed under subtraction and scalar multiplication. For subtraction, take `m=max(m₁,m₂)`, `A=max(A₁,A₂)`, `D=|D₁|+|D₂|`, and `N=max(N₁,N₂)`. For natural `n`, `n!≥1` makes factorial powers monotone in their order, and `n≥0` makes `exp(A*n)` monotone in `A`. Triangle inequality proves the common bound. Scalar multiplication replaces `D` by `|c|*D`; nonzero scalar multiplication preserves membership in both directions by applying the inverse scalar. These are concrete positive closure laws for the class, not an assumption about it.
2. If some shifted moment sequence belongs to `P`, the origin moment sequence belongs to `P`, with the same order/rate/prefactor and an enlarged cutoff, using the audited eventual kernel comparison. Conversely origin membership supplies a witness shift `0`. Thus existential shift membership is exactly origin membership.
3. Suppose two amplitudes `t≠u` both satisfy the existential-shift condition. Step 2 puts their origin moment sequences in `P`; step 1 puts their difference in `P`. The native difference identity makes this difference `(t-u)*Response(0,·,k)`. Inverting the nonzero scalar puts the origin response column in `P`, contradicting the newly formalized no-factorial-majorant theorem. Hence there is at most one exceptional amplitude.
4. Every point-null amplitude measure vanishes on the subsingleton exceptional set. This yields the joint almost-everywhere failure of all finite factorial majorants at all real shifts without any countable-union or measurability premise.
5. If, for some `y,m,A`, the normalized signed moment series were summable, its terms would tend to zero. Eventually their absolute values would be at most one. Multiplying by the positive factors `exp(A*n)*(n!)^m` gives an eventual majorant for the original moment sequence, with prefactor one. This contradicts the almost-everywhere statement from step 4 and proves joint nonsummability of every such normalization.

## Boundaries

- The exceptional amplitude need not exist. Prove at most one, not unconditional existence or uniqueness.
- The result concerns failure of every eventual finite factorial majorant. It does not assert that the normalized magnitudes of an arbitrary affine-center history tend to infinity; center-dependent cancellations may prevent that stronger limit.
- The exact rigidity comes from closure of the union of all finite factorial classes and the native difference law. Do not infer it merely from separate fixed-parameter null-set results.
- Natural factorial powers are the formal target. Any library-level real-order Gevrey bridge still requires separate audit.
- Early columns remain outside the current native threshold.

## Plan

Implement the finite-majorant predicate and positive closure laws, prove existential-shift membership reduces to origin, then prove exceptional-amplitude rigidity and its diffuse-measure/normalized-nonsummability consequences. Verify every new local API in scratch Lean; compile new leaves sequentially, wire umbrella, audit every public declaration, refresh index, run lint, and clean owned scratch files.

## Current log — 2026-10-09

- Fresh corpus query `factorial majorant rigidity shift` (`--any --mode lexical --module WeilLogShift --no-refresh`) returned 525 matches, 121 eligible, 61 modules. Relevant hits are the native coefficient/response no-majorant theorems; no finite-factorial class or impulse rigidity theorem was identified.
- New paths `WeilLogShiftFactorialMajorant.lean` and `WeilLogShiftFactorialImpulseRigidity.lean` were absent before implementation.
- Native response no-majorant signature rechecked. Scratch API verification covers monotonicity of factorial powers, nonzero scalar cancellation, and the point-null measure-to-almost-everywhere conversion.
- First leaf will expose the majorant predicate, positive algebraic closure laws, eventual-domination closure, normalized-summability implication, and some-shift/origin equivalence. Second leaf will prove the joint exceptional-amplitude classification and diffuse-measure consequences.

### First leaf verified

`WeilLogShiftFactorialMajorant.lean` compiles/exports cleanly. The predicate and all planned closure laws are formalized, including eventual-domination closure and the implication from summable normalized terms to an original factorial majorant. The some-shift/origin equivalence also compiles. `WeilLogShiftFactorialImpulseRigidity.lean` is compiling its joint exceptional-amplitude and point-null measure statements. Both leaves are wired into the umbrella; final axiom audit, index, and lint remain.


## Final verification — 2026-10-09

Both `WeilLogShiftFactorialMajorant.lean` and `WeilLogShiftFactorialImpulseRigidity.lean` compiled and exported cleanly using direct leaf commands with `lake --old env lean`, without resource-limit changes. All 13 public declarations (one definition and 12 theorems) passed the scratch `#print axioms` audit with exactly `propext`, `Classical.choice`, and `Quot.sound`. Both modules occur once in the RHTower umbrella; all 13 declarations occur once in the refreshed Lean API index.

The formal lint command exited 1 with three unique unrelated unreachable-module findings: `GaloisForLFunctions.HTGeometry.HankelSecantKernel`, `GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular`, and `GaloisForLFunctions.RHTower.VonMangoldtNonPrimeSqrtSum`. No finding concerns these two leaves. These unrelated modules were not modified.

The formalized survivor is an exact exceptional-fibre classification: on every sufficiently late impulse line, at most one amplitude has a finite factorial majorant at any real shift. Consequently every point-null amplitude measure assigns the exceptional set measure zero, and almost every amplitude simultaneously defeats all such majorants and all factorial/exponential summability normalizations at all shifts. Existence of an exceptional amplitude, divergence to infinity for arbitrary affine histories, and independence of distinct impulse columns modulo factorial-regular sequences are not asserted.


## Formalized finite-family follow-up

`docs/drafts/pipeline/3-formalized/weil-logshift-factorial-finite-error-space.md` now classifies regular amplitudes for arbitrary linear error maps as an affine subspace. In every finite dimension, one late impulse in the range makes that subspace closed, Haar-null, and nowhere dense. Both follow-up leaves and all 11 public declarations are compiled and kernel-audited.
