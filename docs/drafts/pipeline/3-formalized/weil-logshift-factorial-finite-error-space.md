# Affine classification of factorial-regular finite error patterns

Status: formalized and kernel-audited. Corpus-only research, 2026-10-09. Global lint findings are recorded below.

## Target

For a bounded center history c and a linear finite-dimensional perturbation map T, classify

`E(c,T) = {a | ∃ y, the moment sequence of c + T(a) at y has a finite factorial majorant}`.

Prove E(c,T) is an affine subspace (possibly empty), hence closed in finite dimensions. If the range of T contains any sufficiently late unit impulse, prove this affine subspace proper, Haar-null, and nowhere dense. Instantiate T with an arbitrary finite list of impulse columns, requiring only one sufficiently late column. Columns need not be distinct. This allows cancellations; it does not assert independence modulo regular sequences or identify the exact codimension.

## Corpus audit

Direct local research query `factorial majorant affine subspace`, lexical OR, WeilLogShift module filter, cached index: fts5, 46 hits in 14 modules, 23 eligible under the per-module cap. Exhaustive `rg` of all WeilLogShift Lean leaves found the new majorant class and single-line rigidity results, but no affine-subspace classification.

Verified local sources: `WeilLogShiftFactorialMajorant` proves linear closure of the majorant class and reduces existence of a regular shift to origin regularity. `WeilLogShiftUniformBallPerturbation` supplies the exact affine moment subtraction identity. `WeilLogShiftFiniteMatrixReceiver` defines the unit impulse response as the corresponding moment continuous linear map and supplies the arithmetic anchor. `WeilLogShiftFactorialRegularization` supplies the common late-column threshold and excludes every factorial majorant.

Installed Lean library sources provide `AffineSubspace.comap`, `Submodule.toAffineSubspace`, `AffineSubspace.closed_of_finiteDimensional`, `MeasureTheory.Measure.addHaar_affineSubspace`, and `IsNowhereDense.of_isClosed_null`. Exact namespaces and argument signatures will be checked in a scratch Lean file before use. No external sources or numerical experiments.

## Dependency-closed paper proof

1. Let P be the real vector subspace of sequences admitting some eventual bound `D exp(A n) (n!)^m`. Closure is already formalized, with all four parameters allowed to vary by sequence.
2. For any real module of amplitudes, define F(a)=M_0(c+T(a)). Its linear part is `a ↦ (n ↦ MomentCLM(0,n)(T(a)))`. The native moment subtraction identity proves the affine identity exactly, including the fixed arithmetic baseline.
3. E(c,T)=F⁻¹(P). The some-shift/origin equivalence proves that this single affine inverse image captures existence over every real shift and all majorant parameters. Thus E is an affine subspace, including the empty case. For any a₀∈E, it is exactly a₀ plus its direction subspace; no existence of a₀ is presumed.
4. Suppose T(v) is a unit impulse at index k above the native common threshold. If E were the whole amplitude space, then 0 and v would both be in E. Subtracting their P-sequences would put `(n ↦ MomentCLM(0,n)(T(v)))`, exactly the late response column, in P. This contradicts the proved native no-majorant theorem. Hence E is proper.
5. Every affine subspace of a finite-dimensional real normed vector space is closed, including the empty one. Every proper such subspace has Haar measure zero. Haar measure is positive on nonempty open sets, so closed null E is nowhere dense. The complement is therefore open and dense, and almost every amplitude simultaneously has no factorial-majorant shift.
6. For any finite list of indices kᵢ, the map T(a)=Σᵢ aᵢ Unit(kᵢ) is linear. The coordinate vector at i maps exactly to Unit(kᵢ), even if indices repeat. Any one late kᵢ proves the range condition without an independence assumption.

## Boundaries

No closedness claim for the infinite-dimensional regular history space. No claim that every nonzero finite combination is irregular. No exact rank or codimension, no matched quadratic upper growth estimate, and no early-column theorem. No assertion that arbitrary affine-history normalized magnitudes tend to infinity. The summability exclusion follows from the existing theorem that summability implies a majorant; it is weaker than magnitude divergence.

## Plan

1. Verify installed Lean affine/measure APIs and construct exact amplitude affine subspace.
2. Prove native late-column properness, finite-dimensional nullness/nowhere density, and the finite-list instance.
3. Compile only owned leaves, audit every public declaration, wire umbrella, refresh index, run formal lint, and record findings.


## Current verification log — 2026-10-09

Installed affine-subspace, finite-dimensional closedness, Haar-nullness, nowhere-density, finite-sum, and scalar APIs passed the scratch Lean check, including direct inference of the Haar open-positive measure instance. `WeilLogShiftFactorialAmplitudeSpace.lean` now compiles and exports cleanly. Its six public declarations construct the sequence submodule, exact affine moment map, amplitude affine subspace, all-shift membership equivalence, translate classification, and a common properness threshold uniform over all real amplitude modules. The proof uses the native moment subtraction identity with explicit bounded histories to avoid coercion matching ambiguity.

`WeilLogShiftFactorialFiniteErrors.lean` is now compiling. Both new leaves are wired into the umbrella. Final declaration audit, index refresh, and lint remain.


Both owned leaves now compile and export cleanly, with no warnings and no resource-limit changes. The finite-error leaf contains the finite-dimensional closedness theorem, the common Haar-null/nowhere-dense threshold, the finite impulse linear map, its coordinate-vector identity, and the fully quantified finite-list exceptional-set theorem. The threshold is uniform in dimension, center, and all impulse indices; only one listed index must exceed it. Scratch axiom audit of all 11 public declarations is running.

## Exposed next question

Determine the rank of a finite set of distinct late response columns modulo the factorial-majorant sequence submodule. The present result proves only that this rank is positive when one late column is present. It neither proves independence nor identifies any cancellation directions. The exact direction submodule of the new affine amplitude space is the concrete invariant for that next audit. A next conjecture must be chosen after examining the native coefficient recurrence and any existing column-ratio/cancellation lemmas; no rank-one or full-rank assertion is made here.


## Final verification — 2026-10-09

Both new leaves compiled/exported cleanly using direct `lake --old env lean` leaf commands, without warnings or resource-limit changes. Every one of the 11 public declarations (four definitions and seven theorems) passed scratch `#print axioms` with exactly `propext`, `Classical.choice`, and `Quot.sound`. Index refresh exited 0. All 24 public declarations across this increment and the preceding impulse-rigidity increment occur once in `formal/LEAN_API.md`; all four corresponding umbrella imports are unique.

Latest formal lint exited 1 with four unique unrelated unreachable-module findings: `GaloisForLFunctions.HTGeometry.PaperIdealPowerReesFiltration`, `GaloisForLFunctions.HTGeometry.PaperNativeReesSpecialization`, `GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular`, and `GaloisForLFunctions.RHTower.ZeroGapLargeGapTail`. No finding concerns the four owned leaves. These unrelated modules were not modified. Earlier lint snapshots on earlier cards remain historical, not the current result.

A local follow-up audit of the exact coefficient recurrence and the entire existing older-tail/growth argument exposes an alternating-sign law and an explicit cone of noncancelling finite errors. The formalized result is recorded separately in `docs/drafts/pipeline/3-formalized/weil-logshift-alternating-column-cone.md`; all three touched leaves compile and all 12 public theorems pass the axiom audit. This is a finer positive result than properness and does not settle the full quotient-rank question.
