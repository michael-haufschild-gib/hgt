# One factorial regularization for each finite regular family

Status: dependency-closed paper proof; Lean implementation pending. Corpus-only research, 2026-10-09.

## Target

First prove the missing converse: a real sequence has a finite factorial majorant if and only if some factorial/exponential normalization is summable. A majorant supplies absolute summability after increasing the exponential damping rate by one.

Then prove finite-dimensional stabilization: on the factorial-regular submodule of any finite-dimensional linear sequence family, one factorial order and one exponential rate work for every regular vector. The normalized absolute sum is bounded by a constant times the vector norm.

For a bounded center and a finite impulse list, strengthen this to a single test for the entire affine family: there exist m, B, C≥0 such that, for every amplitude a,

`(∃ y, P(Moment_y(center + T(a)))) ↔ Summable(n ↦ exp(-B n) Moment_0(center + T(a),n)/(n!)^m)`.

For amplitudes satisfying this equivalent condition, the sum of normalized absolute values is at most `C (1+‖a‖)`. The choices may depend on center and finite index list. No late-index or positivity assumption is needed for this stabilization theorem; it does not assert which nonzero amplitudes are regular.

## Corpus and local library audit

Direct local query `factorial majorant summable uniform finite dimensional`, lexical OR with WeilLogShift filter: fts5 277 hits in 56 modules, 103 eligible under per-module cap. Exhaustive targeted `rg` over WeilLogShift leaves found `weilLogShiftHasFactorialMajorant_of_summable_normalization`, but no converse and no common-normalizer theorem on the finite regular submodule. The existing `weilLogShiftBoundedMomentSummable_iff_uniform_bound` concerns universal raw summability across all unit-bounded histories; it does not select a factorial normalization on the finite regular part.

Native ingredients: the majorant class is a real sequence submodule; affine moment differences equal the native continuous linear response; existence of a regular shift is equivalent to origin regularity. Finite-dimensional amplitude submodules and affine fibres are already formalized.

Local installed source `Mathlib.Analysis.SpecialFunctions.Exp` proves `Real.summable_exp_neg_nat`. `Module.finBasis` in `Mathlib.LinearAlgebra.Dimension.Free` supplies a finite basis. Read `Module.Basis.opNNNorm_le` and `opNorm_le` in `Mathlib.Analysis.Normed.Module.FiniteDimension`: the proof uses the continuous coordinate map `equivFunL`, finite basis expansion, and bounds every coordinate by an operator norm times the input norm. Exact APIs will be checked in scratch Lean before implementation. No external sources or numerical computations.

## Dependency-closed paper proof

1. Write P(f) for an eventual bound `|f(n)| ≤ D exp(A n) (n!)^m`. Replace D by |D| if necessary. For n beyond its cutoff, normalization with the same m and rate B=A+1 has absolute value at most `|D| exp(-n)`. The factorial denominator is strictly positive. Local geometric-exponential summability, comparison, and invariance under changing a finite prefix give absolute summability. The reverse implication is already formalized. Thus existential factorial regularity and existential summable factorial normalization coincide.
2. Let R:E→(ℕ→ℝ) be linear with E finite-dimensional and normed. Set L=R⁻¹(P), a finite-dimensional submodule. Choose a finite basis vᵢ of L. Each R(vᵢ) has its own mᵢ,Aᵢ,Dᵢ,Nᵢ. Choose m=Σmᵢ, A=Σ|Aᵢ|, N=ΣNᵢ. These dominate every basis parameter. Since n!≥1 and n≥0, each basis tail is bounded by `|Dᵢ| exp(A n) (n!)^m`.
3. Absorb the finitely many values before N into a nonnegative constant Dᵢ' for each basis vector. This is possible because `exp(A n)(n!)^m` is strictly positive at every n, including zero. Thus the common envelope holds at every n for every basis vector. The zero-dimensional case has empty sums and zero response.
4. The finite coordinate functionals cᵢ on L are continuous, so `|cᵢ(a)| ≤ Cᵢ ‖a‖` for nonnegative constants Cᵢ. Basis expansion and the triangle inequality give the global uniform envelope `|R(a)(n)| ≤ D ‖a‖ exp(A n)(n!)^m`, with D=ΣCᵢDᵢ', for every a∈L and every n.
5. Normalize all these responses using B=A+1. The absolute normalized terms are bounded by `D ‖a‖ exp(-n)` for all n. Consequently the normalized series is absolutely summable and its absolute sum is bounded by `C ‖a‖`, with C=DΣexp(-n). No infinite-dimensional closedness of P is required.
6. For a finite affine family F(a)=Moment_0(center+T(a)), if no regular amplitude exists, any fixed m,B works for the equivalence: summability would imply P and contradict emptiness. Its norm bound is vacuous.
7. Otherwise choose a regular a₀. The regular amplitudes are a₀+L, where L is the P-preimage under the linear response map. Apply the same finite-basis envelope construction to the finite collection consisting of F(a₀) and the responses of a basis of L. This yields one m,A and a bound by a constant times `1+‖a-a₀‖`. The triangle inequality absorbs a₀ into a constant times `1+‖a‖`. Increasing the rate to B=A+1 gives the stated common normalization and absolute-sum bound for all regular amplitudes.
8. Conversely, summability under that one fixed normalization implies origin P by the existing theorem, hence existence of a regular shift. This proves the equivalence for every amplitude, including all irregular ones. The weights are fixed before the amplitude quantifier.

## Boundaries and implementation plan

This is an origin-normalization theorem. Do not assert that the same exponential rate regularizes every unbounded real shift. Do not assert a common rate across arbitrary centers or dimensions, a minimal order/rate, computable choices, regularity of any early impulse, or sufficiency of the earlier positive balance equation. The theorem selects a common normalization on the actual regular subspace/fibre, which may be zero-dimensional or empty.

Implement and audit the sequence-level converse first. Then verify finite-basis, coordinate-norm, summability-comparison, and finite-prefix APIs locally; formalize the uniform linear envelope and its finite affine specialization. If Lean exposes a stronger statement, send it through a new paper/novelty audit before extending the claim. Compile only owned leaves, audit every public declaration, wire umbrella, refresh index, and lint. No implementation of this follow-up has started.


## Implementation refinement — 2026-10-09

The same claims admit a shorter dependency-closed implementation. For the sequence converse, use eventual geometric comparison; then summability bounds every normalized term by its absolute sum, yielding a global factorial envelope without a separate finite-prefix construction. For a finite basis, the single sequence `g(n)=Σᵢ|R(vᵢ)(n)|` belongs to P by finite addition and absolute-value closure. A global envelope for g and the bounded basis-coordinate map give the uniform linear envelope directly, avoiding individual parameter maxima.

For the affine specialization, homogenize `F(a)=R(a)+F(0)` to the linear map `H(a,t)=R(a)+t F(0)` on E×ℝ. Apply the regular-submodule theorem to H and restrict to t=1. The norm bound `‖(a,1)‖≤1+‖a‖` gives the requested affine bound and handles empty fibres automatically. This changes only the proof; it adds no regularity hypothesis or stronger claim. Exact local APIs are being checked before implementation.


The homogenization argument applies verbatim to any affine map from a finite-dimensional real normed space into real sequences: its linear part and value at zero define H, and F(a)=H(a,1). This general affine statement is included in the paper proof; the native bounded-history moment family is then a specialization via its already-proved affine map. No continuity into an infinite-dimensional sequence topology is assumed or needed.

Sequence comparison, summability/tsum, finite-basis expansion, and coordinate-norm APIs passed scratch checks (the basis scratch had one harmless unused-variable warning). The sequence normalization leaf and uniform linear leaf are written; the first direct compile exposed a missing local type annotation for a summability comparison, now corrected. Native results are not yet claimed verified.


`WeilLogShiftFactorialNormalization.lean` compiles/exports cleanly. Its four public theorems prove the extra-damping term bound, exact equivalence between a factorial majorant and a summable normalization with positive rate, a global envelope with positive rate/nonnegative prefactor, and a quantitative absolute-sum bound from a global envelope. The uniform linear leaf is ready for compilation after the affine homogenization API check. No resource limits changed.


## Final Lean checkpoint — 2026-10-09

Status: **FORMALIZED**. This completed audit supersedes earlier pending Lean-check notes.

- `WeilLogShiftFactorialNormalization.lean`: four theorems, clean direct leaf compile/export.
- `WeilLogShiftUniformFactorialLinear.lean`: two theorems, clean direct leaf compile/export.
- `WeilLogShiftUniformFactorialAffine.lean`: two theorems, clean direct leaf compile/export.
- All leaf checks used `lake --old env lean`; exported oleans newer than sources.
- All eight public theorem axioms audited in a scratch file: exactly `propext`, `Classical.choice`, `Quot.sound`.
- Three unique RHTower umbrella imports; index refresh exited 0; all eight declarations found exactly once in indexed results.
- Fresh formal lint exited 1 with one unique unrelated existing error: unreachable `GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular`. No new-leaf lint errors.

Mathematical result: factorial majorizability equals existence of an exponential/factorial summable normalization. Every finite-dimensional linear or affine sequence family admits one fixed normalization detecting its entire regular locus, with a uniform absolute-sum norm bound. Native bounded-history affine families inherit the result, with origin summability equivalent to regularity at some shift. No continuity assumption into the sequence space was added. No uniformity across unbounded shifts, centers, or dimensions is asserted.

Corpus audit used existing Lean declarations only; no external papers, web searches, or numerical experiments. Current user directive: use only our local Lean corpus as mathematical source. The research goal remains active.


Subsequent formalized strengthening: [uniform factorial regularity across every real shift](weil-logshift-uniform-all-shift-factorial-regularity.md). The later theorem supplies one normalization across all real shifts, in addition to all regular amplitudes of the finite-dimensional family.
