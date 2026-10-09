# Positive weighted balance for all regular finite error amplitudes

Status: formalized and kernel-audited. Corpus-only research, 2026-10-09. Global lint findings are recorded below.

## Target

For one common late threshold K, every finite list of indices kᵢ ≥ K admits strictly positive weights wᵢ such that the functional

`Φ(a) = Σᵢ wᵢ (-1)^kᵢ aᵢ`

is constant on every factorial-regular amplitude set, for every bounded center history. The same weights work for all centers; only the constant may change with center. Regularity means existence of any real shift and any finite factorial majorant, with all parameters allowed to vary with amplitude.

At the arithmetic center the constant is zero. This is a necessary positive weighted balance law, not an equivalence with regularity and not an exact codimension-one classification.

## Local corpus and library audit

The direct lexical query `positive annihilator submodule` returned no hits. The broadened local query `strict separation compact subspace`, OR with Weil module filter, returned fts5 937 hits in 387 modules, 582 eligible under per-module cap; leading hits concern other Weil separation mechanisms and do not supply this finite-error law. Exhaustive targeted source searches found no Stiemke/Gordan finite-error annihilator theorem. The corpus's polarized-incidence Farkas statements concern a different image/closure problem; no applicability is assumed.

Native ingredients: `WeilLogShiftAlignedImpulseCone` now compiles the exact sign-aligned finite-response obstruction and the arithmetic moment identity. `WeilLogShiftFactorialAmplitudeSpace` supplies the majorant sequence submodule and affine moment map. `WeilLogShiftFactorialMajorant` supplies subtraction closure and some-shift-to-origin reduction. The exact bounded-history moment subtraction identity is already formalized.

Read the installed Lean sources for `geometric_hahn_banach_closed_compact` in `Mathlib.Analysis.LocallyConvex.Separation`: disjoint closed convex and compact convex sets admit a continuous linear functional with strict separating constants. Read the definition, convexity, compactness, and coordinate-vector membership statements for `stdSimplex` in `Mathlib.Analysis.Convex.StdSimplex`. These are local Lean sources, not external papers. Exact application APIs still need scratch Lean verification.

## Dependency-closed paper proof

1. Fix a finite all-late list, and write sᵢ=(-1)^kᵢ. Let S be the diagonal involution `(Sb)ᵢ=sᵢ bᵢ`, so S²=id. Let T be the existing finite impulse map. Form the linear response map `U(b)(n)=MomentCLM(0,n)(T(Sb))` and the submodule L=U⁻¹(P), where P is the factorial-majorant sequence submodule. This is a finite-dimensional submodule, hence closed and convex; no closedness of P in the infinite-dimensional sequence space is assumed.
2. L is disjoint from the standard simplex Δ={b : bᵢ≥0 and Σbᵢ=1}. Indeed a=Sb has aᵢsᵢ=bᵢ≥0 and is nonzero. The compiled aligned-cone theorem excludes a factorial majorant for its origin response. That contradicts b∈L.
3. Local strict separation gives a continuous real linear functional f and real constants u<v with f(l)<u for every l∈L and v<f(b) for every b∈Δ. Since 0∈L, 0<u. Linearity forces f to vanish on L: if f(l)≠0, then `(u/f(l)) l∈L` but its functional value equals u, contradicting the strict upper bound.
4. Each standard coordinate vector eᵢ belongs to Δ. Hence wᵢ=f(eᵢ)>v>u>0. Finite coordinate expansion gives f(b)=Σwᵢbᵢ. Therefore every factorial-regular centered response at amplitude a obeys f(Sa)=Σwᵢsᵢaᵢ=0. This proves the arithmetic-anchor balance by the native full-moment identity. When the index type is empty, all positivity conditions are vacuous and Φ=0; the conclusion remains valid.
5. Take two regular amplitudes a,b for the same arbitrary bounded center. Their witnessing shifts may differ. Reduce both to origin regularity, subtract their sequences in P, and apply the native affine difference identity. The result is the linear response at T(a-b), so S(a-b)∈L. Thus Φ(a-b)=0 and Φ(a)=Φ(b).
6. If a center has a regular amplitude a₀, take its constant to be Φ(a₀); otherwise take zero and the statement is vacuous. This establishes one common positive normal for all centers, without asserting existence of a regular amplitude at any given center.

## Boundaries and implementation plan

The weights depend on the finite index list. Do not assert compatibility across lists, a countably infinite strictly positive annihilator, a uniform lower bound on weights as dimension grows, uniqueness/canonicity, or computable values. Do not identify regularity with the single balance equation. No claim of a full-rank or rank-one quotient follows.

First verify the finite-dimensional simplex separation argument and diagonal sign map in scratch Lean. Then formalize the native response submodule, arithmetic balance, and pairwise/all-center affine balance. Keep any generic separation helper private unless the independent generic statement earns its own paper/novelty audit. Compile only owned leaves, audit every public declaration, wire umbrella, refresh index, and lint. Implementation and final verification are recorded below.


## Implementation log — 2026-10-09

Current native statements and installed strict-separation/coordinate-expansion APIs were rechecked. The implementation will encode the diagonal phase change directly in a finite-sum linear response map, with its majorant preimage as a local submodule. This avoids unnecessary public phase-map/submodule definitions while retaining the exact paper argument. Generic simplex separation remains private. The scratch Lean check is checking the complete positive-annihilator argument, including annihilation from an upper bound on a submodule and finite coordinate expansion.


The complete generic positive-annihilator argument has now passed the scratch Lean check, including dimension zero. The coordinate-expansion lemma requires an explicit `change` from the underlying linear map to the continuous functional and a pointwise equality identifying its basis vectors with `Pi.single`. The two native leaves are written: `WeilLogShiftPositiveResponseBalance` provides the positive response balance; `WeilLogShiftPositiveAffineBalance` provides the exact finite moment difference, the shared positive normal for all centers, and the arithmetic-anchor certificate outside its kernel. The response leaf is compiling; no native result is claimed verified yet.


`WeilLogShiftPositiveResponseBalance.lean` now compiles/exports cleanly, proving the unconditional common-threshold existence of strictly positive weights annihilating every factorial-regular origin response. The weights require no distinctness of the index list and the proof covers dimension zero. `WeilLogShiftPositiveAffineBalance.lean` is compiling. Both new leaves are wired into the umbrella. Final axiom audit, index refresh, and lint remain.


Both native leaves now compile/export cleanly without warnings or resource-limit changes. The affine extension was checked with explicit bounded-history coercions and the exact moment-difference identity. All four public theorems are now in the scratch axiom audit. The final theorem provides strictly positive weights independent of center, an offset for each regular affine fibre, zero offset at the arithmetic anchor, and exclusion of every factorial majorant/normalization whenever the arithmetic-anchor balance is nonzero. This is a necessary balance law, not a sufficient condition for regularity.


## Final verification — 2026-10-09

Both `WeilLogShiftPositiveResponseBalance.lean` and `WeilLogShiftPositiveAffineBalance.lean` compiled/exported cleanly using direct `lake --old env lean` leaf commands, without warnings or resource-limit changes. All four public theorems passed scratch `#print axioms`, each listing exactly `propext`, `Classical.choice`, and `Quot.sound`. Index refresh exited 0; all four declarations are indexed once, both umbrella imports are unique, and both exports are current relative to their sources.

Formal lint exited 1 with two unique unrelated unreachable-module findings: `GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular` and `GaloisForLFunctions.HilbertMetric.HorizontalLamzouriMergeMixed`. No finding concerns the two owned leaves. These unrelated modules were not modified. This is the current lint snapshot for status reporting.

The resulting positive invariant is one strictly positive parity-adjusted normal for each finite all-late list, fixed before every center and amplitude. It annihilates every regular response, is constant on every regular affine fibre, and vanishes on the regular arithmetic fibre. A nonzero arithmetic-anchor balance excludes every real regular shift and every factorial/exponential normalization. No converse or codimension-one equality is asserted.

The next dependency-closed paper proof is `docs/drafts/pipeline/3-formalized/weil-logshift-uniform-factorial-regularization.md`: complete the sequence-level normalization converse, then collapse the varying orders/rates on a finite regular subspace or affine fibre to one common normalization with a uniform absolute-sum bound. Its Lean implementation has not started.
