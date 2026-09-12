# Verified progress: actual Maass map into quotient L2 and all Hilbert generators

Continue the active Selberg/Maass correspondence goal; do not mark it complete or blocked. This turn closed a real analytic gap. Selberg 1/4, completed full group intertwining, and arithmetic exclusion remain unfinished.

## Proof chain and proved advance
Original principal-congruence Maass form -> compact annular reproducing kernel -> globally bounded every Euler word and every changing-weight Maass ladder -> actual quotient L2 admission -> injective finite-model map -> actual Hilbert norm derivatives for E+F, i(E-F), iH -> canonical norm identification -> completed unitary group intertwiner -> arithmetic exclusion of complementary series -> 1/4.

Actual all-order derivative/global bounds apply for every positive real eigenvalue and positive principal congruence level. Finite model/generator theorems take the potential exceptional eigenvalue subtype 0<lambda<1/4, as required for this contradiction route. No supplied derivative bound, generator-domain interface, mean law, or extra axiom is used.

## Installed and verified
Under formal/GaloisForLFunctions:
- HTGeometry/SmoothCylinderKernel.lean: C-infinity periodic annular kernels, derivatives preserving support, division by a radial function proved nonzero on the strip, coth-weighted transpose operations, vanishing radial endpoints.
- HTGeometry/SmoothCylinderIntegral.lean: compact-cylinder Fubini, both integrations by parts, norm estimate, actual divergence identity.
- HTGeometry/CompactSmoothParameterIntegral.lean: derive compact-product derivative majorant and differentiation under the fixed compact integral.
- RHTower/MaassCircleDifferential.lean: public along/circle derivatives, smooth coordinates, generic circle_source_smooth_family; old circle_source_smooth specializes it.
- RHTower/MaassCircleTransfer.lean: actual horizontal and vertical base-flow derivatives expressed in circle radial/angular coordinates.
- RHTower/MaassCircleKernel.lean: exists_reproducing_kernel, from the already proved circular mean multiplier and a normalized smooth annular bump divided by that multiplier.
- RHTower/MaassCircleDerivativeBounds.lean: actual transfer to kernels, word_kernel_representation, all_euler_words_bounded (line 141).
- RHTower/MaassLadderDerivativeBounds.lean: boundedEulerSpace stable under both Euler operators and arbitrary-weight raise/lower; ladders_all_euler_words_bounded.
- RHTower/MaassLadderQuotientL2.lean: literal automorphic inversion/quotient lift; unit-norm K-character; complete raised/lowered ladders in the actual finite quotient L2.
- RHTower/MaassModelQuotientL2.lean: namespace RHTower.MaassModelQuotientL2; modelToLp (line 80), modelToLp_injective (89), literal representative modelToBounded_apply. Reuses Mathlib BoundedContinuousFunction.toLp and its full-support injection.
- RHTower/MaassModelHilbertGenerators.lean: SAME namespace MaassModelQuotientL2; modelToLp_diagonal_hasDerivAt (79), rotation (92), quarterDiagonal (106). These are actual quotient-unitary norm derivatives on every finite model vector. The private general curve helper is fully instantiated by the three existing concrete Maass pointwise flow derivatives.

No further needed olean builds for this chain. All ten new modules wired exactly once in correct umbrellas.

## Final audits
- Combined scratch /tmp/maass_all_hilbert_generators.lean passed. Time-shift helper then simplified and separately passed /tmp/maass_time_shift.lean.
- Final foreground: LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.MaassModelHilbertGenerators. Exit 0; 12690 dependency jobs visited, 12 changed/needed modules built, remaining dependencies cached/replayed. Not an umbrella/full build. One Lean child under the build parent was verified.
- Those 12 modules have no warnings. 79 old dependency warning lines replayed.
- /tmp/maass_hilbert_axioms.lean checked 108 public declarations; exact axiom union propext, Classical.choice, Quot.sound. No native certificate or added axiom. Summary /tmp/maass_hilbert_axiom_summary.json.
- No heartbeat, recursion, transparency, runtime limit increases; no sorry/admit/opaque/unsafe. Scoped whitespace and exact-once umbrella checks passed.
- scripts/formal_tools.py index succeeded, generated LEAN_API/GAPS/OVERVIEW refreshed; 38 changed, 0 removed includes concurrent work.
- Final lint --check-generated EXIT 1 ONLY because unrelated untracked HTGeometry/InversePowerCancellation.lean is unreachable from its umbrella. No generated-staleness error. Initial lint also reported another worker's ThetaCuspHawkingBMFundamentalBoundaryRecovery; that was wired concurrently before final lint.
- No remaining task Lean processes. All tool sessions collected. No commits/pushes performed by this agent.
Logs /tmp/maass_hilbert_final_build.log, /tmp/maass_hilbert_axioms.log, /tmp/maass_hilbert_generated_lint.log.

## Next hard target; concrete paper mechanism
Use actual unitary inner-product invariance + the newly proved Hilbert derivatives. Mathlib Analysis/InnerProductSpace/Calculus.lean has HasDerivAt.inner for real-parameter complex Hilbert curves. Differentiate to show A=E+F and B=i(E-F) skew; solve the two identities to obtain E-adjoint=-F. Compact iH gives distinct K-weight orthogonality.
For THIS corpus's normalization (read RealSphericalHarishChandra.lean 49-74):
E e_m=(nu-1/2-m)e_(m+1); F e_(m+1)=(nu+1/2+m)e_m.
Hence (m+1/2-nu)||T e_(m+1)||^2=(m+1/2+nu)||T e_m||^2.
DO NOT use the inverse ratio from the opposite convention.
RealSphericalComplementaryWeights and RealSphericalComplementarySeries already give positive weights, their recurrence, and the explicit invariant Hermitian form; RealPrincipalSeriesCompactUnitarity transports it to the compact picture. Search found no verified existing uniqueness theorem. Prove actual pullback form equals ||T e_0||^2 times that canonical form, via orthogonality and recurrence in both integer directions. Then extend the normalized isometry to completion.

For subsequent full group intertwining, a concrete analytic-vector route was worked out on paper and recorded in the card (NOT yet a Lean theorem):
||E e_m||^2/||e_m||^2=lambda+m(m+1), F similarly lambda+m(m-1), each square-root coefficient <=|m|+1.
For support |m|<=M, E,F norm <=M+1 and enlarge support by one; A and B bound <=2(M+1).
Thus ||A^n v|| <=2^n (M+n)!/M! ||v||, similarly B. The exponential series converges for |t|<1/2, controlled by binomial(M+n,n)(2|t|)^n. Actual unitary orbit Taylor remainders can identify these series; subgroup multiplication extends in time. Remaining formal work includes invariant closure and comparison with the completed group model.
Local positivity permits the whole complementary interval; it supplies no congruence arithmetic exclusion. Do not spend effort on the old finite-coset/quotient normalization constant: it is unnecessary for this route.

## Searches and literature
Custom research/deep/method searches used extensively before code. Key exact reusable hit:
HTGeometry.hasDerivAt_toLp_two_of_dominated in L2DominatedDerivative.lean, whose source proof was read. New model derivative global bound discharges its majorant.
Other reusable hit: BoundedContinuousFunction.toLp_injective; full source read.
Deep search for invariant Hermitian form uniqueness returned existing canonical form/packet restrictions, no actual norm identification.
Broad arXiv localization/transference searches screened primary abstracts:
https://arxiv.org/abs/2609.02425 (compact-group WZW localization; no noncompact SL2 generator input)
https://arxiv.org/abs/2608.17982 (dense/sparse combinatorial transference; no needed analytic estimate)
No result from these papers was used in a proof.

## Persistence and practical Lean notes
Research card docs/drafts/pipeline/1-in-progress/selberg-actual-maass-model-intertwiner.md updated TOP status and appended detailed proof/audit/next-target records.
Previous memory: mem:selberg/actual-maass-circle-darboux-scalar-mean-2026-09-12.
Keep one foreground Lean process, lake env lean scratch, lake build capstone only at final audit, never full/umbrella builds or raised limits. No subagents authorized.
For real -> complex outer curve composed with real time shift, use HasDerivAt.scomp, NOT comp. Specify (h := fun s : ℝ => s-t) to avoid unifier choosing t-s. Current helper checks explicit t-t point, then rw [mul_assoc, <- hp, show t+(s-t)=s by rw [add_comm, sub_add_cancel]].
Serena symbol tools ignore formal paths in this project; earlier failure verified. New files via normal file tools; read before changes.
