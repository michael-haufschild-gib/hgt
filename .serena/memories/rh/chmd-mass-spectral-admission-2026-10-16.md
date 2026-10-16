# CHMD mass spectral admission and sampling completeness — 2026-10-16

RH goal remains ACTIVE and unproved. This turn is progress: actual arbitrary-mass automatic operator-domain admission, not a new bound or RH equivalence.

Card: docs/drafts/pipeline/3-formalized/chmd-mass-spectral-admission-2026-10-16.md.
Namespace RHTower.CHMDDoobGraph. Five new root-wired leaves:
- CHMDMassFourierReadout (14 declarations)
- CHMDMassMixedExplicitFormula (12)
- CHMDMassSpectralAdmission (15)
- CHMDMassSamplingCompleteness (24)
- CHMDMassPolarCompletion (18)

## Exact structural results
For arbitrary actual MassSpace w, with no prior graph/energy/operator-domain premise:
1. mass_silent_iff_resolvent_half: all literal Xi-zero and both polar Fourier samples vanish iff Rw=(1/2)•w. Gives maximal arithmetic-domain admission, Lw=w, unique actual signed-radical graph lift 2•rieszLift w.
2. massSamplingSpan_closure: closed span of literal real/imaginary mass Fourier kernels at Xi zeros and poles equals the mass-orthogonal complement of the critical eigenspace. Every mass vector has a unique reduced representative with the same samples (exists_unique_reduced_mass_source). This is dual-kernel completeness, not primal cardinal-series synthesis.
3. Stronger mass_zero_samples_mem_arithmetic_domain: vanishing Xi-zero samples alone forces maximal-domain admission. mass_zero_samples_graph_admission supplies an actual full-nullspace graph source; sourceMap injectivity gives uniqueness. Define explicit rank-two b(w)=massPolarImage w from the two real polar moments and opposite polar Fourier kernels. mass_zero_samples_resolvent_identity proves R(2w+b(w))=w, and arithmeticGenerator_zero_samples proves Lw=w+b(w). mass_zero_samples_unique_polar_decomposition gives polar graph source + critical remainder.
No RH, zero-simplicity, finite-off-line-zero, or prior-domain assumption. Vanishing-sample hypotheses specify the vector class; the result does not assert that arbitrary primitive bound states have vanishing samples.

## Mechanism
Uniform strip mass-dual kernel norm bound + absolutely summable compact-test Fourier coefficients => mixed explicit formula converges in mass-dual operator norm. Dense sourceMap extends compact signed generator pairing from graph to arbitrary mass vectors. Joint silence annihilates (L-1)v on compact C2 tests; existing compact C2 operator core extends to maximal domain. Testing v=Rz and self-adjointness gives w=2Rw. Converse uses graph lift and existing full radical theorem. Hilbert orthogonal-complement duality yields kernel completeness. Subtract actual polar graph matching both poles for the stronger zero-only theorem; full graph mixed formula and Riesz uniqueness identify explicit rank-two generator image.

## Duplicate-work correction
User pointed to CHMDBirmanSchwingerBound.lean. Exact theorem CHMDPolar.orthonormal_primitive_bound_states_le at line 471 assumes offLineZeros.Finite and gives k ≤ 2*offLineZeros.ncard for orthonormal primitive eigenvectors of R above 1/2. Already covers finite counting, not exclusion or automatic mass-domain admission. Direct source check and standard-axiom audit passed. Do not reprove it. Existing no-Weyl/pure-point results also supersede the old local-compactness spectral payoff; previous own proposal moved to docs/drafts/pipeline/5-failed/chmd-local-compactness-levy-averages-2026-10-16.md as duplicate, not mathematical no-go, with existing positive survivors recorded.

Three deep searches (cardinal-generator, finite-divisor, mass-nullspace) completed partial=false, no errors or unfinished stages; inventory 72,861/72,861. Compiler metadata mostly pending/stale. Follow-up hybrid OR query 'primitive bound states offLineZeros Birman Schwinger' returned exact counting theorem and negative-subspace rank argument as top candidates; partial=true due interrupted text/source retrieval, inventory 72,872 complete. Do not treat search coverage as proof or certify global absence from partial retrieval.

## Verification
Targeted lake --old builds pass. Final direct lake env lean on all five new leaves and existing CHMDBirmanSchwingerBound.lean: six exit 0, all logs empty. API probe passed against actual toolchain. #print axioms on all 83 new declarations + existing counting theorem: 84/84 exactly [propext, Classical.choice, Quot.sound]. Root imports each new leaf once. No full/umbrella builds or heartbeat changes. git diff --check passed.
formal_tools.py index regenerated indexes. Final lint --check-generated exits 1 solely for concurrent unrelated unrootwired GaloisForLFunctions.RHTower.PaperThetaBoundedForcing; no owned proof/import/stale-generated finding remains. Do not touch others' files to clear this. All 23 owned temporary search results, API/axiom probes, and build/audit logs were removed using apply_patch. All owned tool sessions are terminal; no owned Lean/build process remains.

SHA256:
CHMDMassFourierReadout a2a011b0f503d95e4646c6e469cb08f1364ae1e506af05b73cff02f4b913a115
CHMDMassMixedExplicitFormula 15e4d5615f2fa996ece6f545f146d4a94eeef54652ba9319019e91bd053bec7b
CHMDMassSpectralAdmission e94c96e977c7c95f4d68536c35bf2fc8e0b3097caccd0db181c4497f5cc3fa5f
CHMDMassSamplingCompleteness 88aa3830872e586f4cb6ba407097c73cf4fda53b9b99fbb1b7fc1505084e3650
CHMDMassPolarCompletion 6cd16283dbd89c82f89d150411a288809171f05f4c81f52f6c649c1271c16626

## Lean implementation details
real_inner_comm x y states inner y x = inner x y: argument order matters in rw.
For LinearPMap subtype images, use explicit change to clear CLM/linear map coercion transparency before rw arithmeticGenerator_resolvent or range witnesses.
For uniqueness of r=w-P(w), rw [w=P(w)+r] rewrites w inside P too and is wrong tactic shape. Use calc r=(P(w)+r)-P(w) := by abel; then congrArg (fun u => u-P(w)) hr.symm.
Source equality after mixed-functional rewriting may need rfl (lambda id/sourceMap reductions).
Serena ignores Lean source paths: rg + apply_patch fallback established. rm -f rejected by shell guard; explicit apply_patch Delete File works for owned scratch.

## Remaining frontier
Exclude actual primitive eigenvectors above 1/2. The new domain/completeness theorem does not do this. Before extending to finite nonzero spectral support/cardinal packets, search the current corpus again and reuse existing exact-divisor, full-nullspace, Birman-Schwinger and parity results. No numerical experiments/web/old research Markdown per active goal attachment.
