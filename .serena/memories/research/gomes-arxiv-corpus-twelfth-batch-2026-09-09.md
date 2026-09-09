# Gomes arXiv corpus experiment — twelfth verified batch

Active unbounded goal remains open: mechanically apply arXiv:2607.24901, 2509.25276 (latest v7; do not resurrect withdrawn older equivalence), 2404.10461 throughout Lean corpus, prove exact closed results, explain discoveries. This batch spans an intentionally interrupted turn and its continuation; authoritative source/log checks confirmed progress, no work lost.

## Constraints and verified state
Use scripts/formal_tools.py research for corpus reuse. Only Lean/source/tool metadata; no cards/docs reads. No supplied mathematical proof premises: arbitrary data and complete iff classifications used; internal assumptions introduced from RHS of iff are discharged. No added axioms, sorry/admit/opaque/unsafe or computational tactics. Symbolic algebra/induction only. One foreground Lean invocation: scratch lake env lean /tmp/file, final lake build Exact.Module, never full/umbrella builds. Wire own modules, no commits/push/subagents. Shared tree has other active work; never kill unrelated processes or wire their unfinished modules. Serena ignored Lean paths, so prior fallback to scratch-verified bounded edits applies.

48 new theorems / 5 definitions / 6 modules, all built and wired. Cumulative 651 theorems / 76 modules (previous 603/70). All 53 new declarations axiom-audited: only propext, Classical.choice, Quot.sound. Global scripts/formal_tools.py lint PASSED this batch; old unrelated Fokas wiring errors disappeared through other work. Index refreshed. No older own modules modified. Six new and 19 prior eleventh-batch audited source hashes revalidated unchanged after audit. No owned Lean processes remain. Goal not marked complete.

Artifacts /tmp/hgt-gomes/twelfth: progress.json, modules.json, totals.json, counts.json, build-status.json, AxiomAudit.lean, axioms.log, axiom-audit.json, lint.log, index.log, per-module scratch and build logs. Audit parser strips nested comments and strings. A raw forbidden-token scan falsely matched English 'states admit unconditional...' in a docstring; corrected scan used parser and passed.

## Modules / counts (namespace GaloisForLFunctions.HTGeometry)
GomesFockScalarObservation: 6 thms, 0 defs.
GomesFockCoherentReference: 6 thms, 2 defs.
GomesFockExponentialFrame: 11 thms, 1 def.
GomesDysonUnitaryCovariance: 5 thms, 1 def.
GomesFockUnitaryObservation: 8 thms, 1 def.
GomesFockQubitGauge: 12 thms, 0 defs.

## Scalar ambiguity and positive coherent survivor
First helpers use A : Option(Fin k) → Matrix(Fin d)(Fin d) Complex, arbitrary (not assumed Hermitian), x : Fin d→Complex, including empty internal carrier.
gomesFock_zeroVector_moment: all zero-vector moments vanish.
gomesFockVector_mass_zero_iff: initial moment=0 iff x=0.
gomesFockScalar_moments_eq_iff A x c e: all moments of c•x and e•x equal iff normSq c=normSq e OR x=0. Reuses existing freeFockVectorMoment_smul; not duplicated.
gomesFockScalar_record_eq_iff_mass_eq: on a scalar orbit, the zeroth moment already has exactly the scalar information of the entire sequence.
gomesFockScalar_moment_stabilizer: all moments unchanged by c iff normSq c=1 OR x=0.
gomesFockScalar_global_stabilizer: observing all vectors on Fin(d+1) reconstructs exactly normSq c=1.

gomesFockReferenceContrast A x c a = moment((c+a)•x)0 - moment((c-a)•x)0.
_formula =4*(c.re*a.re+c.im*a.im)*moment(A,x,0); _one and _I isolate real/imaginary coordinates.
gomesFockCoherentMenu A x a b c is pair of contrasts.
_standard_reconstruction: menu with references 1,I equal for c,e iff c=e OR x=0.
_injective_iff: Function.Injective(menu A x a b) iff x≠0 AND a.re*b.im-a.im*b.re≠0. Necessity uses invisible perpendicular scalar a*I or b*I; sufficiency symbolic elimination. This is the sharp positive survivor of phase blindness, not just a no-go.
gomesFockObservation_coherent_reconstruction applies 1,I to actual completed-Fock affine vector gomesFockObservationVector y=Fin.cons 1 y, giving exact c=e with no state premise.

## Frame/tensor observational hierarchy
GomesFockExponentialFrame imports previous GomesMomentMassTensorCovariance.
gomesFockExp_normSq w = exp(2*w.re).
gomesFockExponentialModel B y w = gomesMassScaledModel (gomesFockObservationModel B y)(2*w.re).
_moments identifies exact actual completed-Fock moments of exp(w)•observationVector y.
gomesFockExponential_frame, _quotient invariant under all w.
_gram, _flux scale by exp(-(2*w.re)).
_source_reconstruction: equality iff real parts w.re=t.re (amplitude only).
gomesMomentObservationGram_ne_zero M n z: nonzero for EVERY depth and point, including rank-one depth0, from positive unit wave energy.
_gram_reconstruction: one full Gram equal iff w.re=t.re.
_flux_reconstruction: one flux equal iff w.re=t.re OR z.im=0.
_coherent_reconstruction: coherent menu equal iff Complex.exp w=Complex.exp t; recovers scalar itself, not a nonperiodic logarithm.

## Arbitrary matrix frame changes and exact unitary reconstruction
GomesDysonUnitaryCovariance defines gomesFockConjugate U X=U*X*Uᴴ for arbitrary Fin d square matrices.
_adjoint, _sum unconditional.
_mul_defect: conj(U,X)*conj(U,Y)=conj(U, X*(Uᴴ*U)*Y).
_covariance_defect: matrixSemicircleCovariance (conj U ∘ A)(conj U X)=conj U (matrixSemicircleCovariance A ((Uᴴ*U)*X*(Uᴴ*U))). Original covariance is sum A_k X A_kᴴ (not just A_k X A_k).
gomesDyson_unitary_conjugacy_iff U: (forall A,n, Dyson coeff of conjugated A=conj U coeff A) iff Uᴴ*U=1. Initial identity coefficient proves necessity; strong induction using exact Gram defect proves sufficiency. No mathematical proof arguments exported.

GomesFockUnitaryObservation uses U : Matrix(Fin(d+1))(Fin(d+1)) Complex and B : Fin k→same matrices.
gomesFockConjugatedData U B i=conj U(B i).
gomesFock_completion_covariance_iff U: (forall B,i, completed(conjugatedData U B)i=conj U(completed B i)) iff Uᴴ*U=1. Identity 'none' generator fixes internal metric; 'some' generators use adjoint/additivity.
gomesCompletedFock_moment_matrix_formula B n: actual freeFockMatrixMomentCoefficient = if 2|n then matrixDysonFormalCoeff(completed B)(n/2) else0.
gomesFock_matrix_conjugacy_iff U: full actual matrix-moment covariance for every B,n iff Uᴴ*U=1.
gomesFock_quadratic_transport U M x: star(Ux) dot M(Ux)=star x dot (Uᴴ*M*U)x.
gomesFock_quadratic_conjugate_defect U M x: transporting M and x inserts (UᴴU)*M*(UᴴU).
gomesFockVector_mass_quadratic A x: complex cast initial mass = star x dot x.
gomesFockVector_mass_isometry_iff A U: preservation of all initial vector masses iff UᴴU=1. Reuses matrix_eq_of_quadraticForm_eq.
gomesFock_vector_gauge_iff U: forall B,x,n, moment(completed conjugated B,Ux,n)=moment(completed B,x,n) iff UᴴU=1. Thus actual scalar observations characterize the full unitary internal gauge.

## Four concrete source gate applications
GomesFockQubitGauge imports existing QuantumAlg.Core.Components.Gates. Gates/root namespace QuantumAlg: phaseGateOp, phaseGateOnZeroOp, rotZOp, rotYOp; all have _mem_unitaryGroup theta. For each prefix gomesFockPhase, gomesFockZeroPhase, gomesFockRotZ, gomesFockRotY:
_matrix_moments transports full matrix moments by actual gate conjugation;
_vector_moments preserves every actual scalar Fock moment under joint generator/state transport;
_moment_frame preserves the complete existing real gomesMomentFrame at every level/spectral point, including zero observing vectors.
B : Fin k→Mat2 arbitrary, theta real, x : Fin2→Complex arbitrary. Uses Matrix.mem_unitaryGroup_iff' to derive closed UᴴU=1 internally. QuantumAlg HilbertOperator(Qubits1) is definitionally Fin2 matrix here.

## Source/API evidence read
FreeFockMatrixSemicircle.lean 590–622: freeFockPower_vacuumCoefficient A hA n i j = if2|n then DysonCoeff A(n/2)i j else0; even/odd versions exist.
MatrixSemicircleDysonFormalBranch.lean 56–100: matrixDysonFormalCoeff A0=1, successor sum p:Fin(n+1), Cov A(coeff p)*coeff(n-p).
FreeFockMatrixValuedSpectralLaw.lean 1312–1391: freeFockMatrixMomentCoefficient definition; star_dotProduct_freeFockMatrixMomentCoefficient_mulVec gives actual vector-moment quadratic for Hermitian A. Existing full complex polarization already exists; do not duplicate.
Mathlib Matrix.star_mulVec: star(M*ᵥv)=star v ᵥ* Mᴴ. Matrix.dotProduct_mulVec: v dot A*w=(vᵥ*A) dotw. Matrix.mulVec_mulVec COMBINES nested applications M*(N*v)=(M*N)*v; reverse expands.
Use GLOBAL mul_eq_one_comm (Matrix alias deprecated). Generic API scratches use explicit universe levels when bare @ leaves unresolved levels. Matrix.mul_eq_one_comm alias accepts fewer universes than old expected; corrected UnitaryApi to @mul_eq_one_comm.{0}, @Matrix.star_mulVec.{0,0,0}, @Matrix.dotProduct_mulVec.{0,0,0}.
Complex.norm_exp and normSq_eq_norm_sq verified in /tmp/.../ExponentialApi.lean; identity via exp_add and pow_two. Coherent reference proof must avoid unrestricted simp before ring: simp may convert a product=0 into disjunction. Use explicit simp only for complex coordinate expansion. For mass-isometry necessity, simp at ht before chaining equality removes 1*vector. For B=0 vector gauge necessity, simp only [freeFockVectorMoment_zero] bypasses irrelevant generator presentation.

## Next experiment already searched/read (no code started)
Corpus research 'Fock spectral gauge' and 'Fock spectral unitary' returned no declarations. Extend exact gauge covariance from moments to full spectral measures, atom weights, analytic moment-generating matrices.
FreeFockMatrixValuedSpectralLaw.lean 374–408 READ: freeFockVectorSpectralMeasure A hA hker x (Measure Real), _isFinite, _hasMoments, _carried on [-R_A,R_A], R_A=freeFockMatrixSpectralRadius A. Completed generators discharge hA/hker. Existing scalar spectral-measure homogeneity at 489–556 already read before, do not duplicate.
CompactDeterminacy.lean 15–43 READ: root HTGeometry.measure_eq_of_moments_eq_of_carried uses two finite measures, common Icc m M support, equal moments to sequence s, and all moment integrability. For two presentations use max of R_A,R_A' to widen compact supports; radius bound need not itself be gauge-invariant. This supports building a data-only completed-Fock spectral measure wrapper and deriving actual gauge equality (including x=0) from gomesFock_vector_gauge_iff.

## Process discipline incident
During resumed work one scratch check was accidentally launched before its dependency build had fully exited; it immediately failed on missing GomesDysonUnitaryCovariance.olean. Reported to user, confirmed scratch terminal, waited for original build terminal, reran successfully. Never launch next Lean call in same functions.exec after a wait that still returns session_id: inspect that result FIRST. Every final own process is terminal and ps check found none.
