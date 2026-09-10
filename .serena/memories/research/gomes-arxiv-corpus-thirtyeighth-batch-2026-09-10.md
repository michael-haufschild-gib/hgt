# Gomes corpus experiment — batch38 verified, GOAL ACTIVE

Previous goal turn changed authoritative Lean state; this turn also made verified progress. Batch completion is not completion of the user's unbounded goal. Continue without narrowing the goal or marking it complete at a checkpoint.

## Outcome and evidence

39 new theorems,9 defs/abbrevs,6 modules. Cumulative:1723 theorems/199 modules (prior1684/193).
All48 declarations closed; only propext, Classical.choice, Quot.sound. No added axioms.
All6 individually built after one successful combined scratch batch. All6 uniquely wired into formal/GaloisForLFunctions/HTGeometry.lean. Formal lint PASS. All48 indexed and names unique.142 prior source hashes unchanged. No own Lean/Lake processes left.
No new source warnings in the successful FullBatch. Old LabeledBoundarySimplex:94 and batch37 GomesPolynomialConnectionClassification:99 style warnings may replay during imports.

Evidence directory /tmp/hgt-gomes/thirtyeighth:
progress.json, totals.json, build-status.json, scratch-batch-audit.json, FullBatch.lean/log, axiom-audit.json, declaration-uniqueness.json, corpus-search-audit.json, prior-source-audit.json, process-audit.json, final-command-status.json. Individual build logs all passed, axiom audit exit0.
No live handles remain. Final build/audit script session43316 terminal exit0.

User constraints: search corpus first; work directly in Lean, no cards; closed unconditional classifications, no new axioms/gaps/computational tactics; build missing infrastructure; one foreground Lean per agent; lake env lean scratch files, then individual lake build MODULE audits; no full/umbrella builds; wire new modules; clean own processes. No subagents used. update_plan unavailable; progress.json tracks steps.

All new modules under formal/GaloisForLFunctions/HTGeometry/, namespace GaloisForLFunctions.HTGeometry.

## New modules and usable exact APIs

### GomesPolynomialMultiplicationCommutant (7 theorems,2 defs/abbrevs)

gomesPolynomialMultiplicationMap (P:Real[X]) : Real[X]→ₗ[Real]Real[X] := LinearMap.mul Real Real[X] P.
GomesPolynomialXCompatibleMap := {E:End Real Real[X] // E.comp(M_X)=M_X.comp E}.
gomesPolynomialXCompatibleMap_apply_X E P: E.val(X*P)=X*E.val P.
gomesPolynomialXCompatibleMap_apply E P: E.val P=E.val1*P.
gomesPolynomialMultiplication_X_commutant_iff E:
 E.comp M_X=M_X.comp E iff E=M_(E1).
gomesPolynomialMultiplicationMap_constant c: M_(C c)=c•LinearMap.id.
gomesPolynomialMultiplicationMap_injective.
gomesPolynomialMultiplicationMap_commute P Q: M_P.comp M_Q=M_Q.comp M_P.
gomesPolynomialMultiplication_all_compatible_iff E:
 commuting with every M_P iff commuting with M_X.
Proof: polynomial induction; constants from scalar linearity, monomial successor from commuting with X.

### GomesPolynomialMultiplierIntertwining (5 theorems)

gomesPolynomialMultiplier_intertwining_equation A B P:
 M_P.comp T_A=T_B.comp M_P iff Pprime=(B-A)*P.
gomesPolynomialMultiplier_intertwines_iff A B P:
 same iff P=0 OR (A=B AND Pprime=0).
gomesPolynomialMultiplier_intertwines_constant_iff:
 same iff P=0 OR (A=B AND exists c,P=C c).
gomesPolynomialConnection_coordinate_compatible_maps_iff A B E:
 (E commutes with M_X AND E.comp T_A=T_B.comp E)
 iff E=0 OR (A=B AND exists c,E=c•id).
gomesPolynomialConnection_nonzero_coordinate_map_coefficient:
 any bundled nonzero X-compatible intertwiner forces A=B.
Core proof: nonzero multiplier solving T_(B-A)P=0 forces B-A=0 via previous exact injectivity classification.

### GomesPolynomialStructuredConjugacy (6 theorems,1 abbrev)

GomesPolynomialStructuredIntertwiner A B :=
 {E:GomesPolynomialConnectionIntertwiner A B //
  E.val.toLinearMap.comp M_X=M_X.comp E.val.toLinearMap}.
gomesPolynomialConnectionIntertwiner_linearMap_ne_zero A B E.
gomesPolynomialStructuredIntertwiner_scalar_classification A B E:
 A=B AND exists c,c≠0 AND E.val.val.toLinearMap=c•id.
gomesPolynomialConnection_structured_intertwiner_iff A B:
 Nonempty(StructuredIntertwiner A B) iff A=B.
gomesPolynomialStructuredIntertwiner_unital_iff_identity A B E:
 E.val.val1=1 iff E.val.val=LinearEquiv.refl Real Real[X].
gomesPolynomialConnection_abstract_structured_gap_iff A B:
 (Nonempty ordinary intertwiner AND NOT Nonempty structured intertwiner)
 iff A≠B AND Aprime≠0 AND Bprime≠0 AND degrees equal.
gomesPolynomialConnection_shift_structure_boundary A r (A nonconstant,r bundled nonzero):
 ordinary intertwiner A→A+C r exists AND structured one does not.

### GomesDilatonStructuredReconstruction (6 theorems)

gomesDilatonPolynomialConnection_structured_derivative_iff H K:
 structured intertwiner of half-derivative coefficients iff Hprime=Kprime.
_structured_supercharge_iff H K:
 same iff dilatonSuperchargeCLM H=dilatonSuperchargeCLM K.
_structured_profile_fibers H K:
 same iff exists c,H=K+C c.
gomesDilatonConnectionPolynomial_linear_perturbation H r:
 connectionPolynomial(H+C(2*r)*X)=connectionPolynomial H+C r.
gomesDilatonPolynomialConnection_linear_perturbation_boundary H r:
 for bundled non-affine H and nonzero r, those profiles' polynomial connections are abstractly conjugate but not structurally conjugate.
gomesDilatonSupercharge_linear_perturbation_distinct H r:
 actual Schwartz supercharges differ.

### GomesHermitePolynomialOrbit (9 theorems,6 defs)

gomesHermiteConnectionScale := -(1/(2*pi)).
_scale_ne_zero and _scale_negative.
gomesHermiteConnectionCoefficient : GomesNonconstantPolynomialCoefficient :=
 C(2*(2*pi))*X; _degree=1.
gomesHermiteStepLinearMap := scale • T_coefficient.
gomesHermiteStepLinearMap_apply P = existing hermiteStep P.
The existing hermiteStep is 2*X*P-C(1/(2*pi))*Pprime.
gomesHermitePolynomialSequence : Polynomial.Sequence Real from existing hermitePoly_degree.
gomesHermitePolynomialBasis : Basis Nat Real Real[X], using existing hermitePoly_leadingCoeff=2^n.
_Basis_apply n = existing hermitePoly n.
gomesHermiteStepLinearMap_basis_shift n: HStep(basis n)=basis(n+1).
gomesPolynomialConnectionHermiteTransport A : Real[X]≃ₗ[Real]Real[X], transports orbit basisA to Hermite basis.
_transport_basis A n.
_transport_intertwines_iff A: that canonical transport intertwines T_A with HStep iff degA=1.
gomesPolynomialConnection_Hermite_normal_form A, A:{A:Real[X]//degreeA=1}:
 exists E real-linear equivalence,E.comp T_A=HStep.comp E.
No new proof of Hermite degree/spanning was introduced; existing corpus results reused.

### GomesHermiteCoordinateRigidity (6 theorems)

gomesHermiteStep_commutes_connection_iff E:
 E commutes with HStep iff E commutes with T_(4*pi*X).
gomesHermiteStep_coordinate_joint_commutant E:
 (E commutes with M_X and HStep) iff exists c,E=c•id.
gomesPolynomialFirstOrder_coordinate_commutator A P:
 T_A(X*P)-X*T_A(P)=P.
gomesHermiteStep_coordinate_commutator P:
 HStep(X*P)-X*HStep(P)=scale•P.
gomesPolynomialConnection_no_coordinate_Hermite_intertwiner A:
 no real-linear equivalence simultaneously preserves M_X and intertwines T_A with HStep, for ANY A.
gomesPolynomialConnection_Hermite_normal_form_loses_coordinate A (degree1):
 exists a Hermite normal-form equivalence and it fails coordinate compatibility.
Proof: preserving both commutators would imply scale•E1=E1; E1 nonzero forces scale=1, contradicting scale<0.

## Next priority: full commutant matrix algebra

Conjecture to formalize, not yet proved:
For nonconstant A with degree m, full real-linear commutant of T_A is isomorphic as a real algebra to Matrix(Fin m)(Fin m)Real[X]. Current structured commutant is only real scalars. Full commutant allows polynomial evolution and mixing the m independent orbit chains.

Proposed route:
1. View Real[X] as polynomial module Module.AEval' T_A.
2. Use existing orbit basis n=T_A^(n/m)(X^(n%m)); reindex via (n%m,n/m).
3. Transport to standard real basis of Fin m→Real[X]. Prove T_A becomes componentwise multiplication by X.
4. LinearEquiv.ofAEval promotes transport to a polynomial-linear equivalence.
5. Identify T_A-commuting real endomorphisms with polynomial-linear endomorphisms of AEval' T_A.
6. Finite free module endomorphisms are matrices over Real[X]; compose algebra equivalences.
Build missing reindexing/module/centralizer infrastructure, not just degree1 special case.

Mathlib source fully read: Algebra/Polynomial/Module/AEval.lean1-215.
- Module.AEval R M a type synonym with polynomial action via aeval a.
- Module.AEval.of, .C_smul, .X_smul_of, .of_symm_X_smul.
- LinearMap.ofAEval a f hf and LinearEquiv.ofAEval a f hf: hf is f(a•m)=X•f(m).
- Module.AEval' phi, .of phi, .X_smul_of, .of_symm_X_smul.
These APIs not yet checked in scratch for next work.
Located (not read): Mathlib LinearAlgebra/Matrix/ToLin.lean, ToLinearEquiv.lean. Basis.pi, Pi.basisFun and matrix algebra-equivalence APIs still need discovery/verification.

Corpus search next-polynomial-module-search.json:2 hits, both read:
- SourceCoboundaryModule.lean1-145: reusable generic smul_aEval_of, aEval_of_symm_smul, aeval_monomial_succ_apply. Uses actual AEval' derivation modules. Do not recreate these helpers.
- SpecializationFaithfulnessBoundary.exists_nonzero_rankOneScalarEndomorphism_specializes_to_zero45-50: X-C c witness shows point specialization loses scalar endomorphisms; distinct from commutant classification.
next-cyclic-centralizer-search.json: first20/110 mostly ABHN cyclic Galois centralizers; not an exhaustive absence check.

## Further concrete transfer candidate

Unify S_(a,A)(P)=a•Pprime-A*P for all real a, including0.
Conjecture: nonconstant A classes depend only on degree for all a, even pure multiplication a=0. Constant-A classes retain the constant value and whether a=0. Coordinate-compatible nonzero intertwiners retain a by the commutator, and recover A when a≠0. Not proved yet.

Actual RHTower/HeatOperatorPolynomial.lean1-46 read:
namespace RHTower;
heatShiftPoly t0=1;
successor X*previous-C(1/(2*t))*previous.derivative.
This is a direct scaled-operator application, including t=0. next-scaled-connection-search and next-differential-conjugacy-search returned0.

Important scope: these are concrete scalar reconstruction analogues of2607.24901v1 section4, with joint coordinate/connection structure. Not full gauge-category equivalence; do not revive withdrawn2509.25276v1-v6 claim. The actual Schwartz statement proved is equality of supercharges iff structured polynomial conjugacy, not arbitrary Schwartz/Hilbert conjugacy.

## API and proof lessons

Polynomial.basisMonomials_apply is NOT a name. Correct: Polynomial.coe_basisMonomials.
Polynomial.induction_on has C/add/monomial-successor cases, not general mul_X case.
LinearMap.mul Real Real[X] P is the bilinear multiplication specialization; mul' is tensor multiplication.
In the multiplier intertwining equation, linear_combination -he (not he) has the needed sign.
When a linear equivalence's toLinearMap coercion blocks simpa, first change E.val(1:Real[X])=0 at he.
Nonzero real scalar cancellation can use (LinearEquiv.smulOfNeZero Real Real[X] c hc).injective; generic smul_left_cancel expects a group and is not directly applicable to Real including0.
