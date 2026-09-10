# Gomes experiment — batch 37 verified; GOAL ACTIVE

This is a progress checkpoint in the user's unbounded experimental corpus-transfer goal, not completion of the goal. Continue finding and formalizing applications. Do not call update_goal complete merely because a batch is finished.

User constraints persist: use corpus research tool before new topics; read/work directly with Lean, not cards; unconditional closed mathematical classifications, no new axioms or proof gaps; no numerical proof computations; build missing infrastructure; one foreground Lean process per agent, scratch with lake env lean FILE, only individual lake build MODULE for final audit, no full/umbrella build, wire new modules, clean own processes. No subagents used.

## Verified outcome

40 new theorems, 8 definitions, 7 modules. Cumulative experiment count: 1684 theorems in 193 modules (prior1644/186).
All48 declarations audited with only propext, Classical.choice, Quot.sound. No added axioms. All7 individual builds passed; formal lint passed. All48 declarations indexed and names unique across corpus. All7 source hashes match successful combined scratch runs.135 prior source hashes unchanged. No own Lean/Lake processes remained. All7 imports appended uniquely to formal/GaloisForLFunctions/HTGeometry.lean.
Evidence: /tmp/hgt-gomes/thirtyseventh/, especially progress.json, totals.json, build-status.json, scratch-batch-audit.json, scratch-source-hash-audit.json, axiom-audit.json, declaration-uniqueness.json, corpus-search-audit.json, prior-source-audit.json, process-audit.json, final-command-status.json.
One cosmetic new warning: GomesPolynomialConnectionClassification.lean:99:8 unnecessarySimpa. Existing LabeledBoundarySimplex:94 warning replayed. Neither is a proof failure.

All following modules in formal/GaloisForLFunctions/HTGeometry/; namespace GaloisForLFunctions.HTGeometry.

## New exact infrastructure

GomesPolynomialConnectionIterates (5 theorems):
- gomesNonconstantPolynomialCoefficient_ne_zero A.
- gomesPolynomialFirstOrder_iterate_zero A k.
- gomesPolynomialFirstOrder_nonconstant_iterate_injective A k.
- gomesPolynomialFirstOrder_nonconstant_iterate_ne_zero A Q k, Q:{Q:Real[X]//Q≠0}.
- gomesPolynomialFirstOrder_nonconstant_iterate_degree A Q k:
  natDegree(T_A^[k] Q.val)=k*A.val.natDegree+Q.val.natDegree.

GomesPolynomialConnectionOrbitBasis (6 theorems,3 defs):
- orbit polynomial n = T_A^[n/m](X^(n%m)), m=natDegreeA.
- _ne_zero, _natDegree=n, _degree=n.
- gomesPolynomialConnectionOrbitSequence A : Polynomial.Sequence Real.
- gomesPolynomialConnectionOrbitBasis A : Module.Basis Nat Real Real[X].
- _Basis_apply identifies basis with orbit polynomial.
- _OrbitPolynomial_shift and _OrbitBasis_shift: T_A sends vector n to n+m.
The degree-indexed sequence and unit leading coefficients invoke Mathlib Polynomial.Sequence.basis.

GomesPolynomialConnectionConjugacy (5 theorems,1 def):
- gomesPolynomialConnectionOrbitTransport A B : Real[X] ≃ₗ[Real] Real[X] via Basis.equiv.
- _basis maps the matching natural index.
- _intertwines_iff: this particular transport intertwines iff coefficient degrees agree.
- gomesPolynomialConnection_nonconstant_intertwiner_iff A B:
  Nonempty(Intertwiner A.val B.val) iff natDegreeA=natDegreeB.
- gomesPolynomialConnection_monomial_normal_form A:
  Nonempty(Intertwiner A.val (X^natDegreeA)).
- transport_refl.

GomesPolynomialConnectionConstantRigidity (5 theorems,3 defs):
- gomesPolynomialConnectionIntertwinerRefl A.
- gomesPolynomialConnectionIntertwinerSymm A B E.
- gomesPolynomialConnectionIntertwinerTrans A B D E F.
- _Intertwiner_constant_source a B E: B=C a.
- _constant_source_intertwiner_iff a B: Nonempty(Intertwiner(C a)B) iff B=C a.
- _constant_target_intertwiner_iff A b: Nonempty(Intertwiner A(C b)) iff A=C b.
- _constant_intertwiner_iff a b iff a=b.
- _intertwiner_symm_iff A B.
Proof transports nonzero eigenvector1, then uses exact polynomial eigenvalue classification.

GomesPolynomialConnectionClassification (7 theorems):
- gomesPolynomialConnection_intertwiner_iff A B:
  Nonempty(Intertwiner A B) iff A=B OR (A.derivative≠0 AND B.derivative≠0 AND natDegreeA=natDegreeB).
- _intertwiner_cases gives disjoint union: identical constants OR same-degree nonconstant coefficients.
- _nonconstant_cokernel_complete: iff cokernel finranks equal.
- _nonconstant_index_complete: iff exact connection indices equal.
- _derivative_intertwiner_iff A: Nonempty(Intertwiner0 A) iff A=0.
- _eigenvalues_degree_complete A B: Nonempty intertwiner iff polynomial eigenvalue sets equal AND degrees equal.
- _eigenvalues_cokernel_complete A B: same with cokernel finrank instead of degree.

GomesPolynomialConnectionShiftConjugacy (5 theorems,1 def):
- gomesPolynomialConnectionShiftedCoefficient A r bundles A+C r as nonconstant.
- _nonconstant_shift_conjugate A r.
- _shift_conjugate_iff A r: Nonempty(Intertwiner A(A+C r)) iff r=0 OR A.derivative≠0.
- _shift_coefficients_injective A.
- _shift_family_conjugate A r s.
- _nonconstant_reconstruction_failure A r, r:{r:Real//r≠0}: shifted coefficient differs AND operators conjugate.

GomesDilatonPolynomialConjugacy (7 theorems):
- gomesDilatonConnectionPolynomial_natDegree H = natDegree(H.derivative).
- _degree_from_profile H = natDegreeH-1.
- gomesDilatonPolynomialConnection_intertwiner_iff H K:
  Hprime=Kprime OR (Hsecond≠0 AND Ksecond≠0 AND degrees of first derivatives equal).
- gomesDilatonNonaffineProfile_degree_pos H.
- _nonaffine_intertwiner_iff H K, non-affine bundled profiles: iff natDegreeH=natDegreeK.
- _cokernel_finrank H = natDegreeH-1.
- _affine_intertwiner_iff a b c d: profiles C a*X+C b and C c*X+C d have conjugate polynomial connections iff a=c.
This is real-linear polynomial endomorphism conjugacy, not an assertion about actual Schwartz/Hilbert conjugacy.

## Next conjecture: preserving polynomial multiplication restores rigidity

The arbitrary linear classification forgets all nonconstant coefficient data except degree. Conjecture: require an intertwiner to commute with multiplication by X; then A=B. Stronger plausible result for nonzero (not necessarily invertible) real-linear maps:
1. If E commutes with X multiplication, polynomial induction proves E(Q)=Q*E(1).
2. Put P=E1. Intertwining at1 gives Pprime=(B-A)*P, i.e. T_(B-A) P=0.
3. Nonzero E forces P≠0. Existing gomesPolynomialFirstOrderOperator_injective_iff forces B-A=0.
4. Then Pprime=0, so E is multiplication by a nonzero constant.
This is a paper derivation/conjecture, not yet formalized.
Further conjecture: full commutant of a degree-m connection is Matrix(Fin m)(Fin m) Real[X], using m orbit chains. Build polynomial-action/module and reindexing infrastructure if pursued.

## Searches and additional corpus sites

Current-topic lexical searches orbit basis/conjugacy/dilaton degree found no prior result; eigenvalues degree found only previously known monomial-family point spectrum. All new declaration names subsequently unique/indexed.

Future searches were fully paginated and inspected:
- next-polynomial-commute-search-all.json:83 hits.
- next-creation-search-all.json:41 hits.
- initial narrow multiplication/commutant/oscillator searches:0 hits.

GaussianSchwartz.lean rg excerpts (not complete source read):
hermiteStep at265 over Real polynomials =2*X*p-C(1/(2*pi))*p.derivative.
hermiteStep_apply at291 realizes the actual creation action on polynomial-times-Gaussian profiles.
polyGaussSchwartzReal224, polyGaussSchwartz239, actual Gaussian derivative identity53.
Potential separate transfer: normalize hermiteStep as a nonzero scalar multiple of a degree-one connection and reuse orbit basis.

CPVTwoModeFock.lean1-115 read: domain MvPolynomial Bool Complex; pairCreate is multiplication by Xfalse*Xtrue, pairCartan/pairCharge proven commutators. Requires a multivariable/complex extension before reusing current Real[X] results.
PrimeWeylSamplingIdealizerAnalytic.ccr_scalar_eq_zero340-347 read: commuting polynomial multipliers cannot give a nonzero scalar CCR on a nonempty sampling domain; not the desired intertwiner classification.

Paper version status refreshed:2509.25276v7 withdrew v1-v6 equivalence claim.2607.24901v1 section4 reconstructing generating presentations motivates this scalar analogue. HTML read through4.3, actual section label verified. No claim that our scalar degree theorem is a theorem about full gauge categories.
