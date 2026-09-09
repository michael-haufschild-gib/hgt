# Gomes arXiv mechanical corpus experiment — batch32

GOAL ACTIVE. Batch checkpoint is progress, never goal completion. User wants as many closed, mechanically connected results from arXiv2607.24901/2509.25276/2404.10461 as possible. Do not stop over token budget. Only Lean + formal_tools research; no cards/docs. No computations, no holes/hypothesis-driven claims/new axioms. One foreground Lean per agent, use lake env lean scratch; exact lake build module for needed oleans/final audit; append finished imports, never full/umbrella builds. No subagents authorized. No commit/push. Preserve others' changes/processes. Session init/manual/skills done earlier; don't repeat.

## Verified checkpoint
Artifacts /tmp/hgt-gomes/thirtysecond/. 43 new theorems,4defs,6modules. Cumulative1480theorems/162modules (prior1437/156). Six scratch checks clean, all6exact foreground builds terminalexit0,47declarations axiomaudited only propext/Classical.choice/Quot.sound,47indexed,formal lintPASS,105prior source hashes unchanged,NOOWN Lean/Lake processes at completion. All6imports appended in formal/GaloisForLFunctions/HTGeometry.lean. Source files byte-identical to checked scratch. All checks in build-status.json,axiom-audit.json,corpus-search-audit.json,prior-source-audit.json,process-audit.json,totals.json,progress.json. Last process AxiomAudit session11885 terminalexit0. No processes remain.

## Main mathematical insight
Polynomial divisibility P|Pprime forces Pprime=0 (mathlib Polynomial.dvd_derivative_iff). For F(U)=Uprime+U², equality F(U)=F(V) makes U-V divide its derivative, so derivative and square terms cannot compensate. Exact fibers: U=V or opposite constants. Passing through U=Hprime/2 gives full classification of actual Schwartz Hamiltonian equality: H=K+C c, or affine H,K with opposite slopes. An origin slope recovers the first-order connection; origin value then recovers H. Alternatively Hamiltonians for H and H+X together recover first-order connection; origin value makes this pair injective on ALL real polynomials. This is an experimental scalar analogue of reconstruction/tensor-composition ideas, not a literal gauge-theory equivalence theorem.

## Exact APIs, namespace GaloisForLFunctions.HTGeometry
All paths formal/GaloisForLFunctions/HTGeometry/<module>.lean.

1. GomesPolynomialRiccatiFibers (7theorems,1def), imports GomesFinitePolynomialHamiltonianReconstruction:
- gomesPolynomialDerivative_multiple_iff A B : Bprime=A*B ↔ B=0 ∨(A=0∧Bprime=0).
- def gomesPolynomialRiccati U:=Uprime+U².
- gomesPolynomialRiccati_eq_iff_parts U V : F U=F V ↔ Uprime=Vprime ∧ U²=V².
- _eq_iff U V : F U=F V ↔ U=V ∨(U=-V∧Uprime=0).
- _eq_iff_constants U V : F U=F V ↔ U=V ∨∃c,U=C c∧V=C(-c).
- _constant_iff U k : F U=C k ↔∃c,U=C c∧c²=k.
- _square_fiber U r : F U=C(r²) ↔U=C r∨U=C(-r).
- _constant_image_iff k : (∃U,F U=C k)↔0≤k.

2. GomesDilatonPolynomialPotential (8theorems,2defs), imports above:
- def gomesDilatonConnectionPolynomial H:=C(1/2)*Hprime.
- def gomesDilatonPotentialPolynomial H:=F(connectionPolynomial H).
- gomesDilatonConnectionPolynomial_eq_iff H K : connectionPolyEq↔Hprime=Kprime.
- _neg H : connectionPoly(-H)=-connectionPolyH.
- _derivative_zero_iff H : connectionPolyHprime=0↔Hsecond=0.
- gomesDilatonPotentialPolynomial_eval H x : eval=actual dilatonPotential H x.
- gomesDilatonPotential_polynomial_eq_iff H K : actual potential functions equal↔potential polynomials equal.
- gomesDilatonPotential_derivative_fibers H K : potentialEq ↔Hprime=Kprime ∨(Hprime=-Kprime∧Hsecond=0).
- gomesDilatonHamiltonian_derivative_fibers H K : actual HamEq↔same derivative alternatives.
- gomesDilatonHamiltonian_parts_iff H K : HamEq↔Hsecond=Ksecond∧(Hprime)²=(Kprime)².

3. GomesPolynomialHamiltonianFibers (7theorems), imports above + GomesDilatonDualShiftRigidity:
- gomesDilatonDerivative_constant_iff H a : Hprime=C a↔∃b,H=C a*X+C b.
- gomesDilatonPotential_profile_fibers H K : potentialEq↔(∃c,H=K+C c)∨∃a b c,H=C a*X+C b∧K=C(-a)*X+C c.
- gomesDilatonHamiltonian_profile_fibers H K : same for actual Schwartz HamEq.
- gomesDilatonHamiltonian_dual_eq_iff H : HamH=Ham(-H)↔∃a b,H=C a*X+C b. Reuses existing secondDerivative_constant_iff at0.
- gomesDilatonHamiltonian_origin_slope_iff H K : (HamEq∧Hprime.eval0=Kprime.eval0)↔superchargeEq.
- gomesDilatonHamiltonian_origin_jets_iff H K : (HamEq∧H.eval0=K.eval0∧Hprime.eval0=Kprime.eval0)↔H=K.
- gomesDilatonHamiltonian_curved_fibers (H:{H:ℝ[X]//Hsecond≠0}) K : HamH=HamK↔∃c,H.val=K+C c.

4. GomesConstantPolynomialPotential (8theorems), imports above:
- gomesDilatonPotential_affine a b x : potential(C a*X+C b)x=a²/4.
- gomesDilatonPotential_constant_iff H k : (∀x,potentialHx=k)↔∃r b,H=C(2*r)*X+C b∧r²=k.
- _constant_image_iff k : (∃H,∀x,potentialHx=k)↔0≤k.
- _square_fiber H r : (∀x,potentialHx=r²)↔(∃b,H=C(2*r)*X+C b)∨∃b,H=C(-2*r)*X+C b.
- _zero_iff H : (∀x,potentialHx=0)↔∃b,H=C b.
- gomesDilatonHamiltonian_free_iff H : HamH=Ham0↔∃b,H=C b.
- gomesDilatonHamiltonian_affine_eq_iff a b c d : Ham(C a X+C b)=Ham(C c X+C d)↔a²=c².
- gomesDilatonConnection_affine_eq_iff a b c d : same first-order connection iff a=c.

5. GomesHamiltonianTensorProbes (6theorems,1def), imports GomesPolynomialHamiltonianFibers:
- gomesDilatonHamiltonian_tensor_pair_iff H K R : (HamH=HamK∧Ham(H+R)=Ham(K+R))↔HamH=HamK∧(superH=superK∨Rprime=0).
Proof difference of squared derivatives gives 2*Rprime*(Hprime-Kprime)=0, no zero divisors.
- gomesDilatonHamiltonian_linear_probe_iff H K : (HamH=HamK∧Ham(H+X)=Ham(K+X))↔superH=superK.
- gomesDilatonHamiltonian_all_tensor_contexts_iff H K : (∀R,Ham(H+R)=Ham(K+R))↔superH=superK.
- def gomesDilatonTensorHamiltonianRecord H:=(HamH,Ham(H+X)), pair of actual complex Schwartz CLMs.
- _eq_iff H K : recordEq↔∃c,H=K+C c.
- _origin_iff H K : (recordEq∧H.eval0=K.eval0)↔H=K.
- _augmented_injective : Injective(funH=>(recordH,H.eval0)).

6. GomesHamiltonianNormalizationBoundary (7theorems), imports GomesConstantPolynomialPotential:
- gomesDilatonMeasure_affine_mass a b : raw(C a X+C b)univ=∞. Reuses gomesPolynomialAffineTilt_finite_iff atH0 and zero_not_mem.
- gomesDilatonMassNormalized_affine a b : norm(C a X+C b)=0.
- gomesDilatonHamiltonian_affine_kernel a b : ker(Ham(C a X+C b)).toLinearMap=⊥.
- gomesDilatonMassNormalized_hamiltonian_iff H K : normH=normK↔HamH=HamK∨(rawHmass∞∧rawKmass∞). In particular HamEq always implies normEq.
- gomesDilatonHamiltonian_connection_failure_iff H K : (HamEq∧superNe)↔∃a b c,a≠0∧H=C a X+C b∧K=C(-a)X+C c.
- gomesFinitePolynomialProfile_curvature_ne_zero P : P.valsecond≠0.
- gomesFinitePolynomialHamiltonian_arbitrary_fiber P K : HamP=HamK↔∃c,P.val=K+C c. K unrestricted; stronger than previous finiteP/finiteQ result.

## APIs / proof traps
RiccatiApi.lean terminalexit0 verified dvd_derivative_iff,derivative_eq_zero,eq_C_of_derivative_eq_zero,derivative_mul,derivative_pow,C_injective,derivative_C_mul,degree_derivative_lt. Real.sq_sqrt verified by actual scratch proofs. #check outputs make API log NONEMPTY; only check errors, not empty.
- eq_C_of_derivative_eq_zero hp returns P=C(P.coeff0); NEVER simp[that equation] because RHSselfreferencesP. letc=P.coeff0, rw equation once.
- `rw [← neg_eq_iff_eq_neg] at hu;rw[←hu,hc,map_neg]` works for U=-V and U=Cc to derive V=C(-c).
- gomesDilatonDerivative_constant_iff: `simpa only [derivative_C_mul,derivative_X,mul_one] using(gomesDilatonDerivative_eq_iff H(C a*X))` FAILED to simplify inside using. Working proof: constructor; introh; apply(gomesDilatonDerivative_eq_iff H(C a*X)).mp;simpa usingh; reverse rintro⟨b,rfl⟩;simp.
- Calling `(gomesDilaton_secondDerivative_constant_iff P.val 0).mp hz` with hz:Hsecond=0 FAILS since expectedHsecond=C0. Pass `(by simpa using hz)` before final `simpa using` the resulting quadratic classification.
- To remove polynomial factor2 use `(mul_eq_zero.mp hp).resolve_left two_ne_zero`; no computations.
- Lint ends `formal lint passed` lowercase, notPASS. Existing unrelated LabeledBoundarySimplex94unnecessarySimpa replay warning remained untouched.
- Don’t run unfiltered ps output: filter Python result to own Lean/Lake processes; full command lines from unrelated processes are noisy and can contain private data.

## Next conjecturing loop
Classify constant differences of Riccati images and actual polynomial Hamiltonian scalar energy shifts. Expected trichotomy for F(U)-F(V)=C k:
1 U=V and k=0;
2 U,V constant with squared difference k;
3 U=-V and Uprime=C(k/2), so opposite affine drifts.
For profiles: same derivative/zero shift; arbitrary affine profiles with squared-slope energy difference; opposite quadratic profiles up to constants with Hsecond=C k.
Build missing forced polynomial ODE theorem: Bprime=A*B+C c. If B nonconstant, degree(Bprime-C c)<degree B; B divides Bprime-C c, so derivative=C c and A=0. ConstantB branch algebraic. Then take B=U-V,A=-(U+V),c=k. Verify all degree/divisibility APIs in scratch before use.
Already searched research 'polynomial constant shift' (2hits) and 'constant shift' --moduleGomes (10hits), all reviewed in next-shift-search.json/all-constant-shift-search.json. Existing GomesDilatonDualShiftRigidity.gomesDilatonDual_constant_shift_iff and _quadratic_rigidity classify ONLY prescribed dual pairs. GomesQuarticChargedConnection contains family-specific no-go. No general arbitrary-pair theorem found. Reuse existing dual quadratic theorem. Earlier batch32 searches Riccati equality0, derivative-squareGomes0, derivative-multiple7irrelevant, polynomialpotentialconnection1priorfinite theorem, affine derivative0, dualHamiltonian7knownapplications, derivativeconstant10known, constantpotential5known, Ham tensor reconstruction0, affine mass2known. No duplication.

## Attribution
2509.25276v7 withdrew earlier equivalence; NEVER revivev1–v6claims. Reverified https://arxiv.org/html/2509.25276v7#S5.SS2 and https://arxiv.org/html/2607.24901v1#S4 thisbatch. Tensor charge/composition and information-reconstruction ideas motivate our scalar analogues. Not full gauge-category formalization. 2404.10461 fundamentalgeometrypaper previouslyverified. All source claims modest.
