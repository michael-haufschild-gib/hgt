# Root: new dyadic winding obstruction and literal complex Ward bridge

Goal remains unconditional Lean RH proof/falsification, unresolved. User explicitly forbids touching git and insists conjecture/proof-or-failure/pivot loops. No git commands in this continuation. No numerical experiments, no subagents. Follow docs/meta/scientific-method.md and stroke-of-genius-method.md; derived results labeled BRIDGE, no new universal producer claimed.

NEW FINISHED LEAF: formal/GaloisForLFunctions/RHTower/ThetaBoundaryDyadicClassification.lean (400 lines), namespace RHTower.DyadicBoundary.
- Law F: F(x+1)+F x=F(4*x)/2.
- Primitive F=(F x-F(x+1))/2.
- Reconstruction A=sum_n (1/4)^n*A(4^n*x).
- Complete bounded 2-periodic solution classification: reconstruction_primitive, primitive_reconstruction. Continuous anti-periodic A gives continuous bounded solution. Exact finite_reconstruction and error <=M*4^(-N), norm bound 4M/3.
- integral_eq_zero: continuity+period2+law already force mean zero.
- exists_injective_normalized_family: entire complex parameter free with normalized endpoints 4/3,-2/3.
- MAIN NEW NO-GO exists_arbitrary_odd_winding (k): continuous nowhere-zero period2 Law solution, endpoints4/3,-2/3, mean0, winding=-(2*k+1). Construction A_k=exp(-i*pi*x)^(2k+1), remainder norm<=1/3, quotient F/A lies radius1/3 around1, hence winding0 correction. Scaling pi^2/8 matches actual theta endpoint values. Does NOT identify these loops with literal theta renewal feedback or falsify RH.
- Positive survivor full reconstruction classification is Lean-closed, not just negative statement.
- Source scratch and named leaf build pass. All36 public axiom reports only propext,Classical.choice,Quot.sound. Wired into RHTower.lean.
- Card docs/drafts/pipeline/5-failed/theta-dyadic-boundary-winding-rigidity.md. Own fact log F14-F16.

NEW FINISHED BRIDGE LEAF: formal/GaloisForLFunctions/RHTower/ThetaCuspComplexWard.lean (~115 lines), namespace RHTower.ThetaImaginaryArc.
- Potential z=exp(z/2)*jacobiTheta(I*exp(2*z)); realJet m x=2*thetaCuspTailDerivative m x+exp(x/2)/2^m.
- analytic_potential, potential_real, hasDerivAt_realJet, deriv_potential_real, deriv2_potential_real, source_real_ward, source_complex_ward.
- MAIN source_complex_ward proves literal thetaCuspStripSource=(deriv(deriv Potential)-Potential/4)/2 on thetaCuspStrip. Proof real jets + analytic continuation, no surrogate or unproved premise.
- Scratch and named leaf build pass. All7 public axiom reports standard-only. Wired into umbrella. Fact F17.

NEXT SOURCE-SPECIFIC ATTACK, PAPER DERIVED, NOT YET LEAN-CLOSED:
Own card docs/drafts/pipeline/1-in-progress/rh-theta-imaginary-arc-charge-2026-09-26.md. Set L=pi/4, p(t)=Potential(i*t), k=literal source. P even and Schwarz -> p real. p''+p/4=-2k(it). Exact shifted-Poisson formula with delta=L-t:
p(L-delta)=sqrt2*(sin delta)^(-1/2)*exp(-(pi/8)*cot delta)*R(q),
q=exp(-pi*cot delta), R(q)=sum_m>=0 (-1)^(m(m+1)/2)*q^(m(m+1)/2).
Derived using w=exp(2it)-i=2 sin(delta) exp(-i delta),1/w=(cot delta+i)/2; phases cancel. R analytic at0, R0=1, first2 derivatives uniformly bounded near0. This gives p,p',p'' flat atL and delta^4*p''/p->(pi/8)^2, hence k(it)<0 eventually nearL. k0>0 -> interior imaginary source zero.
Exact Green charges: integral0L cos(t/2)k(it)=0; integral0L sin(t/2)k(it)=-theta(1)/4. Positive survivor is this signed charge, no whole-strip log k. Does NOT decide Xi zeros/RH. Cusp derivative flatness + integral/IVT transfer remain Lean-open. Existing numerical-only source zero near0.6388i in xi.md motivated test; no numerical location needed.

Verification logs /tmp/rh-dyadic-{leaf-build,axioms,index,lint}.log; /tmp/rh-theta-complex-ward-{build,axioms}.log; /tmp/rh-boundary-final-{index,lint}.log. Final index succeeded. Final global lint --check-generated FAILS on FIVE unrelated missing umbrella imports: ModularAxisSourceTransform,ThetaGroupDeformationPrimeTwo,ThetaGroupFormCuspBounds,ThetaGroupHauptmodulForms,ThetaGroupOffLineStripZero. Do not edit other agents' files/logs. All owned tool sessions terminal; no owned Lean/search jobs left.

Other worker concurrently adds theta-group modular off-line countermodels: ThetaGroupHauptmodulForms defines thetaThree*P(h), h=lambda(1-lambda), exact period2 and S covariance; ThetaGroupOffLineStripZero proves two real coefficient deformation has an off-line transform zero, NOT RH falsification. Those files currently unimported by umbrella; read headers before relying. New ThetaGroupDeformationPrimeTwo appeared during final lint and was being inspected at checkpoint. No need repeat dyadic/finite-prefix proofs or broad builds. Prior finished fixed-prefix theorem memory mem:rh/reflection-source-sign-fixed-prefix-2026-09-26.
