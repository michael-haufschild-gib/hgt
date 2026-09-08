# Verified original forced radial master at fundamental Xi QNMs

Goal ACTIVE, RH UNPROVED. Frontier map READ ONLY; do not edit. No subagents authorized. No numerical computations indicated/run. This turn produced a real verified radial ODE continuation, NOT full joint continuation or physical left pairing. Do not re-audit these leaves.

## Installed and verified
8 canonical leaves, 691 lines, 31 public theorems:
HTGeometry:
- HypergeometricSpatialJets
- HypergeometricLocalFamilies
- FirstEndpointMellinSpatial
RHTower prefix ThetaCuspHawking:
- BMLaplaceSpatialODE
- BMLaplaceJetHolomorphy
- BMLaplaceWronskianContinuation
- BMLaplaceMomentSpatial
- BMLaplaceContinuedForcedODE

All individual canonical lake build <module> audits passed without warnings, in isolated cache package with 3,998 old own dependency oleans. Exactly 8 new oleans built; no dependencies/umbrellas rebuilt. Only the 31 new public theorems got scratch #print axioms; all only propext, Classical.choice, Quot.sound. All 16 installed olean/ilean copies byte-identical to audited artifacts. Imports wired: 3 HTGeometry, 5 RHTower.
Index refreshed once. Global lint --check-generated: no new-leaf errors or generated drift; unrelated concurrent unwired HTGeometry.FokasLenellsScatteringContinuity and FokasLenellsSpectralContinuity; existing large-file warnings. Do not modify others' work.
Owned scratch /tmp/hb-radial-ode.e9Yjyn scheduled for removal at end; no owned Lean/Lake process left after audits. No commits/pushes. Frontier and universal STATUS not changed by this work.
Docs:
- docs/drafts/pipeline/3-formalized/hb-original-continued-radial-master.md (paper proof, validation, remaining boundary)
- docs/drafts/pipeline/1-in-progress/hb-qnm-parameter-continuation.md (current target updated)

## Main exact theorems
Namespace RHTower.D4BMLaplaceRadial.
continuedResponse_allXi_fundamental_original_equation, canonical BMLaplaceContinuedForcedODE line106:
every XiZeroCopy q, fixed s a J K, both n=0 physical QNM Laplace frequencies w, each b in (0,1):
eventually u in punctured nhds w, original D4BMPhysicalMaster.radialJet (I*u) chi b applied to continuedResponse and ACTUAL deriv/deriv deriv in b equals sqrt(1-b)*continuedSourceProfile s a J K u b/2.
No supplied nonresonance, endpoint admission, continuation, source-numerator nonvanishing or RH premise.
General continuedResponse_original_equation_germ: nonreal w, -2<Rew, b interior. Same germ identity.
continuedResponse_original_equation: pointwise for connection w chi !=0. That natural off-pole condition is DERIVED on a punctured neighborhood in the germ capstone.
continuedResponse_hasDerivAt: first and second spatial jets are actual derivatives.
continuedResponse_deriv_eq: exact deriv and deriv deriv values. Double derivative via eventual equality of first deriv with first jet on Ioo.
Defs continuedResponseFirst/Second parallel original responseFirst/Second, replacing old moments and source by continued originals. Second retains moving endpoint source jump.
Previous meromorphy/equality-to-original theorem remains exactly same continuedResponse.

## Proof and APIs
HTGeometry.hypergeometric_radius_one_le a b c : 1 <= ordinaryHypergeometricSeries radius for ALL complex params. Split exists parameter=negative natural -> corresponding mathlib radius_top theorem, else radius_eq_one. Totalized denominator collisions still converge, but original horizon Gauss ODE uses w.im!=0 to exclude denominator collisions.
hypergeometric_coefficient_shift a b c n:
(n+1)*Coeff a b c (n+1)=(a*b/c)*Coeff(a+1)(b+1)(c+1)n, valid even terminating numerators/totalized c.
Uses ascPochhammer_succ_left+eval_comp for leading-factor shift, factorial_succ, mul_inv_rev, field_simp.
hypergeometric_first_eq_shift: actual RHTower.ordinaryHypergeometricFirstDerivativeSeriesValue=(ab/c)*ordinaryHypergeometric shifted, unit disk. Via existing HasSum value/first/second theorem and HasSum uniqueness.
hypergeometric_family_of_im_ne_zero / _of_re_pos: AnalyticAt parameter families and corresponding denominator im!=0/re>0 imply DifferentiableAt original Gauss sum, |z|<1. Local sum-of-norm bounds and real/imag separation feed existing parameter-uniform dominated-sum theorem.
BM gaussFactor_derivatives_continued: all w chi, |z|e<1, both jets.
horizonFactor_equation_continued and horizon_equation_continued: w.im!=0.
outerGauss_equation_continued, outerFactor_derivatives_continued, outerFactor_equation_continued, horizon_derivatives_continued, normalizable_derivatives_continued, normalizable_equation_continued: all w, proper spatial interior.
horizonGaussFirst_frequency_differentiableAt: nonreal w; outerGaussFirst_frequency_entire.
horizonFirst_frequency_analyticAt: nonreal w, interior radius; normalizableFirst_frequency_entire: arbitrary w, interior radius.
wronskian_frequency_analyticAt: nonreal w.
wronskian_eq_continued: original integratingFactor*(H*Nfirst-Hfirst*N) = -connection/2 for ALL nonreal w incl its zeros, all interior b.
Proof: identity theorem on each upper/lower half-plane. Seed v=(|chi.im|+1, w.im) belongs same component and original Chamber v chi. Original proven W normalization supplies seed; frequency holomorphy extends it.
connection_eventually_ne_zero: nonreal w, eventually punctured nhds connection!=0. Local analytic zero dichotomy; identically-zero alternative propagates over same half-plane to seed and contradicts original connection_ne_zero in Chamber. Do not confuse codiscreteWithin theorem with pointwise punctured nhds; use local dichotomy + eqOn_zero_of_preconnected_of_eventuallyEq_zero.
HTGeometry.firstEndpointMellin_hasDerivAt:
hb>0,-2<Rew,w+1!=0, measurable Fw, continuousAt Fw b, first-difference bound on Ioc0b -> derivative in b of restored Mellin = b^w*Fwb.
Uses prior remainder integrability, genuine interval FTC, eventual Ioc=interval integral, cpow derivative, exact cancellation of restored F0.
continuedSourceProfile_continuousAt: all w, positive b.
horizon_continuedSource_eq_mellin: H(w,t)*continuedSource = t^w*actual horizonMellinCore(w,t)*(1/(w-2s)+onsetCorrection(2s)w).
continuedHorizonMoment_hasDerivAt: nonreal w,-2<Rew, b interior -> H*Scont/(-connection), no assumed connection nonzero necessary for derivative identity of totalized formula.
continuedOuterMoment_hasDerivAt: all w,b interior -> -(N*Scont/(-connection)). Actual outer integrand continuous through t=1; Gauss at argument0, sqrt outer factor continuous on real line. FTC at lower endpoint.
Original forced ODE assembly: homogeneous H,N ODEs cancel bulk; source jump becomes b(1-b)(Nfirst H-Hfirst N)S/(-connection), then W identity and sqrt-square identity give sqrt(1-b)S/2. Derived actual derivatives, not assigned jets.
Fundamental Xi frequencies nonreal and Re>-2 from existing strict Xi strip + nonzero real coordinate. Same explicit algebra as prior capstone; no repeated old axiom checks.

## What is actually still hard
Full proof chain: literal theta cusp -> Xi occurrence -> retained spin-two source -> original causal response and physical left-QNM pairing -> independent Hawking-clock extinction -> RH.
Current necessary next work: transfer newly verified continued radial original ODE through tortoise chart into ORIGINAL principal responses, radialLift subtraction and all 3 cutoff commutators. Then weighted joint angular/radial domain continuation of complete source and response, physical advanced/adjoint left residue. Scalar radial germ continuation alone does not prove these, pole survival or extinction.
Already-read actual source files in this turn/prior:
ThetaCuspHawkingBMJointSource{GreenAdmission,PrincipalData,GradientReduction,ResidualAssembly}.lean, plus BMLaplace{GaussFactors,OuterFactor,Solutions,Wronskian,EndpointGreen,ParameterHolomorphy,FrequencyContinuation,SourceContinuation,HorizonMomentContinuation,OuterMomentContinuation,OuterEndpointBounds,PowerJets,SourceProfile,FundamentalContinuation}.
No file ThetaCuspHawkingBMJointWave.lean; find actual names using rg --files.

principalDifference q branch w a T i t =
tortoiseGreen w (principalFrequency q i) (physicalRate q branch) a
 (principalAmplitude q i) (principalGradient q branch i) T t
- radialLift (physicalRate q branch) w a T t*principalAmplitude q i.
cutoffRadialCoefficient=horizonCoordinate t * principalDifference.
cuspResidualForcing=reducedCoefficient*squareResidual + sum_i cutoffRadialCoefficient*cutoffCommutator.
explicitField=radialLift*fullSquarePotential+sum principalDifference*cutoffPower.
originalForcing_explicitResidual (old PrincipalChamber) identifies literal full source = explicitSeparatedWave + cuspResidualForcing; retains all cutoff derivatives.
Scalar_gradient_absorption and stream variant use literal radialLift derivatives at all w. principalFrequency q i=I*(principalExponent q i-1/2), exponents [2q,1,2-2q]; distinct from physical Xi QNM chi. Principal amplitudes are both Weyl squares and their cross term; do not omit any.
Prior original joint causal response already constructed in convergence half-plane; its continuation and physical left pairing are separate obligations.

## Build/API discipline learned
Run broad corpus OR (--any) discovery then focused AND. This turn searched weighted/resolvent/scattering/Fredholm, parameter/derivative/holomorphic, Wronskian/connection/derivative/parameter, and focused intersections. Actual corpus was starting point; no external/numerical conjectures used.
Use one foreground lake/lean. Scratch actual names before use. Check tool exit before dependent build.
exact_mod_cast does NOT convert norm<1 to enorm<1 here; simpa only [<-ofReal_norm,ENNReal.ofReal_lt_one].
convert! handles disabled complex-real instances. In HasSum shift, explicitly unfold RHTower.ordinaryHypergeometricFormalCoefficient in simpa to avoid reducibility mismatch.
ContinuousAt compositions may need dsimp before linarith. Pi.mul_def/Pi.sub_def and mul_assoc normalize function/product forms.
StronglyMeasurable.stronglyMeasurableAtFilter is MeasureTheory namespace; dot form hmeas.stronglyMeasurable.stronglyMeasurableAtFilter works.
Local audit path manifest can be written directly; no lake update needed. Old .ilean may be absent; only .olean required. Don't rebuild to replace unused old .ilean. New artifacts must include both and be verified.
