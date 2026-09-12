HB extinction/RH goal remains ACTIVE and OPEN. This turn is verified progress: closed actual incoming radial sector's finite-cusp physical-clock balance. Do not mark overall goal complete/blocked. No extra action/extinction/covariance assumptions.

New leaf:
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticTestedCurrentCusp.lean
namespace RHTower.D4BMQuarticTestedCurrentCusp.
SHA256 ce13833079844dd9a71392bdfbcd65ed72cf5bbef7c67636bab0d8557e730c5d.
~401 lines, 9 public theorems +8 public definitions.
Scratch /tmp/hb-tested-angular-current.lean passed with original and trimmed imports using lake env lean at default limits.
Final exact isolated lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticTestedCurrentCusp passed in16s, only cached imports, via formal/.lake/hb-extinction-scratch/audit-leaf.py. Matching oleans/hashes copied back. No heartbeat/depth/transparency changes. Umbrella once (line17475 when checked).
Index initial8changes; first lint staleAPI+overview due VERIFIED concurrent RHTower.lean and MaassLadderL2.lean edits after index. Reindex2changedfiles; FINAL lint --check-generated PASS exit0. All17 API entries + singleumbrella + sourceSHA rechecked. Audit dir hb-quartic-leaf-audit-dgdqxawn removed.
ALL ownprocesses terminal: finalscratch59433, audit45370, search43289, index7516/89401, lint40987/23169. No remaining handles/processes to wait/restart. No commits/push.

Paper card docs/drafts/pipeline/3-formalized/hb-physical-clock-tested-current-cusp-balance.md.
Active card docs/drafts/pipeline/1-in-progress/hb-source-contact-spin-two-balance.md appended exactsourceidentity, researchmethodaudit, finalstatus.
Proof chain theta -> Xi -> retainedspin2 -> physical causal radial/left-QNM action -> fixed common Hawking-clock extinction -> RH.

IMPORTANT RATE DISAMBIGUATION:
New module/sourceWork use D4BMModularCore.physicalRate = fundamental s=rho-2,t=-rho-1, s+t=-3.
D4BMCuspProjection.physicalRate in cusp-root formulas is DOUBLED. Do not confuse them.
Original incoming horizon clockMoment retains common rate -6, independent of q.

Let H/K=fullAngularField true/false, Q=fullSquarePotential, psi=scalar physicalAngularParameter, alpha/beta=parameter true/false, w_i=sourceWorkWeights.
Original angularResponseGreen JG=beta(K+Q)gradH-alpha(H+Q)gradK.
Original reducedSourceCurrent JS=Q[w0gradH+w1gradK+(2w2/3)gradQ].
completeCurrent J=-(s*t/3)JG+JS (line31).
testedCurrent=psi J (36); testDerivativeWork=sum dpsi_j J_j (40).
Original reducedSourceWork W=w0alpha QH+w1beta QK+squareWorkCoefficient Q².
Old source identity y² clockCoeff_1,0 =4(a²b²/64)[y²divJ-W].
Arbitrary original COMPLEX amplitudes a,b retained.

PUBLIC THEOREMS:
testedCurrent_divergence93: div(psiJ)=gradpsi·J+psi divJ.
tested_radial_balance106: psi clockCoeff=4(a²b²/64)[div(psiJ)-gradpsi·J-psiW/y²].
testedCurrent_periodic169: full testedCurrent periodic under Fin2 translation ![1,0], INCLUDING contact Q terms and bothfullresponses; from literal scalarperiodicity, fullAngular modular invariance, periodic coordDeriv.
cuspBoundary_hasDerivAt240: B'=D on positiveheight.
testedCurrent_finite_cusp_stokes264: int_l^r D=B(r)-B(l).
radialTestDensity_eq315: R_ab=4(a²b²/64)(D-Wtested).
physical_radial_finite_cusp_balance346: int_l^r R_ab=4(a²b²/64)[B(r)-B(l)-int_l^r Wtested].
physicalClockDensity_eq375: T_h=h exp(-6h)R_ab forALL realy andh:NNReal.
physical_clock_finite_cusp_balance389: int_l^r T_h=h exp(-6h)4(a²b²/64)[B(r)-B(l)-int Wtested].

Public definitions:
cuspBoundary217=mean_x psiJ_vertical in original planar chart.
cuspDivergenceDensity220=mean(divtested).
completeTestedWorkDensity306=mean(gradpsi·J+psiW/y²).
radialTestDensity310=mean(psi*actualclockCoeff q a b ...1 0).
physicalClockDensity370=mean[psi*clockMoment(-6)h(fun u=>incomingCurrent q a b 1 u coords 1)].
Meanwidth[-1/2,1/2], exactplanarchart.
Finiteheightl,r:Ioi0; nativefundamental-cusp applications take l,r>3.
PlanarintpsiClockCoeff is nativeintpsi*y²ClockCoeff dmu on actualcusp; DON'T lose this metricweight.
Common-clock moment theorem uses existing incomingCurrent_horizon_clockMoment, not fittedfrequency.

Every public result specializes original constructedsource data, no added conservation/extinction/admission hypothesis. This is INCOMING RADIAL SECTOR only: does NOT identify complete leftQNMaction or prove extinction/cancellation of otherchannels/boundaries.

Optimization:
Trimmed imports to QuarticResponseWork, PhysicalAngularCutoffCalibration, CuspMeanDerivative, HTGeometry.ComplexCoordinateDerivativeRules; doesn't need fullQuarticFinitePartchain.
ContDiffAt.const_mul unavailable: use contDiffAt_const.mul h.
For REALsmooth COMPLEXquotients use numerator.mul(denominator.fun_inv hne); ContDiffAt.div hereforces targetsameasbasescalar. Explicitlambda change before simp[div_eq_mul_inv], partialworkField q won't unfold underContDiffAt using simp.
Continuous.integrableOn_Ioc needs explicit μ=volume AND a=-1/2,b=1/2 in untypedhave declarations.
Normalize Function.comp_apply inintegrability hypotheses before integral_sub rewriting.
Before ring/linear_combination fully identify coordinates z1=z.im and nativecoordinates with angularCoordinates(pointxy), includingRHSdenominators. Ring treatsunreducedcoordinateforms asdifferentatoms even if rfl.
Symmchartre/im: local hre/him proved by change ((w0:ℂ)+(w1:ℂ)*I).re/im=...; thenrewrite. simp[angularCoordinates] alone doesn'treduce continuouslinearequiv.symm.
Subtypepositiveproperty simp can becomeTrue: explicitlyrewrite(pointxy).im=y thenexact y.2.
FullAngularField globalhorizontalperiodicity proof positivecaseT modularinvariance, nonpositivecase ofComplex_apply_eq_of_im_nonpos; outsideextension iscommon Classical.choice, don'tassumeI.

Research:
Deep cached300s formal/.lake/hb-extinction-scratch/tested-current-source-product-search.json completedPARTIAL, oldergeneration/semanticcoverageunavailable. Inspected candidatelemmas/sourcearguments/methods/proofideas/ingredientsets. UsedactualsourceWork, literalperiodicity andcuspcalculus successfully. General/coreGreen hits don'tsupplycancellation oftestderivativework.
Primary broadarXiv:
https://arxiv.org/html/2608.25047v1 CamposKillipVisan Aug25 KirchhoffPohozaev: resolventgeneratingfunction+quarticGramcorrection conservedforc(q)=(1±<q,Aq>)^-1 andfixednonnegativeSA A. NoidentificationwithactualHBnonlinearassembly; noimportedconservationassumption.
https://arxiv.org/html/2609.01891v1 Bambusietal Sep1 sameequationinvolutiveHamiltonians; noHBmodelidentification.
https://arxiv.org/html/2609.04169v1 Vuetal Sep3 passivelinearreciprocity: compliance symmetry, notyetcompletecausalnonlinearactionboundaryidentity. No computations/numericalexperimentsused.

NEXT HARD TARGET:
Original uppercusp finitepart of B AND complete differentiated-test work, with native response PRODUCTS retained; match prior source-derived fullscalar-tested response periods (mem:hb_full_tested_cusp_period_2026_09_12) and local Q²finitepart. Thenjoin every remainingphysical scalar/scalar,scalar/vector,vector/vector,retainedspin2,horizon,characteristic,sourcecontact contribution andactualleftQNMradialresidue. Horizontalperiodicity onlycancels sideflux; it doesNOTremoveBtop/Blower/testderivativework. Don'tdefinebracketzero orassumeclockinvariance. Coercivity/orientationfromliteraltheta stillmissing. New balance makes that obligationexplicit, ratherthanassumingit.