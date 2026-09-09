# HB original physical quotient pairing — finalized

Goal ACTIVE, RH UNPROVED. This goal turn made PROGRESS: actual original integral regularity, physical identification and complete four-channel angular source value, six installed/audited leaves, 15 public theorems. Previous turn's broad Fokas/Higgs search was evidence progress; it found a normalized Schwartz Cauchy inverse but no identification with HB scattering. Frontier map READ ONLY. No agents authorized. No numerical computations, full builds or umbrella builds. Only NEW theorem axiom checks. One owned foreground Lean/Lake process at a time. Other tasks actively modify this huge corpus; do not kill/build/edit their work.

## Installed exact modules
All prefix GaloisForLFunctions.RHTower.ThetaCuspHawking; canonical filesystem formal/GaloisForLFunctions/RHTower/.
- BMNativeScalarUniformCusp:100 lines,3 public theorems; namespace RHTower.D4BMAngularSeries.
- BMNativeResidualUniformWeights:61 lines,2; namespace RHTower.D4BMJointSource.
- BMNativeClearedDomination:68 lines,1.
- BMNativePeriodRegularity:86 lines,4.
- BMNativePhysicalPairing:105 lines,4.
- BMNativePhysicalSourceValue:23 lines,1.
Total443lines15publictheorems. Six sources+12olean/ilean installed and18hashes verified twice; six imports wired exactlyonce after BMNativePeriodPhysicalValue in RHTower.lean. Allsix scratch lakeenvlean checks andall6individualcanonical lakebuildmodule audits passed WITHOUTwarnings. Actualcompile times3.7–5.2s/leaf. An initial empty-globs audit returned a no-op; detected missing artifacts, corrected globs to exactcanonicalmodule, then ACTUALLY compiled allsix. Do not count no-op as audit. Exactly15newpublicaxiom outputs ONLY propext,Classical.choice,Quot.sound; no Lean.ofReduceBool or added axioms. Capstone #check confirms explicitXi source andRe q>1/2, no extraadmission/identification/RH premises.

One indexrefresh completed (12changed,0removed; others concurrentlyedited). One repo-wide static lint--check-generated EXIT1 because separately added GaloisForLFunctions.HTGeometry.FokasLenellsContourFundamental was unreachablefromHTGeometryumbrella. No newHBunreachableorproofdebt. DO NOTclaimglobalstaticgatepassed; failure recordedinnewproofcard. Scopedgitdiffwhitespace andalllinksinfourupdatedcards passed. Do not repeatedly rerun lint or editotheragents'newFokaswork just forglobalgreen.

## Cleanup
/tmp/hb-native-regularity.hq2dtu_u and /tmp/hb-native-regularity-current both REMOVED. Marker verified before deletion. NoownedLean/Lakeprocesslive; alltoolhandles terminal. Sixinstalledcanonicalsource/artifacthashesverified immediatelybeforecleanup. Private4145requireddependencyhardlinkcache removed without affectingoriginalartifacts. No scratch currently exists; recreateprivatecacheauditwhen needed. ToolchainformalLean4.32.2. Neverrunlakeenvfromwrongcwddefault4.33.1. Source/artifacts installedwithbytechecks, no commit/push requested orperformed.

## New mathematics
q:XiZeroCopy. Original scalarResidualPeriod q u is actual quotient integral J(q,u)=int scalar(u,z)*squareResidual(q,z)dmu. Source/measure/allFouriermodes/cutoffs unchanged.
P(u)=clearFactor u=u(2u-1)(2u+1).
Eclear=(2u+1)Xi(2u)y^(.5-u)+(2u-1)Xi(1+2u)y^(.5+u)+P(u)tail_u.
New clearedResidualPeriod q u=K_q(u)=int Eclear_u*S_q dmu.

UniformTail lemmas:
scalar_heightDecayConstant_uniform R l hR hl gives C>=0 controlling heightDecayConstant u u 0 l for ALLnormu<=R. Literal coefficientbound (N+1)^(3|Reu|+1) <= (N+1)^(3R+1); besselBound u l<=exp(R²/(2l))*sqrt(2pi/l); summablefixedmajorant(N+1)^(3R+1)*exp(-N*l/2). Existingvalue_height_decay thenprivatebounded y^.5 exp(-y/2) gives scalar_value_uniform_cusp. Fulltail=2*(signedfalse+signedtrue), so scalar_tail_uniform_cusp gives one C fornormu<=R,ALLhorizontalx andy>=l.

squareResidual_fd_weighted_bound q w: eachfixedcomplexheightweight*y^w*S_q boundedonfd. Lowfd truncatedaty4 compact; highy>3 source=squareRemainder(centerq)/2 usesoldweighted_squareRemainder_bounded. Spatialcontinuitycpowonpositiveheight. squareResidual_fd_uniform_weight_bound q a b: oneconstant controls ALLw witha<=Rew<=b, ALLzfd. Endpointinterpolation y^Rew<=y^a+y^b bycasesy<=1 or>=1. No assertionaboutcomputationaltruncations.

clearedScalar_squareResidual_fd_uniform q R hR: oneC>=0 uniformlyboundsEclear_u*S_q fornormu<=R,zfd. CompactboundsXi/polynomialcoefficients; weightinterval[.5-R,.5+R]; fdy>=.5; uniformtailtimesresidualbound.

clearedScalar_squareResidual_continuous q u: continuousoriginalintegrandonUpperHalfPlane allu, uses height_cpow_contDiffOn andcuspTailPart_contDiffOn.
clearedScalar_squareResidual_integrable q u: actualquotientabsoluteadmissionallu.
clearedResidualPeriod_differentiable q: K_q ENTIREforEVERYXisource(noRe qrestriction). Proofusesfd.indicator originalintegrand to satisfyALLspatialpoints dominationpremise of HTGeometry.differentiableAt_integral_of_cauchy_dominated. Constantboundintegrablebecause originalquotientmeasurefinite. Indicatoragreesa.eonrestrictedfd measure. Radius1aroundu0 boundedbyR=normu0+1.
clearedResidualPeriod_eq q u hu: ifu.im!=0,K_q(u)=P(u)*J(q,u), viaoldpointwiseclearedScalar_eq andactualintegral_const_mul.

## Actual physical identification — CLOSED now
Previous nativePeriodContinuation q s=Jc_q(s) completeexpression andnativePeriodContinuation_eq_original q hq s hs had hq:Req>.5,hs:Res>2. PreviousphysicalvaluewasONLYcontinuation; now actualintegral equalityproved.
clearedResidualPeriod_eventuallyEq_continuation q hq u:
K_q =eventually[puncturednhds u] (v=>P(v)*Jc_q(v+.5)) forEVERYu, WITHReq>.5.
Difference globallymeromorphic. Vanishesonnhood3+i usingoldchamberequalityandnonrealclearing. meromorphicOrderAt=top there; MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected onuniv forcesorder=topeverywhere. Givesactualpuncturedgermidentity.
Atuphys=(q-1)/2, oldJcphysicalanalytictogetherwithKentiregivesactualvalueequality bytendsto_nhds_unique_of_eventuallyEq. Xiim!=0 provesP(uphys)!=0, cancel legitimately.
scalarResidualPeriod_physical_eq_continuation q hq:
J(q,(q-1)/2)=Jc_q(q/2).
scalarResidualPeriod_physical_value q hq:
J(q,(q-1)/2)=Lambda(5q/2-1)*Lambda(q/2)^2*Lambda(1-3q/2)/2 +Lambda(q-1)*M_q(-q/2).
M_q remainsliteral3termprincipalcutoffmoment; oldLambda(q-1)!=0.
scalarResidualPeriod_physical_eq_diagonal_iff q hq: actualphysicalJ equalsdiagonalIFFM_q(-q/2)=0. Notvanishing/nonvanishingproof. SOURCE RIGHT-HALFrestrictionReq>.5 remains explicit! DoNOTextendagreementtoallq merelybecauseK isentireinTESTINGparameter.

continuedAngularSourceProjection_physical_value q hq branch a w t:
ACTUALoriginal angularintegral atuphys = reducedCoefficient(physicalRateqbranch)w a(continuedOnset...)t * [fullJphysicalabove] +SUMiFin3 continuedCutoffRadialCoefficient q branch w a i t *scalarCutoffBoundaryValue(uphys)(principalExponentq i).
AllthreeoriginaldifferentialcutoffchannelsRETAINED; noenergy/boundary/sourcefitpremise. Fullphysicalangularsourceidentified, notoutgoinginverseoradjointpair.

## Exact next hard obligation
Original causal joint response must be continued to outgoingphysicaldomain while retainingactualradialendpointcondition andFULLmodularangularoperator. Proveagreementwith jointWaveResponse onoriginalpositive-frequency overlap. Existingcausalresponse/operator-domainLaplaceidentityandoriginalradialGreenbridges exist (frontiermapreadonly, hb-qnm-parameter-continuation currenthardtargetlines104+). Source meromorphy andfullangularvalue NOWclosed; continuation ofresponseinverse, physicaladvanced/adjointleftresidue, evaluationofitscompleteprojection andnonzero/nonremovablepole stillopen. Independentlyselectedopposite-half-planeenergyinversedoesnotidentifyoutgoingcontinuation. No pole survival followsfromsourcevaluealone. Spin-two/AIMEreconstructionandindependentHawking-clock++extinctionremain. DoNOTrepeatparameterregularityorperiodcontinuationwork.

Usefulnextread: ThetaCuspHawkingBMPhysicalAngularCutoffCalibration.lean (filenameverified; notreadthisturn), actualcutoffformulaalreadyknown; BMJointSourcePrincipalData definesprincipalExponent; BMJointSourceGradientReduction definesreducedCoefficient; BMJointSourceFullForcingContinuation definescontinuedCutoffRadialCoefficient. Could factorphysicalcutoffΛ(q-1) becauseΛq=0, butthatdoesnotclosephysicalinverse/leftresidue byitself. Needtargettrueoutgoingresponseobstacle, avoidanothergenericreceiver or normalizedFokasreplacement.

## Docs
New docs/drafts/pipeline/3-formalized/hb-native-physical-quotient-pairing.md contains completepaperproof, scope andauditincludingglobalstaticfailure.
Active docs/drafts/pipeline/1-in-progress/hb-native-square-residual-mellin-value.md now titledHBoriginalphysicalsourceandoutgoingresponse, regularityclosedandnexttrueoperator/leftresiduetarget.
Updated hb-qnm-parameter-continuation.md completeperiodsection andold3-formalized/hb-native-period-continuation.md nextobligation/currentstatus.
STATUSaddedF20i-z: MustproveparameterregularityofORIGINALintegralbeforeidentifyingitsvaluewithcontinuedformula; cannotinferfrompointwiseabsoluteconvergence; cancelclearingfactoronlywherenonzero; retainsourcedomainrestrictions. ExactnewLeanevidence/cardlink. FrontiermapNEVERedited.

Prior memory mem:hawking_bm_native_period_continuation_2026_09_09 contains old8leaves33theorems andJc/Mq/Wdefinitions.

## Lean details
Open scopedContDiff toparse infinity inheight_cpow_contDiffOn. norm_add₃_le hasimplicitarguments(usebare). DifferentiableOn_const takesexplicitconstant. Multiplicative norm_le_norm_add_const_of_dist_le' iswrongforComplex; additive versionNOapostrophe, or use norm_le_norm_add_norm_sub' anddist_eq_norm. isOpen_ne takesnoContinuousargs; use(showIsOpen{x:R|x!=0}fromisOpen_ne).preimagecontinuous_im. ContinuousAt.comp shouldexplicit(f:=funv:Complex=>v+.5) toavoidcommutativewrongunifier. simp only[Pi.mul_apply] before rweventualpointwiseproductvalue. Open D4BMModularCore forphysicalRate. NevertrustautoImplicit errors. Narrowcanonicalauditlean_lib must roots=[exactmodule],globs=[exactmodule], notempty; dummycachepackagesroot/globsEMPTYtoavoiddependenciesbuild. Linknewcanonicalartifactsintoprivatecachebeforeaxiomprobes, sincecachepathsearchprecedesownauditoutput.