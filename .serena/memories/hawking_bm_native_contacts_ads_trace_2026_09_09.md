# HB actual characteristic contacts and retained AdS master trace

Goal ACTIVE. RH and full physical extinction UNPROVED. This turn PROGRESS: 5 new verified theorems in2installedmodules plus explicit paper twolegcontacts, retainedmasterAdStrace andfinite-timecandidateAdScurrentlimit. Noexternalblocker. Do not markcomplete/blocked becausehard.

Instructions persist: everyturnfullchain literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH; hardesttarget2Ω(B(p,p)/2,B(m,m)/2)=0 withallindependentSS/SV/VV,temporal,horizon,AdS,cuspterms. Constructiveconjecture/proof/fail/pivot, no repeated no-go/scaffolding. Frontier READ ONLY. Analyticalonly,no mathematicalcomputations. Broadcorpusresearch singleterms/--any(defaultAND). OneforegroundownedLeanprocess; scratchlakeenvlean; finalexactleaflakebuildonly; noolddeps/full/umbrellas. New-onlyaxioms. Noagentsauthorized.

## Installed this turn — DO NOT re-audit
Namespace RHTower.D4BMNativeCircle; filesunderformal/GaloisForLFunctions/RHTower/.
`ThetaCuspHawkingBMNativeCharacteristicContact.lean` (~203lines),public3:
- mean_second_at_zero: actualm''(0)=scalarLaplacian(fullSquarePotentialq)![X,expk]/2.
- argumentFirst_tendsto_characteristic: interiorM' expression tendsfromZ>1 toΔQ/2.
- angularKernel_right_derivative: HasDerivWithinAt actualangularKernel ΔQ/2 (Ici1)1.
`ThetaCuspHawkingBMNativeCausalSourceContacts.lean` (~108lines),public2:
- nativeRiemannKernel_direct_source_contact: h:Ioi0,xXkreal; righty derivative ofR(h-x+y,x,y)aty=x-h/2 equals sinh(h/2)/(coshx cosh(x-h/2))*ΔQ.
- nativeRiemannKernel_image_source_contact: h:Ioi0,x:Iic0; righty derivative ofR(h-x+y,x,-y)aty=-h/2 equals sinh(h/2-x)/(coshx cosh(h/2))*ΔQ.
These areRiemannkerneltraces,beforemasterfactor-1/(2uw).
Bothscratchsourcespassedwithoutwarnings. Finalexactleaves4.7sec/3.6sec,3942frozenoldowndeps; noolddepcompiled. All5newpublictheoremsaxiomsONLYpropext,Classical.choice,Quot.sound. Installed2sourcesand4mandatoryolean/ileanartifactsbytecompared;2umbrellaimportsappended,noumbrellabuild. Indexupdatedandbothmoduleentriesverified. StaticlintPASSED,141oldsizewarnings; whitespacepassed. AllownedLean/Lakeprocessesterminal. Owned/tmp/hb-native-contacts.mfuUloG3REMOVED. No mathematicalcomputations.
Cards:
- docs/drafts/pipeline/3-formalized/hb-native-characteristic-contacts.md exactnewscope.
- docs/drafts/pipeline/1-in-progress/hb-native-circle-green-kernel.md updatedconstructivepaperformulae(7)-(11),first-jetformalstatus.
- docs/drafts/pipeline/3-formalized/hb-native-circle-riemann-kernel.md updatedfirstjetstatuslinkonly; nooldLeanaudits.
Frontier/STATUSnotedited. Newfactsroute-specific.
Priorcontext: `mem:hawking_bm_native_circle_kernel_2026_09_09`, `mem:hawking_bm_complete_current_common_source_2026_09_09`.

## Shorter first-characteristic proof actually formalized
Qactualhalf-square, m(d)=nativecirclemean. Private laplace_circle_smooth provesactual(ΔQ)(circle(d,θ)) C∞in(d,θ)fromQalljetsandcoordinateformulaΔQ=Y²(QXX+QYY). Privateaverage_continuous usescompactdomination on[t-1,t+1]×[0,2π]. ThusA(d)=mean_d ΔQ continuous.
DivideexistingS²m''+SCm'=S²A byS for d≠0. Continuouslimit0forcesm'(0)=0. HasDerivAt.tendsto_slope_zero gives m'(d)/sinhd→m''0. DividetheDarbouxequationbyS²; limit gives2m''0=A0=ΔQ. Composewitharcoshapproaching0puncturedfromZ>1; actualfirstderivatZ>1verifiedfromchainrule. `hasDerivWithinAt_Ici_of_tendsto_deriv` extendsfirstderivativeintophysicalclosedchart.
PrivateedgeArgument(a,b,x,y)=1+2sinha*sinh(y-b)/(coshx coshy). For a≥0 mapsIci b toIci1; edgeArgument(b)=1; derivativeaty=b2sinha/(coshxcoshb). Directinvariant=edgArg(h/2,x-h/2,x,y); image=edgArg(h/2-x,-h/2,x,y). Thisprovesoriginalcoordinatecontacts,not suppliedtraces.
All-ordersrightjetsVolterraproofstillpaper; J2=Δ(Δ-2)Q/8notyetLean. DoNOTuseordinary`deriv angularKernel1`: totalReal.arcoshextensionbelow1doesnotgenerallygivecorrecttwo-sidedderivative.

## New PAPER exact twolegcontacts
Currentcardfixesλ=(s+1)(s+2)=ρ(ρ-1),t=-s-3.
A0=(5λ-6)/4,C=((4λ+1)(λ+2)-(λ+4)Δ)/8,K=(7λ-2-2Δ)/8.
Afterconjugationby1/u,P†(R/u)=[a(u)R+b(u)Ru]/u,
a=A0+3Ku+(C+K)u²,b=Ku²(1+u).
Forpositiveingoingdelayh,η=tanh(h/2),T(u)=(u+η)/(1+ηu).
Z±=coshh+sinhh(u-w)+(±1-coshh)uw.
DirectcausalkernelH(T-w)M(Z+);imageH(η-w)M(Z-).
SmoothtwolegactionF=au aw M+[au bw Zw+bu aw Zu+bu bw Zuw]M'+bu bw ZuZw M''.
Canonicaldirectcontact:
δ(T-w){[bu T' a(T)-au b(T)-bu T'b'(T)]Q+bu b(T)T'Zw(u,T)ΔQ/2}
-δ'(T-w)bu b(T)T'Q.
Imagecontact=-δ(η-w)au b(η)Q; subtractimagefromdirect.
δ' meansderivativeofdisplayedargument; f(w)δ'(T-w)=f(T)δ'+f'(T)δ. TangencyZu+T'Zw=0makesonefirstjetterm,not2.
Thesearelocaldistributionsinopenradialsquare; source/targetradialendpointsandcuspstillretainedseparately. Firstjetdataformal; distributionidentitynotformal.

## IMPORTANT constructive normalization correction: full AdS master trace
Scalarconjugatedcontactsdirectminusimagecancelatu0,butMASTERhas-1/(2uw). Cannotsetmasterboundaryvalue0fromthat. Retainlinearcoefficientinu.
FullmasterkernelG(u,w)=-[H(T(u)-w)M_Q(Z+)-H(η-w)M_Q(Z-)]/(2uw).
Z+-Z-=2uw, T'(0)=1-η². Atfixedh>0,localdistributioninsource0<w<1, letZ0=coshh-sinhh*w, H=H(η-w),Sh=sinhh:
G_AdS=-H M'_Q(Z0)-δ(η-w)Q/Sh=(1/Sh)∂w[H M_Q(Z0)].
Theδarisesfrommovingdirectendpoint. Factor1/2included. Angularcurrentweightnotincludedhere.
OriginalP†before1/wconjugation=ã(w)+b(w)∂w,ã=A0+4Kw+(C+2K)w²=a+b/w. TargetP†boundaryreducesA0 becauseGhasasmoothextensionasdistributioninuandb(u)=O(u²).
CompleteTWO-PRODUCERAdStrace:
A0{H[b(w)Sh M''_Q(Z0)-ã(w)M'_Q(Z0)]
+δ(η-w)[b(η)ΔQ/2+(b'(η)-ã(η))Q/Sh]
+δ'(η-w)b(η)Q/Sh}.
ThisincludesendpointshiftfromSMOOTHterm; takingonlyu-limitofexplicitcontactmissesit. Multiplybyderivedscalarcurrentweight-Δ(Δ-2)onlywithretainedcuspGreenboundary. ThisisNOTyetfullEinsteinpairing.

## PAPER finite-time candidate AdS flux
Forfinitev,compactangularregion,actualcandidatecausalSCALARresponseφfromnativekernelhasfinitecompactdoubleintegralwithsmoothmovingendpoints,φ(u=0)=0. Paperall-ordersrightsmoothnessMimpliessmoothφinu≥0includingh0corner. Dividebyu(Hadamardone-variableformula)andtakeoriginalcoexactangularderivative:Ψ=r coexactφ smoothatAdS. OriginalsourceS=2coexact(PFs)finite.
MIXEDCURRENTingoingformulaMUSTretaintemporalterms:
ω_r=u²[(Ψ_v-(1-u²)Ψ_u)·(AΦ-SΦ)-(Φ_v-(1-u²)Φ_u)·(AΨ-SΨ)].
Reason∂r|t=-u²∂u|v+(1/f)∂v. Bracketfiniteforfinitev+compactangularregion,hencecandidatecurrent→0atAdS. DoNOTomitΨ_vterms orclaimmastervaluezero. NoexchangeAdS/infinite-time/cusplimits. Noidentitywithadmittedphysicalresponseyet. Distributionlimits,C∞causalintegral,dividedmasterregularity,currentlimitallPAPERnotLean.
Thisgivesaconcreteboundaryformulaandfinite-timecandidatefluxresulttouseinhardpairing. Hardremainingphysicalinverseadmission,horizon/temporal/cuspassemblyandindependentSS/VVcoefficientsstillopen. Don'tendnextturnwithmoregenericno-gos.

## Existing positive source reduction found; do not re-prove
`ThetaCuspHawkingBMFullSourceOnsetReduction.lean` ALREADY provesfulloriginalsourceastwowaveimages+explicitfixedχ' transitionpulse, withfullAngularFieldinverse. `fullSourceOnset_wave_identity`and`timeOriginalForcing_gradient_absorption`areexisting. Cubicparticular-profileconjecturethisturnmatchedalreadyknownreduction; reusedratherthaninstalledduplicate. Source-onlycausalhorizonformulaandpulsebridgeI_s'-2sI_s=K_sareanalyticalinhb-causal-horizon-circle-kernel.md. Fixedclockfinitepairingthereeq8andregularcircleTaylorassembledpairinginhb-causal-circle-taylor-cancellation.md eq13remainhardactualintegrals; noidentitysettingthemzeroproved.

## Lean details for reuse
- ContactimportsnativekernelandMathlib.Analysis.Calculus.FDeriv.Extend. Average_continuousprivategenericcompactcontinuitycopy~20lines; laplace_circle_smoothactualQ~30lines. Nochange/rebuildoldNativeCircleMeanneeded.
- hs1=(contDiff_infty_iff_deriv.mp(mean_radial_smooth...)).2; hs2likewise. Explicitx0 inhs.contDiffAtforstandaloneHasDerivAt.
- `simpa only [ContinuousWithinAt,Real.arcosh_zero] using (Real.continuousOn_arcosh1...).mono Ioi_subset_Ici_self` requiredunfoldingContinuousWithinAt toTendsto.
- `sinh_ratio_limit`: dividecomplexslopesf(d)/dandsinh(d)/d, simplifyPi.divviaexplicit`change`thenfield_simp[ofReal d ne0].
- Derivativeedge sinh(y-b): need `.comp b (h := fun y : ℝ => y-b)`toavoidunifierchoosingb-yfromb-b; simplifierFunction.comp_applybeforezerovalues.
- Set.Ici/Ioi membershipnotautomaticallyvisibletolinarith; `change`inequalityorhavehp:0<h.val:=h.property.
- cosh_add/subedgeidentitylinear_combination -hs,not+hs.
- Anonymous`have := @Name`polymorphicAPIsneedexplicituniverselevels.{0,...}inNames scratch.
- Exactfrozenauditasprior: 3942existingowndepshardlinkedbyileanimports; externalcachesstubsno globs;2mainlean_libeachroots/globexact;copynewfirstartifacttostubbeforesecondbuild,then5-onlyaxioms. Ole/ilemandatory,private/serveroptionalabsent. AlltemporaryworkspaceREMOVED.
