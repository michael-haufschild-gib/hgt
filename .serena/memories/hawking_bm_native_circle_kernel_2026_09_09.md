# HB: native full-source circle mean and Riemann kernel

Goal remains ACTIVE. RH and full physical extinction remain UNPROVED. This turn is PROGRESS: four installed modules, 21 new public identities, plus constructive paper proof of all right characteristic jets. Do not mark goal complete or blocked because hard.

## Instructions
Every new turn opens literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH, names hardest complete-pairing cancellation obstacle 2 Ω(B(p,p)/2,B(m,m)/2)=0, and direct attack. User requires constructive conjecture/proof/fail/pivot, no repeated no-gos or scaffolding. Frontier READ ONLY; no mathematical computations. Use corpus research broad single terms/--any (default AND). One owned foreground Lean/Lake job, scratch `lake env lean`, final exact leaf `lake build`; no dependencies/full/umbrellas rebuilt. New-only axioms. No agents authorized.

## Installed modules — do not re-audit
Namespace RHTower.D4BMNativeCircle. Under formal/GaloisForLFunctions/RHTower/:
1 ThetaCuspHawkingBMNativeCircleChart.lean (~208): denominator_pos, circle_pos, offset_radial_derivatives, height_radial_derivatives, offset_angular_derivatives, height_angular_derivatives, polar_principal, polar_connection, base_laplacian_coefficients.
2 ThetaCuspHawkingBMNativeCircleSource.lean (~331): source_smooth, source_darboux_integrand, source_base_laplacian_integrand, source_horizontal_derivative.
3 ThetaCuspHawkingBMNativeCircleMean.lean (~315): mean_radial_action, mean_laplacian_commutes, mean_darboux, mean_zero, mean_radial_smooth.
4 ThetaCuspHawkingBMNativeCircleRiemannKernel.lean (~158): nativeRiemannKernel_wave, nativeRiemannKernel_characteristic, nativeRiemannKernel_AdS.
All actual source identities with smoothness and derivative facts internally proved, no supplied source/PDE assumptions. XiZeroCopy and original point parameters remain universal parameters. Four exact final builds with3938 frozen own dependency modules,12/39/17/41sec. No old dependency compiled. All21 new public theorems axioms exactly propext,Classical.choice,Quot.sound. All4 sources and olean/ilean byte-compared and installed. Umbrella4imports appended, not built. Corpus index refreshed; static lint PASSED (141 preexisting sizewarnings), whitespace passed. Allowned Lean handles terminal. Owned /tmp/hb-native-circle.jFHv54lZ REMOVED. No staleownedprocess.

Cards:
- docs/drafts/pipeline/1-in-progress/hb-native-circle-green-kernel.md: actual analytical two-leg transfer and characteristic Volterra proof; current positive candidate.
- docs/drafts/pipeline/3-formalized/hb-native-circle-riemann-kernel.md: exact verified scope and remaining gaps.
No frontier/STATUS edit this turn; new facts route-specific.

## Exact native geometry and source
Q=fullSquarePotential q, C=cosh d,S=sinh d,D=C-S cosθ>0,E=S-C cosθ,A=S sinθ/D,B=1/D. circle(d,θ;(X,Y))=(X+YA,YB); logCircle usesY=expk. Native source is actualQ(circle).
Ad=sinθ/D², Bd=-E/D², Add=-2sinθ E/D³, Bdd=2E²/D³-1/D.
Aθ=-SE/D², Bθ=-S sinθ/D², Aθθ=-SC sinθ/D²+2S²E sinθ/D³, Bθθ=-S cosθ/D²+2S²sin²θ/D³.
Polar principal: S²Ad²+Aθ²=S²B², S²AdBd+AθBθ=0, S²Bd²+Bθ²=S²B². Polar connection S²Add+SCAd+Aθθ=0 and sameB. Base correction1+A²-B²=-2Aθ,2AB=-2Bθ.
Actual F=Q(circle): S²Fdd+SCFd+Fθθ=S²(ΔQ)(circle). Base ΔF-(ΔQ)(circle)=-2Y ∂θ[QX(circle)]. In logarithmic height Δ=exp(2k)∂X²+∂k²-∂k. Compact integration and true2πperiodicity killθderivatives.
`average F=(1/(2π:ℂ))*∫θ in Ioc0(2π),Fθ`. `mean q d X k=average(source...)`.
Proved m_radial C∞, S²mdd+SCmd=S²Δm, Δm=mean(ΔQ), m0=Q(X,expk).

## Actual interior kernel
`angularKernel q z X k=mean q (Real.arcosh z) X k`.
`argumentFirst=m'(arcosh z)/sinh(arcosh z)`; `argumentSecond=m''/sinh²-cosh*m'/sinh³`. Names argumentFirst/Second avoid collision with Source.angularFirst/Second.
Forz>1 actual first2 derivatives and(z²-1)M''+2zM'=ΔM internally proved.
`nativeRiemannKernel q h x y X k=angularKernel q (invariant h x y) X k`, invariant=(coshh+sinhx*sinhy)/(coshx*coshy), imported proven geometry from ThetaCuspHawkingBMCausalRiemannKernel.
`InteriorPoint={p:CausalPoint //1<invariant p.time p.target p.source}`.
Proved actual R_hh-R_xx-ΔR/cosh²x=0 forInteriorPoint. Characteristic h=x-y givesQ exactly. Directminusimage atx0 is0.
This is actual fullQ angular response, not spectral substitution. Not yet formal forced retarded/advanced inversion, cutoff removal, complete tensor source pairing or extinction. Every independentSS/SV/VV and temporal/horizon/AdS/cusp term remains needed.

## New PAPER PROOF: regular right characteristic jets (not Lean)
Apply circle derivation to each actual smooth Δ^jQ. Every such field has all derivatives on positiveY. Compact radius/base neighborhoods remain compact inH², so means and derivatives are continuous includingd0. Forany suchF: (sinhd*mF')'=sinhd*mΔF for d>0. Integrate fromε>0 to d; lower flux→0 by radial smoothness. Changez=coshd:
(z²-1) M_F'(z)=∫1^z M_ΔF(a) da.
Forh>0: M_F'(1+h)=1/(2+h)*∫0¹M_ΔF(1+th)dt.
RHS extends continuously toh0. Integrate back toM_F(1)=F toprove right derivative. Simultaneous induction for everyΔ^jQ gives all rightderivatives: ifall meansC^n thenstableRHS C^n, henceallmeansC^(n+1). Base derivatives commute bysamecompactargument.
DifferentiatingDarboux n timesat1 yieldsJ0(F)=F, J_(n+1)(F)=[Δ-n(n+1)]J_n(F)/(2(n+1)). InparticularJ1Q=ΔQ/2 andJ2Q=Δ(Δ-2)Q/8. Exact secondTaylor remainder M_Q(1+h)=Q+hΔQ/2+h²∫0¹(1-t)M_Q''(1+th)dt. No infiniteTaylor convergence assertion. Second jet is1/8ofsameangularpolynomial ascoexactmixedsymplecticpairing: positive contact-coefficient identification.
CRITICAL: These are RIGHT derivatives onZ>=1. Current angularKernel uses total Real.arcosh below1; do NOT assert `deriv angularKernel 1` equalsJ1 as ordinarytwo-sidedderivative. Native extensionbelow1neednotmatch. Formalize HasDerivWithinAt onIci1 orconstructexplicitappropriateextension.
Next useful direct work: formalize this actual characteristic regularity, thencombine differentiated causal indicators and twolegproducerinterior with all Einstein actioncontacts; don't stop at more kernel scaffolds. Bulk+contacts vanishing still unproved.

## PAPER two-leg common producer transfer (from current card)
Prior source/current results in `mem:hawking_bm_complete_current_common_source_2026_09_09` (already audited; no repeat).
Atfixed ingoingtimesu=-tanhx,w=-tanhy,h=v-v', Ch=coshh,Sh=sinhh:
Zε=Ch+Sh(u-w)+(ε-Ch)uw; ZuZw=(ε-Ch)(Z+ε),ε±1.
OriginalmasterGreencarries -1/(uw) times scalarwavekernel. Conjugatedtranspose P†(R/u)=[a(u)R+b(u)Ru]/u, a=A0+3Ku+(C+K)u²,b=Ku²(1+u), A0=(5λ-6)/4,C=((4λ+1)(λ+2)-(λ+4)Δ)/8,K=(7λ-2-2Δ)/8.
Smooth twolegaction: a(u)a(w)M+[a(u)b(w)Zw+b(u)a(w)Zu+b(u)b(w)Zuw]M'+b(u)b(w)ZuZw M''.
Characteristic indicators ALSO differentiate. Forh>0 b=tanh(h/2), directw∈[0,(u+b)/(1+ub)],imagew∈[0,b],bothupperZ1. Combinebothmovingendpoints andactualactioncontacts. Notavanishingtheorem.

## Lean workflow lessons
- Source C∞ proof using `source_smooth.comp` for2variablefamilies caused kernel whnf/isDefEq timeouts even1.2millionheartbeats. Successful Average private radial/horizontal/height/theta families instead derive pointwise C∞directly fromactual Q smoothness and explicit circle map using `contDiffAt_infty.mpr(fun n=>fullSquarePotential_smooth ... n)`,thencomp,pi,fin_cases,fun_prop withdenominator_pos.ne'. Don'tretrygenericcomposition kernel blowup.
- Average private general compactdifferentiationhelpers: parameterDerivative(F:ℝ×ℝ→ℂ),partial_smooth,average_hasDerivAt,average_derivative,average_second,average_finite_smooth. They areprivate; latergeneralization mayneed deliberate sourcechange+re-audit onlychanged results. Preferuse actualpublicmeanwherepossible.
- `ContDiff.deriv` unavailable. `(contDiff_infty_iff_deriv.mp hf).2` givesC∞deriv. `Real.arcosh_zero` meansarcosh1=0 (namecounterintuitive);Real.arcosh_one nonexistent. Mean hs.contDiffAt needs explicitx in standalonehave.
- Integral linearity `erw` andexplicitcomplexcoefficients preventPi.add/Pi.subdefeqfailure.
- Source comp derivatives with real→complex use `.congr_deriv` thenring, notsimpa throughmoduleinstances. Usual3realcomplexinstance disables; Average additionallydisables RCLike.innerProductSpace. `open scoped ContDiff` for∞.
- Scratchdependencies: `lake env lean /tmp/owned/Chart.lean -R /tmp/owned -o /tmp/owned/Chart.olean`,thenLEAN_PATH=/tmp/owned lake env lean dependent. Needed -R becauseoutsideprojectroot.
- Finalfrozenaudit: ownstub packagebuildDircache roots/globs[],hardlinktransitiveownoleans3938fromdirectImportsilean. Externalstubs cachebuildDirs;ClassFieldTheory usesdefaultsubdir. Mainpackageeachnewmodule ownlean_libroot/globexact. Buildexact4leavessequentially,copyeachnewartifacttostubcachebeforedependentbuild (pathprecedence). .olean/.ileanmandatory;private/serveroptionalabsentnormalnonmoduleLean. Copy8mandatoryartifacts+4sources. Everythingdeletedafterpass. No broadrebuilds.
