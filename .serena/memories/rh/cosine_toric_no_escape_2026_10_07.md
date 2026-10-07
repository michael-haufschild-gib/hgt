# Current handoff: regular rational repairs certified; toric no-escape proof candidate
Goal active: unconditional Lean RH/disproof, not achieved. User arxiv2610.05474 prompt stale/ignored by explicit instruction. Apply hgtl7 each turn. No positivity/energy/frequency/Fourier/spectral mechanisms, bounds/estimates or numerical experiments. Exact geometry/local analytic orders/qualitative covering/compactification allowed. No subagents. One own foreground Lean at a time, terminal exit before next; no umbrella/full builds/heartbeat increases/commits. Skill and Serena instructions previously read. This turn obeyed sequential Lean throughout.

## New strongest open work: N and E
READ active card:
docs/drafts/pipeline/1-in-progress/logarithmic-toric-no-asymptotic-values.md
It contains complete proposed paper mechanism, dependencies, false shortcuts and next formal targets. No Lean for N/noescape/infinite fibers/E yet. Do not mark proven in Lean or retire basepoint route before exact certificate.

General Conjecture N: closed affine algebraic curve B in C² whose projective infinity misses RP¹, Laurent polynomial L with 0 strictly inside 2D Newton polygon. F=L(exp(iu),exp(iv)) on normalization B has no finite asymptotic value along a continuous escaping path.

Paper mechanism:
1. Exponential restricted to B is proper into (C*)². A compact torus set has finitely many relatively compact logarithm charts. On a subsequence escaping lifts differ from a compact chart lift by real deck lattice (2pi Z)², so any projective escape direction is real, contradicting B∞∩RP¹ empty. Equivalent exact Imu=-log|X|. Use boundary incidence, not growth estimates or positive form criterion.
2. Compactify torus by adapted Newton toric surface. Finite level family L-a has finite fixed boundary edge-root points, no toric vertices: constant coefficient varies only interior because0 interior. Exponential properness excludes interior cluster; connected path tail must converge to one finite boundary point.
3. At edge normal(m,n), character X^n/Y^m→nonzero. Its local logarithm differs from i(nu-mv) by one constant integral deck shift on connected tail. Thus nu-mv finite limit; projective direction[m:n] real, contradiction. Multiple edge roots/special levels need retained audit; exact character limit enough, no normal-form assumption of family.
Important: not true for arbitrary escaping sequences; fibers can infinite. Continuity fixes log sheet. F itself not proper.

Concrete no-general-toric-library first target:
c=pi/9, alpha=4pi²/27, B:u²+v²=2c²;
u²=alpha(w+1/12), v²=alpha(-w+1/12).
X=e^(iu),Y=e^(iv); L=X+1/X+Y+1/Y=2S(w), S=T(w)+T(-w).
P1xP1 finite-level equation X²Y+XY²+X+Y-dXY=0 has only4boundarycorners, independently of finite d.
At(0,0)/(∞,∞):Y/X→-1. Atmixedcorners:XY→-1. Invert∞coordinates, local equation linear partX+Y, derivative1; workswhen d→finiteA.
Connected loglift then u-v oru+v converges; identity (u+v)²+(u-v)²=4c² preventsescape (or B∞=[1:±i] nonreal).
Asymptotic wpath lifts to B after avoiding finitebranchpoints±1/12.

Proposed full E proof:
- nofiniteasymptoticvalues S by above.
- S transcendental: infinite exact0fiber h=n+1/2, r=sqrt(81h²-1), w=(3/2)i h r, u=pi h+i pi r/9,v=-pi h+i pi r/9. u-v oddpi =>cosu+cosv0. Squaredwvaluesnonconstantquartic =>infiniterange. Snotidentically0 via existingdistinctdiagonalvalues2T(w_n).
- Classical Iversen: transcendentalmeromorphic finitelymany a-preimages =>aasymptotic. Hence each finiteSfiberinfinite. Known published theorem, not unresolved premise, but notfoundLean yet.
- Each realSfiberfinite: escaping realw gives oneof u,vreal, henceoneofX,Yunitcircle. Butfinitelevelescape mustapproachcorner,bothcoords0or∞, impossible. Realfibercompact+analyticdiscrete=>finite. No explicit interval/numericalbound.
- S=2a,a=T0 theninfinitelynonrealw. AllT=a pointsreal by existing source_eq_fiberValue_iff, so Tw!=a atnonrealroot, T-Tref!=0. Canonicalbasepointrepair has genuineholomorphic1 there. Excludesonebasepointrepair, notallnegative-sign rationalrepairs/C2/RH.
Keep constraintaudit explicit: projective real/nonreal incidence is geometric; do not silently replace by estimates,DCA,Nevanlinna,Rouche,coshpositivity. N proof still underhostileaudit/generalnoveltyunverified. Fourcornerspecialization priority.

## Completed cycle D, fully formalized
Card moved:
docs/drafts/pipeline/3-formalized/rational-cosine-diagonal-repair.md
Theorem: forall bivariate complex polynomials P,Q with norm identity Pxy*Pyx=Qxy*Qyx, regular normalization Paa=Qaa!=0 at ANY a, rational pullback P(Tw,T-w)/Q(...) has infinite set of nonreal points with analyticity and value1.
Normalization anywhere ondiagonal stronger thaninitiala=T0; samefactorizationpaperproof.
Diagonal polyp²=q² =>p=±q, regularone excludesminus. Infinite distinctcosine diagonalcoordinatesavoidfinite qzeros.
BRIDGE;classicalparents;significantnoveltyunverified.

New Lean:
formal/GaloisForLFunctions/HTGeometry/CosineInfiniteDiagonal.lean (~107lines)
namespace GaloisForLFunctions.HTGeometry.CosineInfiniteDiagonal
radius n=sqrt(81*(n+1:R)^2-1)
point n=(3/2)*I*(n+1:C)*(radiusn:C)
lift n=pi*(n+1)+I*pi*radiusn/9
radius_sq, radius_ne_zero, point_im, point_nonreal, point_coincidence, source_point, lift_im
source_point_injective, point_injective
infinite_coincidences_avoiding p hp atline94.
Proof usesexactcosdeckrelationimagparts; pfinitezeros andinjectiveimages, noquantestimates.
Directfinalauditpassed and targetedbuild3401jobs.

formal/GaloisForLFunctions/HTGeometry/RationalCosineDiagonalRepair.lean (~108lines)
namespace ...RationalCosineDiagonalRepair
Bivariate=MvPolynomial Bool C; eval p x y= MvPolynomial.eval(funb=>condb y x)p
diagonalp=eval₂HomPolynomial.C(fun_=>Polynomial.X)p
diagonal_eval, diagonal_sign line38, diagonal_eq_of_regular_one
pullback p w=evalp(Tw)(T-w);repair p q ratio
pullback_entire viaMvPolynomial.induction_on
infinite_off_real_one_fiber line81 (all explicit hyps as above)
Directcheckedno warnings,targetedbuild3403jobs.
Fouraxiomaudits bothleaves onlypropext,Classical.choice,Quot.sound.

## Completed cycle basepoint boundary certificate (not E)
Activecard:
docs/drafts/pipeline/1-in-progress/cosine-basepoint-secant-repair.md
Correctcandidate s=(Tw+T-w-2a)/2,t=(Tw-T-w)/2,V=(t+i*s)/(t-i*s).
Equivalent -(Tw-a+i*(T-w-a))/(T-w-a+i*(Tw-a)).
Earlierrealcoefficient -(Tw-a)/(T-w-a) haswrongconjugationlaw; don'tmistakeforfullcompetitor.
Vgenericdiagonal=-1,filledV0=1. Bothreflections. Full1fiberstillnotLean.

Newleaf:
formal/GaloisForLFunctions/HTGeometry/CosineBasepointRepair.lean (~150lines)
namespace...CosineBasepointRepair
divided=dslope source0 (filledderivative)
numerator=bw+b-w+I*(bw-b-w)
denominator=bw+b-w-I*(bw-b-w)
repair=ratio
divided_entire viaHasFPowerSeriesAt.dslope at0, dslope derivativeaway
divided_mul
scaled_coordinates line35: wN=Tw-T-w+i*(Tw+T-w-2T0), wD=...-i*...
source_deriv_zero_ne, source_deriv_zero_conj, divided_conj
numerator_entire,denominator_entire,neg_coordinates,conjugate_coordinates
repair_reciprocal,repair_conjugate,denominator_zero_ne,repair_zero,repair_analyticAt_zero
source_zero,source_point_ne_zero_value usingcosdeckimagcontradiction
divided_point_ne_zero,divided_neg_point,point_denominator_ne,repair_point=-1
basepoint_escape line137 nohyps:
repair0=1 &AnalyticAt0 &bothfunctionalidentities &infinite{nonreal,holomorphic,repair=-1}.
Certifiesnegative generic sign underremovednormalization+bothreflections. DoesNOT refuteextensionofD'sCONCLUSION:Ecouldstilltrue.
Directchecknowarning,targetedbuild3402jobs.
Threeaxiomaudits scaledcoordinates/dividedentire/basepointescape onlystd3axioms.

All3newleaveswiredonceHTGeometryumbrella alongsideCosineReflectionCoincidence. ParentlabeledcardandfrontiermapupdatedD. NoRHclaim.
NoownedLeanprocessrunning; allhandles terminal.
Latestindex66851 terminalexit0 wroteLEAN_API/GAPS/OVERVIEW and2changed0removed.
Latestlint96558 terminalexit1: exactly5unrelatedunreachablemodules ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra. Noownleaferrors. Allnewfilesgitdiffnoindex--checkemptyoutputs(exit1expectednewdiff); trackedscopeddiffcheck0.
Scratchcleanup follows beforefinal.

## Corpus/literature
DparentHilbert90alreadypriorcard.
Basepointdeepquery20+20allinspected irrelevant; partialfalse,noerrors,oldercoverage,compilerincomplete.
Noescapequery20+20allinspected irrelevant; partialfalse,noerrors,currentcoverage,compilerincomplete. Proposedfiberentropyingredientfalseapplicability.
LexicalIversen total0; rg HTGeometry/mathlibComplex noIversenhit. Needbroadenfinitevalence/inversesingularities/pathcontinuation/Picard—notbroadsemanticrepeats.
Primary:
Bergweiler–Eremenko https://www.math.purdue.edu/~eremenko/dvi/bergo.pdf pp2 inverse/asymptoticdefinitions,pp16 Iversenfinitepreimage=>asymptotic explicitly. Noquantitative/finiteordercorollaryimported.
Juyal–Moody https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=931852 pp1-3 classicalLaurentellipticfamily; nonsingularparameter!=0,±4. NoMahlermeasure/rankdependency.
Heittokangas–Ishizaki–Tohge–Wen https://arxiv.org/pdf/2202.01574 v2 (2022), abstract/contents/algebraic+ODEsections inspected;find'asymptoticvalue'none. Coverspolynomialphases;oursalgebraiconconic. Nonewunresolvedexternalproblemadopted. Nnoveltynotverified.

## Mathlib implementation notes
Verifiedvia/tmpnamechecks:
MvPolynomial.induction_on.{0,0}, polynomial_eval_eval₂.{0,0,0};
Polynomial.finite_setOf_isRoot.{0},funext.{0};
Set.infinite_range_of_injective,Infinite.sdiff,Finite.preimage,Infinite.image, sq_eq_sq_iff_eq_or_eq_neg.
Set.Infinite.image (hi:InjOn f s) (hs:Infinite s). Dot hi.imageinjective works hs.image hi.
dslope_same,dslope_of_ne,sub_smul_dslope,differentiableAt_dslope_of_ne all.{0,0};
HasFPowerSeriesAt.has_fpower_series_dslope_fslope.{0,0}.
Avoid simp[eval,MvPolynomial.eval]loop; use changeexplicit eval₂ + congr functions.
pullback_entire induction use changeDifferentiable(funw=>MvPolynomial.eval_(p+q)),simp onlymap_add,exacthp.addhq; blanket simpwon'tunfoldfunction asneeded.
Nat.cast_nonneg usesparameterαnotR.
Complexim simp automaticallycancelsπ inpluscosdeckcase butnotminus; checkresidual.

Anti-theatre/anti-lazinesspostedtwicecurrentturn: no significantnoveltyclaim, concretecheckedboundarynewinproject,hardEattackratherthanonlyinfrastructure;noeffort-skips. Need repeatnewturnperhgtl7.
