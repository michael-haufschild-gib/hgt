# Weighted Mellin source and logarithmic repair window

Goal ACTIVE, no budget; RH and [R] remain OPEN. Last automatic turn made progress: one audited Lean leaf and new paper bounds/remainder analysis. No subagents authorized/spawned. No mathematical computations this turn (only Lean/file tools); no remote jobs started. Prior context: `mem:research/chronological-boundary-moments-2026-09-06`. Do not mark goal complete/blocked for hard math.

## New formal leaf — COMPLETE component, not full no-go theorem
formal/GaloisForLFunctions/RHTower/ChronologicalWeightedMellin.lean, 214-ish lines.
Imports narrow SquarefreeMoebiusNormalization, Mathlib.Analysis.MellinTransform, Mathlib.MeasureTheory.Integral.DominatedConvergence.
namespace RHTower;8 public declarations +3 private helpers:
1 chronologicalMobiusWeightedSource w t = tsum_(n:Nat) (moebius n:Complex)*w((n:Real)*t).
2 chronologicalMobiusWeightedSource_hasMellin:
   Re s>1, MellinConvergent w s -> HasMellin actual source s (mellin w s * zeta(s)^-1).
   Absolute integrability of actual source established BEFORE interchange.
3 chronologicalMobiusWeightedSource_mellin: equality-only corollary.
4 chronologicalMobiusWeightedSource_eq_sum:
   t>0, w=0 beyondtheta, theta<(N+1)t -> exact range(N+1) finite sum.
5 chronologicalMobiusWeightedSource_eq_zero:
   theta>=0,w=0 beyondtheta,t>theta ->actual source0.
6 chronologicalMobiusWeightedSource_measurable: measurable w ->measurable actualsource.
7 chronologicalMobiusWeightedSource_norm_bound:
   C>=0,|w(x)|<=C forx>0,w=0 forx>1,t>0 ->|source(t)|<=2C/t.
8 chronologicalMobiusWeightedSource_locallyIntegrable:
   same boundedness/support + measurablew ->LocallyIntegrableOn source (Ioi0).

Private helpers: mellin_norm_dilate exact normintegral scaling a^-Re(s);
integrable_tsum_of_norm_integrals (complex,Realmeasure), absolute normseries via ENNReal lintegral;
mobius_weight_summable, from LSeriesSummable_moebius_iff.

Validation:
Scratch lake env lean /tmp/ChronologicalWeightedMellin.lean passed.
Final LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ChronologicalWeightedMellin passed; ONLY requestedleaf compiled,42sec. Tool reported3160 dependencyjobs in graph, not3160 compiledjobs.
Umbrella import wired afterChronologicalHarmonicCharge, exactlyone.
All8 #print axioms in /tmp/chronological_weighted_axioms.lean ->only propext/Classical.choice/Quot.sound.
Authoritative scripts/formal_tools.py lint passed existing sizewarnings. Index refreshed; corpusresearch returnsall8. git diff --check ownscope passed.
Artifacts /tmp/chronological_weighted_manifest.json,axioms.txt,lint.txt,index.txt.
Scratch probes /tmp/ChronologicalWeightedMellinProbe.lean and WeightedNames.lean intentionally had unknown-name errors; do not confuse with finalproof.
All Lean sessions exited; finalownedpath ps audit no matches. No live handles.
Now13 chronological leaves /162 public audited total; previous12 unaffected.
Certificate docs/drafts/pipeline/3-formalized/chronological-weighted-mellin.md.
NO fullfixed-space no-go capstone, no growingjet capstone, no RH proof. Do not call thoseformalized.

## New paper result [BRIDGE K-window], fullproof in growing-moment paper
For ANY unitbounded row, exact half-prefix throughM=floor(N/2), exact harmoniccharge0:
K=M+1, q=e^-t.
Sharper absolute Lambert tail:
|r_N(t)| <= 2e^-Kt/[(1-e^-t)(1-e^-Kt)].
For N>=4, delta=logN/N:
0<delta<=1, K>=N/2, e^-Kdelta<=N^-1/2<=.5.
1-e^-delta>=delta/(1+delta)>=delta/2.
Hence on t>=delta, |r|<=8 e^-Kt/delta.
Integrate squared: <=64 e^-2Kdelta/(2Kdelta²)<=64/log²N.
Thus tailnorm <=8/logN.
For growing-jet source full[R] is EQUIVALENT to actual moving-window estimate
N^-1 integral_(u0..logN) |r_N(u/N)|² du ->0.
Must NOT replacegrowing uwindow withfixedcompact. NoPNT/momentassumptionused in tailbound beyondexacthead/charge/unitbox.
This result still PAPER-ONLY.

## Actual remainder attack, paper exact formulas and positive local bound
Classical primary source verified search+open:
https://dlmf.nist.gov/4.36.E3, coth partialfraction.
h(z)=.5-2z sum_(n>=1)1/(z²+(2pi n)²).
After odd Taylor polynomial degree2m-1:
R_m(z)=(-1)^(m+1)2 z^(2m+1) sum_(n>=1)1/[(2pi n)^(2m)(z²+(2pi n)²)].
Finitegeometric identity valid allz>0, notjustTaylor-radius range.
|R_m(z)|<=4 z^(2m+1)/(2pi)^(2m+2) byzeta(2m+2)<=2 (integralcomparison).
Exact momentrow:
r_N(t)=cosh(t)-1-[sinh(t)-sum_(j1..m)t^(2j-1)/(2j-1)!]+sum a_k R_m(kt).
On0<=u<=1,t=u/N, unitcoeff:
||r_N||L2([0,1/N)) <=
e/(2sqrt5 N^(5/2)) +
e/[(2m+1)! sqrt(4m+3) N^(2m+3/2)] +
4sqrtN/[(2pi)^(2m+2)sqrt(4m+3)].
This directabsolute majorant needs a quantitative rate onm; sufficient
m-logN/[4log(2pi)]->+infty, not suppliedbydiagonal.
Onu0..logN, arithmeticmajorant =
4sqrtN (logN)^(2m+3/2)/[(2pi)^(2m+2)sqrt(4m+3)].
ForlogNlarge it growswithm. Thus this absoluteTaylor bound cannotclosefullwindow. NOTalowerboundonactualerror, NOTrefutationof[R]/source. Need estimate signedarithmeticremainder before termwiseabsolutevalues.
Paperproofs recorded in docs/drafts/pipeline/2-fully-proven/chronological-growing-moment-source.md. Positive localbound/exactremainder notLean yet. No route retired.

## Notes updated
Main docs/drafts/pipeline/1-in-progress/chronological-bounded-repair-attack.md totalsandnewwindowcomponent.
Focused chronological-boundary-moment-repair.md hascompactnewfacts andnexttarget.
Paper chronological-finite-tail-obstruction.md linksnewLeancomponent butretainsfullpaper-only status.
Paper growing-moment-source.md hasK-windowproof andexactremainder/localbounds.
Certificate3-formalized/chronological-weighted-mellin.md created.
External concurrentagents/commits continue; umbrella hasadditionalexternalimports. Preserveall. We didnotcommit/push.
Noexperimentsrerun; lastK-testarchivecomplete frompreviousmemory.

## Next exact formal work (planned, notdone)
Need generalweighted criticalzero obstruction for actualsource:
boundedmeasurablew positive, support<=1, rho.re=.5,zeta(rho)=0,mellin w rho!=0 ->
actualsource is NOT littleo(t^-1/2) as t->0+.
Then heattransformseparation, C1 Riemann Gramprojection O1/N, actualresidualobservation ->fullfixedspacefloor.
No fullweightedboundary scratch createdyet beyond completedWeightedMellin.

Useful implementation path considered:
- actualsource localintegrable/norm2C/t/topzero nowavailable.
- w itself localintegrable onIoi0 by boundedmeasurable andfiniteIoo neighborhoods.
- mellin_differentiableAt_of_isBigO_rpow_exp supplies holomorphy:
  w boundedat0 ->Re>0; actualsource littleo half ->Re>.5.
  Topzeroeventually =>IsBigO exp(-t).
- zetaResidueUnit from RHTower/ZetaLogDerivResidue.lean is analyticallcomplex, agrees(s-1)zeta except1.
  Use actualMellinidentity onRe>1 and identitytheorem viaresidueunit toextendproducttoRe>.5.
  Existing model: MobiusLaplaceCriterionFrontier.lean1243..1302.
- Need Abelboundary delta*mellin(source)(rho+delta)->0. Existing BaezDuarteMobiusCriticalTailObstruction.lean503..616 is private Laplace finalvalue forCONTINUOUS f; cannotdirectlyapply tojumpingcompactweight. Better prove physicalsplit directly forlocallyintegrable/measurable boundedsource:
  littleo gives|f(t)|<=eta*t^-.5 on0<t<=a<1.
  Lowintegralnorm at rho+delta <=eta*a^delta/delta.
  High a..1: normf<=2C/t, t^(delta-.5)<=a^-.5 fordelta>0 andt<=1, so uniformfiniteconstant; beyond1 f0.
  Multiplybydelta, chooseeta then delta small. No continuityneeded.
  Atcriticalzero zetaResidueUnit(rho)=0 and derivative slope bounded => productzero, contrarymellinw(rho)!=0.
  Existing finalderivativepattern BaezDuarteMobiusCriticalTailObstruction.lean797..863.

Verified THIS toolchain APIs:
MellinConvergent.comp_mul_left ha : iff.
mellin_comp_mul_left w s ha ; mellin_const_smul.
hasSum_integral_of_summable_integral_norm hi hsum.
Measurable.tsum / AEMeasurable.tsum ; .aestronglyMeasurable.
enorm_tsum_le_tsum_enorm;
ofReal_integral_norm_eq_lintegral_enorm hi;
ENNReal.ofReal_tsum_of_nonneg hnonneg hs.
No built-in integrable_tsum_of_summable_integral_norm or MeasureTheory.integrable_tsum identifier; privatehelper innewleafprovesit.
IntegrableOn.of_bound measure_set_lt_top hmeas C hbound.
Ioo_mem_nhds,mem_nhdsWithin_of_mem_nhds, LocallyIntegrableOn defIntegrableAtFilter.
Nat.floor_le hnonneg, Nat.lt_floor_add_one realarg.
norm_sum_le isunqualified, NOTFinset.norm_sum_le.
Integral_normsimpa for HasMellin requiredexplicit [IntegrableOn]unfold inaddition[MellinConvergent].
DO NOT rw[<-hp] whenhp=rpowproduct=1: rewrites1 insideexponents too. Insertcalcproductthenrw[hp].
globalC>=0 branch normsource0: use simpa[norm_zero] using div_nonneg...; positivityalonefailed.
Mathlibfiles Analysis/MellinTransform.lean; MeasureTheory/Function/LocallyIntegrable.lean (notIntegral/LocallyIntegrable).
Mathlib.Analysis.SpecialFunctions.Integrals.Basic hasintervalIntegral.integral_rpow.
Asymptotics.isBigO_zero; IsLittleO.bound; EventuallyEq.isBigO.
No new norm_num/native_decide/decide computationaltactics inleaf.
OneforegroundLeanprocess; lakeenvlean scratch; finalleafonly lakebuild--old; printaxioms scratch;nofullbuilds.