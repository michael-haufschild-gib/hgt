# EDQ weighted fifth circulation — verified checkpoint 2026-09-07

RH remains unproved/unfalsified; persistent goal ACTIVE. Prior and current turns made verified progress. No external blocker or route retirement. Continuation baseline5,237,737tokens.

Full chain: Euler deletion -> exact complex zero balance -> signed arithmetic separation -> off-line exclusion -> RH. This turn closes actual weighted polygon/word identification and exact source absolute-convergence zero test. No signed location restriction yet.

## New complete leaf
formal/GaloisForLFunctions/RHTower/EulerDeletionWeightedFifthCirculation.lean,400lines,namespace RHTower.DeletionJointCirculation. Imports JointNilpotentWitness,QuasiShuffleSecondConvergence,Mathlib.Integrals.Basic.19publictheorems,6publicdefinitions;4privatelemmas+1privatecoordinate. Wired RHTower umbrella. DO NOT rebuild/re-audit.

For arbitrary complex increments a,b:
pathProduct=orderedProduct(chainExp(an)(bn)).
endpoint a N=sum n<N an.
segment x y a b=integral0..1 (x+t*a)(y+t*b)^3*a dt.
Exact polynomial:
a*x*y^3+(a²*y³+3a*x*y²*b)/2+
(3a²*y²*b+3a*x*y*b²)/3+
(3a²*y*b²+a*x*b³)/4+a²*b³/5.
Rows00,01,02=1,x_N,x_N²/2.
Write U_N,V_N,W_N for actual entries03,04,05.
FINITE sumsegments=-6W_N+6y_NV_N-3y_N²U_N+x_N²y_N³/2.
No endpoint cancellation supplied.
source_factor_eq_chainExp/source_product_eq_pathProduct identify literal moduli2/3 arithmetic weights at EVERY cutoff incl incompleteblocks. q1meansmod2,q2meansmod3.

- segment_eq,prefix_first_coordinates,finite_circulation_eq_boundary:finite bridge.
- circulation_limit_of_closed_endpoints:matrixconvergence+bothendpointlimits0 ->sumsegmentlimit -6U05.
- sourceSegment s n:actualsegment at actual cumulative deletionprefixes.
- norm_segment_le <=(normx+norma)(normy+normb)^3 norma.
- norm_sourceSegment_le_at_zero:Re s>0,s!=1,ζs0 ->normJ_n <=(A1+1)(A2+2)^3(n+1)^(-5Re s),
 A_q=eulerDeletionAbelTailConstant q s=2q(1+norms/Re s).
- sourceSegment_summable_at_zero:abs summableforRe>1/5.
- source_fifth_word_at_zero:exists actual unitproductlimitU, fullsourceconvergesU,abs summableJ,U05=-(tsumJ)/6. No critical-line premise.

## Exact source zero test
segmentResponse removescommonfactora;segment=a*R.
segmentResponse_tendsto:x->X,y->Y,a,b->0 ->R->XY³.
norm_two_jump:norm actualmod2jump=(n+1)^(-Re s) EXACT alln.
source_endpoint_tendsto:actualprefix->eulerDeletionDirichletSum q s,Re>0.
source_response_tendsto:Ractual->D1(s)D2(s)^3.
endpoint_product_eq_zero_of_summable:Re>0,Re<=1,abs summableJ ->D1D2³=0.
ProofnonzeroL->eventuallynormR>=normL/2;firstpowertailcontradicts p-series.
source_endpoint_value:Re>0,s!=1 ->Dq=(1-complexEulerDilationFactor(q+1)s)ζs. Polecancellationjustified.
one_sub_dilation_ne_zero:p>1,Re s<1 ->1-dilation!=0 since normdilation=p^(1-Re s)>1.
sourceSegment_summable_iff_zero:unconditional subtypeforall1/5<Re s<1,Summable(normactualJ) iff ζs=0.
This detectszeros throughoutstrip, DOES NOT selectRe=.5. Neither positivitynorRHfollowsfromhighermomentabsoluteconvergence.

## Audits DONE
Scratch44093 exit0noddiag.
Leafbuild37625 exit0ONLYnewleaf5.1s,8799cached/replayedjobs,nofull/umbrella.
Axioms56212 exit0all25newpublicdecl standardpropext,Classical.choice,Quot.sound;privatelemmasinclosure.
Lint19937 exit0 PASSED existingfilesizewarnings. Priorconcurrentunwiredissuesweregone atthisaudit.
Index50491 exit0ONCE2changed0removed. Scopedgitdiffwhitespacepassed;newfilewhitespaceverified.
Scratch/tmp/edq_circulation.lean,/tmp/edq_circulation_axioms.lean deleted.
Allownedcheck/build/axiom/lint/indexhandlesterminal. Propercomm-basedprocessinspection->0ownedLean/lake.
Logsretained/tmp/edq_circulation.api.log,.check.log,.build.log,.axioms.log,.lint.log,.index.log.
No numerical experiments/premises,addedaxioms,admissions,unsafe,native_decide.

## Docs
3-formalized/edq-weighted-fifth-circulation.md:dependency-closedpaperproof,finiteidentity,absiffzeroproof,audits;tempinprogresscardmovedthere.
Frontiernewparagraphafterjointfifthphase+EDQrowCURRENTstate.
STATUSnewMUST-DISTINGUISH-ZERO-DETECTION-FROM-LOCATION.
Continuingpolygoncardnewexactweightedrelationsection.
No commits/push;concurrentworkpreserved.

## Next gate
Independent signed/relative comparison of actualcomplexcirculation/fullchronologicalsource at strict-rightzeros. Do not count newabs-convergenceiffzero as RH or higherwordvanishing. Unitmatrixlimitdoesnotforceentry05nonzero. Genericfiniteendpointidentity+fullabsolutezerocarryavailable.
Usecorpusstartingpoint,onlynewaxioms,oneownedforegroundLeanprocess,scratchthenleafonlyfinalbuild. Nosubagentsauthorized.

## Lean tips
prefix isreserved;usepathProduct.
Complex.hasDerivAt_ofReal absent;(hasDerivAt_id t).ofReal_comp works.
Fin.sum_univ_succ leavesFin.succindexsyntacticdifferences;norm_num[...] <;>ring_nf<;>rfl resolves.
Continuous.tendsto takesINPUT U,notoutputcoordinate.
rw norm_mul mayhitnormofendpointconstantbeforesegment; useisolatedidentityorsimp only.
rpow_natCast:firstcongr1 toisolatepower;otherwisehitsunrelatedcoefficientcube.
PointfreeTendsto rewrite useh.congr(funN=>finiteidentity).
From-6U=J,use linear_combination -he/6 (negative sign).
Finalfile400lines,nodiagnostics.