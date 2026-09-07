# EDQ averaged Barban–Vehov divisor source and full cumulative covariance — 2026-09-07

RH/EDQ goal ACTIVE, NOT achieved. Continuation baseline8,954,341tokens. Prior turn classified progress (exact cutoff average+adaptive current RH receiver); this turn made verified source/covariance formalization progress. Full chain Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH. NO numerical experiment this turn: finite algebra outcomes predictable. NO subagents, commits, pushes, full builds, umbrella builds, or older-leaf reaudits.

## New closed leaf — DO NOT REBUILD OR REAUDIT
`formal/GaloisForLFunctions/RHTower/EulerDeletionAveragedDivisorCovariance.lean`,288lines, namespace`RHTower.DeletionAveragedDivisor`, imports EulerDeletionCutoffAverage and Sieve.GrahamMeanSquare.14publictheorems6definitions5privatehelpers. WiredonceRHTower.lean.

Definitions:
18 arithmeticCoeff(X,M,d)=ifd<=M then taper(X,M,d)*mu(d) else0.
22 divisorSource(X,M,k)=sum_(d|k) arithmeticCoeff d.
121 errorIncrement(X,M,k)=[k=1]-divisorSource k+DeletionCutoffAverage.harmonic X M.
135 cumulativeEnergy(c,T)=sum_(1<=n<=T)(sum_(1<=j<=n)c(j))²/[n(n+1)].
139 cumulativeKernel(T,j,k)=1/max(j,k)-1/(T+1), NATURAL max forced insidecast.
258 fullErrorEnergy(X,M)=stepGram(1-modular,1-modular), same fullcarrierintegral/weightedseries, nofinitecutoff.

Publictheorems:
29 arithmeticCoeff_eq_weight_difference:for1<=X<M, ALL d including0,(w_M(d)-w_X(d))/(logM-logX). w=Sieve.barbanVehovWeight.
53 divisorSource_eq_difference:ALLk,(b_M(k)-b_X(k))/L,b=Sieve.barbanVehovCoeff,L=logM-logX.
60 divisorSource_one=1.
65 divisorSource_eq_vonMangoldt_sub:1<k<=M,g=(Lambda(k)-b_X(k))/L.
71 divisorSource_initial_zero:1<k<=X,g=0.
97 sum_divisorSource_eq_floor:ALL X,M,n, sum_(k<=n)g(k)=sum_(d<=M)a(d)*floor(n/d). Includes everycoordinatebeyondsupport.
110 modular_eq_centered_divisor_sum:only X<=M,ALLn,F(n)=sum_(k<=n)g(k)-n*Havg.
125 error_eq_cumulative:onlyX<=M,n>=1,1-F(n)=sum_(k<=n)errorIncrement(k).
172 cumulativeEnergy_eq_covariance:ANYreal c,ALLT,E=sum_(j,k<=T)c(j)c(k)*(1/max(j,k)-1/(T+1)). Exactfinitedoublecovarianceallunequalpairsretained.
206 errorEnergy_eq_covariance:actual averagederror specialization,onlyX<=M.
218 sum_sq_divisorSource_le:1<=X<M<=N, sum_(k<=N)g(k)^2<=2*(B(M,N)+B(X,N))/L² withB(Y,N)=N*4*coprimeLogMoebiusConst²*(1+logY)+(YlogY)². ActualGrahammomentdonor,explicitfloorerrorretained. This controls unsummed coefficient squares, NOT fullcumulativecovariance.
237 abs_modular_le:1<=X<M,EVERYn,absF(n)<=M by positivefiniteaverageofrawbounds.
262 hasSum_fullErrorEnergy:1<=X<M,genuineHasSum fullerror²/((j+1)(j+2)) atj+1 =fullErrorEnergy.
269 fullErrorEnergy_eq_covariance_add_tail:for1<=X<M,ALLT, fullerrorenergy=actualfinitecompensatedcovariancethroughT + tsumi>=0 error(i+T+1)²/[(i+T+1)(i+T+2)]. NOinfinitedoublesumexchange,NOdiscardedtail.

Fiveprivatehelpers span_pos,divisorSource_eq_truncated,reciprocal_weight_sum,cumulativeKernel_eq_sum,abs_error_le.

## Meaning/current mathematical gap
The exactaveragedsourceisnowconnectedtoBarban–Vehov/Grahamdonors, and throughouterM itexplicitlyexposesLambda minustheinnerpartialdivisorsource. Accumulationcreatesmaximum-index temporal covariance, whereasGrahamcontrolsordinarycoefficientmean-square(the lcmquadratic arisesfromdivisor expansionbeforeaccumulation). Cannotdrop temporalunequalpairs or harmonicdriftbeforeestimating. Thisisnotano-go/retirement: potentialstronger covariance transferisstillopen. No boundofthatcumulativecovarianceattheinnerXsubpowerscaleisproved. No generalfullarithmetic-energy-to-averaged-currenttransferwasaddedthisturn. OldrawcurrentHardytransferexistsbutis specializedto rawNcoefficients. RHremainsunproved.

## Validation complete
Scratch finalhandle76376exit0,empty /tmp/edq_covariance.check.log. Earlierinitialscratch29826failedonlyredundantomega inIcc/Icoequalityandunusedhyp;33632failedonly1+1vs2 proofandunusedhyp. Fixedandremovedunneededhypothesesratherthanwarning suppression.
Finaltargeted `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionAveragedDivisorCovariance`handle24597exit0. ONLYnewleafbuilt7.3sec,13149cachedgraphjobs. Olderwarningreplaynotrebuild.
New-onlyaxiomaudithandle98390exit0;all20publicdeclsexactlypropext,Classical.choice,Quot.sound. /tmp/edq_covariance.axioms.log. Noaddedaxiom/admission/numericalcertificate.
ONElint4033exit1: EXACTLY3concurrentunrelatedunwiredmodules ProductAFEContour,ProductAFEIntegrand,RectangleThreePoleResidue. Subsequentgitstatusverifiedall3untracked,umbrellaquerynoneofthem. OwnEDQmodulewiredonceandnolinterror. DO NOTCLAIMGLOBAL LINTPASSED. Preserveforeignfiles. Nonewlintneededunlessexternalstatechanges.
ONEsearch-indexrefresh11changed0removed,33192files404650declarations3957gapmarkers. /tmp/edq_covariance.index.log.
Scopedcheckspassed scratch=source,20axiomcoverage/stdsets,noadmission/numericalcertificate,whitespace,uniqueumbrella,doclinks,stage,singleleafbuilt,lintlimitedexactly3foreignerrors.
AllownedLeanhandles terminal;processcheckfoundnoneowned. Removed /tmp/edq_covariance.lean and/tmp/edq_covariance_axioms.lean. Logsremainunder/tmp/edq_covariance.*.log. NOremoteprocessstartedthisturn.

## Docs
Cardmovedto`docs/drafts/pipeline/3-formalized/edq-averaged-divisor-covariance.md`,exactsource/formula/Grahamdonor/fulltail/statusandhonestlintlimitation. Old3-formalized/edq-cutoff-averaging-transfer.mdRemainingproducerlinksnewcard. FrontiernewparagraphafterCutoffAveragebeforePrimitiveHardyandEDQrowadditionCURRENTstateonly. STATUSnewrouteindependentMUST-RECOMPUTE-COVARIANCE-AFTER-ACCUMULATION:incrementvsaccumulatedenergypairkernel,compensationbefore squaring,transfercostandfulltailretention.

## Lean technical notes
- `Sieve.card_filter_dvd_Icc {d N}(hd:0<d)` fromSieve/DivisorSumMeanSquare.lean:16 availablethroughGrahamimports. ConvertsfilteredIcccardtoN/d. Finsetsumconstantnsmulhandlesfloorreversal.
- GenericdivisorSource_eq_truncated uses sum_subset ofdivisors.filter(d<=M),zerooutsidebyarithCoeff; setextwithNat.mem_divisors,Nat.pos_of_dvd_of_pos.
- Globalmodularidentity uses existingnatMod_div_eq_div_sub_natDiv andharmonic_eq_taper; no sourcepathalgebra duplication.
- `show Finset.Icc L T=Finset.Ico L (T+1) by ext n; simp` alreadycloses; trailingomega errors.
- reciprocalweightsum rewrites1/[n(n+1)]=1/n−1/(n+1)onpositiveIcc thenFinset.sum_Ico_eq_sub andexplicitFinset.sum_range_sub' withf(n)=1/(n:Real). Fullrangezero-term cancelsbetweenthetwosums.
- CovarianceproofextendsallinnerIcc1n intocommonIcc1T viaifj<=n; expandtwosums/square,swapfinite3sums,filterbyj<=n andk<=n equalsIcc(maxjk)T. Noanalyticexchange.
- HasSumstepGram withboundederrorgivesfullenergy; sum_add_tsum_nat_addT splitandIcc/rangeinduction. `simp[f,Nat.cast_add,Nat.cast_one,add_assoc]`left1+1vs2;ringafterwardcloses.
- Weakenedmodular_eq_centered_divisor_sum,error_eq_cumulative,errorEnergy_eq_covariance toX<=M (no1<=X orstrictXMneeded). Nontrivialnormalization/positiveaverageboundsstill1<=X<M.

## Corpus investigations this turn
Research BarbanVehovoffset20limit40 inspectednamesoutof454decl65modules(modulecap2total120); manydifferentiatedshort/longlcmenergydonorsforLevinsoncriticaldetector,notcurrentprimitive.
ReadGrahamMeanSquarewhole155linesactualtheoremN>=X,C*N(1+logX)+(XlogX)^2. ReadBarbanVehovWeight1–90exactdefshead/correctedheaderremainingclaimnotused. ReadSelbergDiagonalUpperAsymptoticdeclinventoryand570–end:actualSelbergdiagonal/logN→1; sourceprooflcmform.
ReadMollifiedDeviationHeadVariance1–230(first230oflargerfile):linearMollifierDirichletCoeff=w_M/logM,mollifiedProductCoeff=b_M/logM,headunit+Lambda/logM;criticalheadcoefficientenergy→1/2andDirichletmeanvaluewindow. Itdoesnotboundourcompletecumulativefield. BatchedoutputtruncatedsomeCoprimeLogMoebiusOneRate1–105; donotclaimreadall. Thatfilehasratioharmoniclog identityandrate toward1.
ReadEulerDeletionMobiusPrimitiveEnergy1–135,158–177,235–330,declinventory:rawspecificAbeltailHardySchurtransfer. Couldgeneralizeatnextuseinsteadofassuming italreadyappliestoaveragedsource.
Research'mollifier norm'first30of55(38modules),mostlypointwisecutofforcriticalDirichletmean-square,noneyetfullcarrieraveragebound. 'mobius logarithmic average'4hits3modules includesInfiniteMobiusSignedChannelcontractiveallprime shifts, different source. 'mobius logarithmic primitive'4hits4modulesincludesGammaCoPoisson sources(rawlogenergyalreadyowned). 'barbanVehov summatory'4decl1module(sharpGrahamexisting); 'barbanVehov'filterMollified4decl3modules. Noexternalnoveltyclaimed.

## Next
Pursueactualfullcompensatedtemporalcorrelationbound orbuild generalboundedfinite-sourceHardytransferthenreduceadaptivecurrentreceivertothisfullarithmeticcovariance. Avoidmerely repeatingfiniteidentitiesorbad mean-square estimatesasRHproofs. Noexperimentwithoutnew frozen uncertain question; presentformalidentitiesarepredictableandnotexperimental targets.
