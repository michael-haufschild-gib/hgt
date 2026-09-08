# CCM-FU transverse front: new exact separation and hostile source experiment

Goal remains unconditional RH proof/falsification; RH NOT solved. Goal ACTIVE. Current turn classified PROGRESS: 6 new audited Lean theorems plus bounded RunPod experiment changing next action. Frontier map READ ONLY. No commits/pushes/subagents. Other agents edit shared tree; preserve their files. No owned processes live, locally or RunPod.

## New exact theorem
File formal/GaloisForLFunctions/RHTower/MobiusDivisorTwoTransverseEnergy.lean
Imports MobiusDivisorInheritedTwoCost. Namespace RHTower.
Definition:
T(M,P)=mobiusDivisorSelectionEnergy(M,P)-F_empty²-F_{2}²
named mobiusDivisorTwoTransverseEnergy.

Six public theorems:
1. mobiusDivisorTwoTransverseEnergy_eq_sum: M>2, T equals sum of squared actual labels except empty,{2}.
2. mobiusDivisorTwoTransverseEnergy_nonneg.
3. mobiusDivisorTwoTransverseEnergy_union_two_child_inactive:
actual fresh helper primes L, p<M,p≠2, P covers every child prime <M/p+1 except2, helpers mutually child-inactive (M/p+1≤q for distinct helpers):
T(P∪L)=T(P)-Σp∈L p*(I0²+I2²).
NO balance, small-head or energy-budget premise.
4. mobiusDivisorTwoTransverseEnergy_insert_gain_union:
for any further prime q≠2, q∉P,L (quotient unbounded allowed), T cost of inserting q after helpers is EXACTLY same as before helpers.
5. mobiusDivisorTwoTransverseEnergy_union_gain_union:
for any finite additional prime set A excluding2 and disjointL,
T((P∪L)∪A)-T(P∪L)=T(P∪A)-T(P).
Already-processed primes allowed in A. Entire additional-core transverse energy function translated by one constant reserve.
6. mobiusDivisorTwoTransverseEnergy_insert_cross:
for fresh prime q<M,q≠2,
Delta_q T=2Σ_{R≠empty,{2},q∉R} F_R F_{R∪{q}}-F_{q}²-F_{2,q}².
Every signed complementary pair retained.

Proof:
existing exact two-plane energy+head-shift identities cancel all receiving terms. q inactive in each helperchild because otherwise q∈P. Hence helper packets unchanged atP+q; subtractreserveidentities. Induct on A for fullfinitecore. Exactgainformula removes{2} pairedterm from existing nonemptyenergy formula, cancels updated {2} square.

Strong implication: head balancing cannot change a positive transverse gain's sign. It can pay gain from fixed accumulatedreserve; cannot claim futuretransversecost repaired. Need independent CUMULATIVE signedtransversebudget across actualgrowingprimecore. This is not failureofRH, fixedweightmaincandidate, or alladaptiveorders.

## Frozen experiment — genuinely new question, completed once
Candidate tested: with P containing {3,5,7,11,13},2 retained and macrohelperpool initiallyunused, inserting smallestremainingprime≠2 always has nonpositiveTgain.
FourM 512,2048,8192,32768,64 deterministiccores each. Prime17alwaysretained; extra P onlyprime19≤p≤M/15, sourcewindowsaboveM/15untouched. Includes empty/full extras, prefixes, alternatingcores, seededBernoulli densities .25,.5,.75. Primarysourcequotientblockformula, independent80digitwitnessoriginaltimesumformula. This is NOT an extension/reanalysis of oldM≤32fixedweight/greedy datasets. Candidate now numericallyfalsified, not kernelcounterexample.

RunPod root@157.157.221.29 -p27094 -i~/.ssh/id_ed25519:
primary4workers numericalthreads1,0.4996054694s.
Audit1witness1.3129573166s.
Internal90s/external100s+5killgrace each; no enlargement or tuning.
No numericalresult used in Lean.

All data downloaded:
docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-transverse-front-2026-09-08/
screen.py, audit.py, summary.json, audit.json, README.md.
Hashesverifiedagainstremote; READMEhashes.
Ownedremote /root/ccm-transverse-VYcEuH and4filesremoved. /proc cwdscan confirmed owned_processes[] anddirectoryabsent. AllSSH/toolhandles terminal.

Resultpositivegaincounts:
M512 0/64;2048 43/64;8192 29/64;32768 9/64.
Firstwitness M2048 P={3,5,7,11,13} itself:
Tbefore2175.281118171437933967...
Tafter+17 2463.545537963806082780...
gain288.264419792368148813518...
diagonal4961.5003774385954956...
gain/diagonal .0581002515092393...
head−4.10785606375697;F2=3.50904117708543;bothalready≪sqrt2048.
Primary/auditgainerror1.48e−11. Flagthreshold1e−10*max(1,diagonal).
Audit highprecision FLOAT, not intervalarithmetic; no negativeLeanproofclaimed.

Mechanismpositivepairedlabels71/1207,67/1139,47/799,74/1258 etc outweigh absorbedF17²andF34². Alltermsin audit.json.
SamefixedP coregain/diagonal acrossM:
512 −.0103243338;2048 +.0581002515;8192 +.0823216326;32768 +.0899937942.
Suggests examining existing fixed-core prime-correlation limit; DOES NOT proveasymptoticpositivecoefficient. No extra computationtoinferit.

## Docs
Frozenprotocol movedfrom1-in-progress to:
docs/drafts/pipeline/5-failed/ccm-fu-transverse-front-renewal.md.
Clearlylabelled numericallyfalsifiednegativecandidate, no symbolicinterval/Leannegativeproof. Strongpositivesurvivorextractedwith6checkedtheorems; no no-go-onlyretirement.
Fullpaperdependencyclosedproof:
docs/drafts/pipeline/3-formalized/ccm-fu-transverse-reserve-commutation.md.
ComputationsREADMEseparatefromLeanproof.
Addedrouteindependentledgerentry MUST-TRACK-THE-COMPLEMENT-OF-BALANCING in universal-law-field/STATUS.md, points to exactsymbolicidentities, no numericalsignclaim.
Frontier map untouched (gitstatusmapempty).

## Validation — DO NOT repeat
All6theorems scratchPASS and exactleafemissionPASS (session44272 exit0).
One scopedaxiomaudit session18614 exit0, allonlypropext,Classical.choice,Quot.sound.
No sorry/newaxiom/computedproof.
RHTower umbrella importsnewleaf nearMobiusDivisorInheritedTwoCost. Nofull/umbrellabuild.
Indexrefreshed; LEAN_APIincludesall6+def (checked).
Singlelint --check-generated failedonlyunrelatedconcurrent:
HTGeometry.FokasLenellsLaxCompatibility
HTGeometry.FokasLenellsPlaneWaves
HTGeometry.FokasLenellsUniformization
and stalegeneratedLEAN_API,LEAN_OVERVIEW afterconcurrentwork.
Noownedproof/debterror. ScopedwhitespacePASS.
ScopedLakepackageauditstillpending becausepreviouspackageplanningexpandedprohibitedbroaddependencies; didnotrepeatlakebuild.
Removed/tmp/ccm_transverse.lean,/tmp/ccm_transverse_axioms.lean,/tmp/ccm_transverse_lint.log. NoownedLeanprocess.

## Next serious mathematical action
Fullchainactualsource→renewablereserve→exhaustiveorder→uniformO(M) signedAbel→RH.
Lastturn prescribedstream result onlyboundedquotients fixedfractionpool withKhelperspertarget+oneO(sqrtM)batch. ThisturnshowsfixedhelpersdoNOTaltertransversecorecost evenaftermanyprimeoperations. Universalforcedsmallestprimenonincreasingsign iswrong numerically. Do not recyclethat rule or claimheadbalancefixesit.
Need boundsumofpositiveactualtransverseincrements (orchooseordergivinguniformtotalbudget), alongsideheadpair. Candidate next primitive: useactualfixed-core signedprime-release coefficient to choose changingprimeorder, becausecommutationisolatesitfrommacrohelperdisplacements. Existing modules:
MobiusDivisorFixedCoreEnergyLimit.lean (allfixedPquadraticlimit, explicit4^card tailconstant; NOuniformgrowingP)
MobiusDivisorFixedCorePrimeCorrelationLimit.lean (signedprimereleasecoefficientabsolutelysummable explicitblockmasses anderrorbound)
MobiusDivisorSmallCoreInteractions.lean (nonoverlappingmixeddifferenceignoresprocessedprimesabovechildcutoffs)
MobiusDivisorRemainingFrontTransport.lean (oneforcedprimecostchargedtoOTHERremainingquotients).
Readexactstatementsbeforeuse; notallproofbodiesread.
FixedPcore17gainseemsmacroscopicacrossselectedM butformalpositiveasymptoticwouldrequireanalyticserieslowerbound+tail; doNOTtreatfournumbersasproof. Bare4^Pcardtailcouldbeverywasteful; anynewexperimentmusthaveunpredictablefrozenquestionnotconfirmtrend.

Earlierrelevantmemory ccm_fu_prescribed_stream_reserve_2026_09_08 (11prioraxiomaudits) and ccm_fu_weighted_terminal_head_barrier_2026_09_08 (21prioraudits); don'treaudit.
Noarchitecture.md/testing.md docsfoundatinit. Serenamemorieslisttopicreturns{}butreadknownmemoryworks. Serenamanualalreadyread. update_plan unavailable. Noagentsauthorized.
Leanforegroundoneownedprocess only. ComparisonspacesavoidMatroid< m token. rw Fibre_insert onlyfirstmatch; simp only [Fibre_insert,...] at* expandsbothreceivingcoords consistently.
