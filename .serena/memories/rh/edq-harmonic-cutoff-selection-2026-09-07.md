# EDQ finite harmonic-gcd cutoff selection (2026-09-07)

Goal ACTIVE/unachieved. This turn yielded diagnostic evidence that changes next action; no new arithmetic upper bound or Lean theorem. Previous turn PROGRESS was all-gcd corrected-head theorem; see `mem:rh/edq-all-gcd-head-subpower-2026-09-07`. Frontier map READ ONLY, untouched. No subagents/commits/new Lean files/builds/axiom audits/index/lint this turn. No numerical experiment result enters Lean.

## Direct proof attempt at the actual hard bound
Need retained polynomial P(N)=headMass(N)*sum_r|K_r(N)| together with complete later tail. J_q(N)=sum_(q|d,d<=N)mu(d)/d, K_r=sum_l mu(l)J_(rl)^2. Hence sum_r|K_r|<=sum_q tau(q)J_q^2. For squarefreeq, J_q=mu(q)/q times ordinary coprime harmonic partial sum throughN/q; nonsquarefreeq gives0. Corpus Sieve/SmoothPrimeCoprimeConvolution.lean:216 primeSupportedReciprocal_mul_moebiusDiv identifies the exact coprime mask by convolution. Sieve/MoebiusHarmonicArbitraryLogRate.lean:218 exists_abs_deningerHarmonicPartial_le_const_div_log_pow supplies every fixed inverse-log rate for H(N), NOT reciprocal-cutoff saving. q1square remains actual harmonic defect; multiplying such a bound byN leaves N/log^A N. No source estimate closing cofinalsubpower produced. Earlier joint signature/full-energy identities don't supply the missing sign law.

## Completed new unpredictable diagnostic
Archive docs/drafts/pipeline/2-fully-proven/computations/edq-harmonic-lattice-cutoff-selection-2026-09-07/ (9files:PROTOCOL,experiment.py,INPUT_SHA256SUMS,results.json,run.log,analysis.py,analysis.txt,SHA256SUMS,REPORT.md).
Read scientific-method.md beforefreeze. [BRIDGE candidate], not new primary RH conjecture. Four fixedbands64..127,128..255,256..511,512..1023. S chooses least numericalmin of N H(N)^2; G independently chooses least numericalmin of P(N). Frozenparameterfreeprediction: E_F(G)<=E_F(S) in everyband, where E_F=sum_(k>=1) F_N(k)^2/[k(k+1)] and F_N(k)=sum_(d<=N)mu(d)*(k mod d)/d (same literal rawresidue carrier). Fullscan1..1023archived; no bands/precision/selectors/constants changedafterresults. This is different from previous poweroftwo gcdgroup tests and scalaronly minimum experiments.

SelectedS/G pairs and fullenergyintervals (analytic omittedtail<=.005, floatingmargin1e-7 separate):
64..127:77/78, S[1.035755973,1.040755925],G[1.159816287,1.164816239], REVERSED.
128..255:154/190,S[1.038664519,1.043664498],G[1.169433093,1.174433081], REVERSED.
256..511:390/266,S[1.038271156,1.043271152],G[1.030281832,1.035281826], supported finitely.
512..1023:859/571,S[1.036372321,1.041372320],G[.981034346,.986034345], supported finitely.
Everyfullenergycomparisonseparated. G-S head differences .113277133,.121375849,-.006198206,-.062873033.
G-S later-tail intervals [.005783229,.015783133],[.004392745,.014392714],[-.006791114,.003208876],[.002535059,.012535057]. Thus Glatertail definitivelylarger in3bands, unresolvedthird. Lastband has lowerfullenergy despite larger tail, paid by smallerhead.

## Interpretation / avoid false inference
Only strict finite selector-dominance prediction reverses. This DOES NOT refute fullenergy<=C*P(N)+subpower: such an upperbound would NOT imply minimizingPminimizesactualenergy. Do NOT retire taildominationorRHroute on this experiment. Do not interpretfiniteconstantcomparisons asdifferentpowergrowth; prior all-gcdremainder theorem alreadyrulesoutthat inference. Positive survivoralreadyclosedinLean: totalcorrectedheadremaindersubpower+totalvariationcomparison. No newrepresentation/receivernecessary.
ExactinitialsourceF=kH-1 yields headenergy=H^2*headMass-2H*sum_(k<=N)1/(k+1)+1-1/(N+1). Unit-source linearcrossterm explainsfiniteheadrankings: G78 andG190 have negativeH andlargerhead; G571positiveH=.0122273 lowersheadversusS859H=-.0001424. This is not a signlawforfulltail. Need directsame-sourcefulltailestimate; do not run another nearbyselector/ranking/budgetscan as substitute.

## Computation and validation
All mathnumerics andanalysis onauthorizedRunPod ssh root@157.157.221.29 -p27094 -i ~/.ssh/id_ed25519. 8independentenergyworkers/nativepools1, Python3.8.10 NumPy1.24.4 LDmantissa63, 120seclimit; actualwall.7775108367seconds. Totalprefixcoords24,896,646; maxT13,460,275.
Kscan exactupdate formula K_r(N)-K_r(N-1)=2(muN/N)sum_(d<N,gcd(d,N)=r)mud/d+[r=N]muN²/N². SelectedK independentlyreconstructedfromJq²inversion. Exactint64divisorincrements+cumsum(nooverflow), LD finalharmonic subtraction+energies. Globalalgebraicresiduebound B=.5sum|mud|(1-1/d)+|.5sum mud(1-1/d)|, so infiniteenergyafterT<=B²/(T+1). No uniformperiodaverage replacesactualweights.
Controlerrors: scanKsum-H²4.38e-20; independentdirectresiduevsaccum1.36e-12; closedheadidentity2.17e-19; selectedP independentinversionwithin1e-12. Minrunner-upgapsS2.02886e-8,G.00253211. Numericalrankingnotexactrationalcertificate; noformalintervalarithmetic. AllselectedharmonicgroupsJ,K andcompleteheadtailintervalsstoredinresults.

## Docs / cleanup
Workingcard docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md has new retainedharmoniccoeff+frozenexperiment+outcomesections; fullRHchainunchanged. No newrouteindependentSTATUSentryneeded; existingaggregatecorrection/taillawsalreadycovergeneralpoint. Frontier untouched. Inputsverifiedbeforecompute; downloads andanalysis hashchecked; localREPORT hashappended. Scopedworkingcarddiffcheckpassed.
Remote owned /tmp/edq-harmonic-lattice-selection-20260907-root removedafter /proc cwd audit showednone andexact8file inventoryguardpassed. NoownLeanprocessstarted. Allhandlesclosed:64277mkdir,31054upload,69762run,40396download,66803analysisupload,34361analysisdownload,85211cleanup. UnrelatedHB andCCMFULeanprocesseswerepreserved. No remainingscratch/remotejobs.