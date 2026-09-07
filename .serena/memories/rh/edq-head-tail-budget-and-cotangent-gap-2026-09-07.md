# EDQ head/tail diagnostic and cotangent estimate gap (2026-09-07)

RH goal remains ACTIVE and unachieved. Latest user instruction: frontier map READ ONLY; no frontier edits in this turn. This turn is diagnostic progress, not a new unconditional arithmetic bound. Do not present finite tests as asymptotics or repeat them at larger scales without a new unpredictable question. No new Lean files, builds, axioms audits, index refreshes or lint runs this turn. No subagents or commits. Existing audited head-subpower result remains valid; see `mem:rh/edq-coprime-head-subpower-2026-09-07`.

## Actual hard bound and paper attempt
Full chain Euler deletion -> exact complex zero balance -> signed arithmetic separation -> off-line exclusion -> RH. Need actual cofinal subpower current/full compensated energy, with inner scale X retained. Working card docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md updated with source estimate attempts and complete diagnostic.

Inspected primary Bettin--Conrey, Period functions and cotangent sums, https://msp.org/ant/2013/7-1/ant-v7-n1-p08-p.pdf, formula13 (printed225,PDF11), formula14 (printed226,PDF12). For fractional autocorrelation A(h,k), normalized BD Gram is A(h,k)-A(h,1)/k-A(k,1)/h+A(1,1)/(hk). Formula13 and homogeneity, g=gcd(h,k), a=h/g,b=k/g, give paper identity:
2hk G_BD(h,k)=(k-1)log h+(h-1)log k + pi[V(1/h)+V(1/k)-gV(a/b)-gV(b/a)]. Universal constants cancel. V(h/k) is -c0(bar h/k), with MODULAR INVERSE; PDF text loses bar. Do not replace mu(h) by mu(inverse h). Elementary |V(h/k)|<=C k log k still permits O(N log N) pairwise absolute budget on balanced h,k~N; no saving for full signed aggregate established. Also checked Bettin--Drappeau primary https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1119.pdf, no usable actual mu-weighted bound extracted. Coprime product mu(d)mu(e)=mu(de) leaves restricted-divisor rectangular weights, not free complete convolution. Do not build a representation/receiver module merely for these identities without an actual estimate.

## New bounded RunPod diagnostic COMPLETE
Archive docs/drafts/pipeline/2-fully-proven/computations/edq-gcd-head-tail-budget-2026-09-07/ has PROTOCOL.md, experiment.py, full_source_results.json (copied original input), INPUT_SHA256SUMS, results.json, run.log, analysis.py, analysis.txt, SHA256SUMS, REPORT.md. Inputs frozen before run; reused complete C_r intervals from prior edq-gcd-gram-variation experiment, no long tail recomputation. All numerical work and analysis on authorized RunPod, 8 Python workers/native pools1, timeout60seconds, actualwall0.0381194seconds. Python3.8.10, numpy1.24.4, LDmantissa63.

Same8sources M64,128,256,512 raw X=M, averaged X=M/4 (exact log taper). Actual finite head H_r from sum_(k<=X) residue Gram, retaining literal coordinates. E_q^head multiples-channel squares; H_r=sum_l mu(l) E_(rl)^head. J_q=sum_(q|d)a_d/d; K_r=sum_l mu(l)J_(rl)^2; P_r=K_r sum_(k<=X)k/(k+1). Tail T_r=C_r-H_r inherits archived fulltail intervals. Every group H,K,P,H-P,Tlower/Tupper,Clower/Cupper stored. Tests at fixed threshold4: A=(sum|H_r|+sum|T_r|)/D<=4; B=(sum|P_r|+sum|H_r-P_r|+sum|T_r|)/D<=4.
Results A interval ; B interval:
64raw [2.330877,2.355351];[7.849413,7.873887] B FAIL
64avg [1.089432,1.124429];[2.689256,2.724253]
128raw [1.930228,1.949774];[4.920854,4.940401] B FAIL
128avg [1.732207,1.758516];[3.595035,3.621345]
256raw [1.698434,1.714650];[3.904535,3.920751]
256avg [1.913486,1.934353];[3.282046,3.302913]
512raw [1.575490,1.589326];[3.688107,3.701942]
512avg [1.704080,1.718590];[2.638721,2.653231]
All A pass, all other B pass. Finite result: splitting polynomial/corrected head can lose budget inside head; does NOT refute asymptotic subpower bounds or establish that head/tail splitting remains affordable. At raw64 Habs4.169010 versus Pabs6.260743 + correctedabs9.180997, tailabs[.592281,.642274].
Controls: direct gcd Gram at64 everyr vs inversion2.17e-19; literal initial F(k)=kH-1 discrepancy4.93e-17; headnorm reconstruction6.51e-19; harmonic reconstruction3.13e-21. Inherited analytic fulltail allowance<=.05. Floating margin1e-7 sensitivity, NOT interval certified.

## Remaining mathematical issue
Corrected coprime head is subpower (previous Lean theorem), but retained polynomial and complete later tail lack required joint estimate. Finite data now cautions against assuming polynomial mainly cancels against later tail; head-internal cancellation matters. Complete signed raw head equals sum_(k<=M)(k H(M)-1)^2/[k(k+1)], so raw uniform/cofinal estimates require harmonic control too. Corpus BaezDuarteMobiusPrefixApproximation already has corresponding error-energy obstruction; no new receiver necessary. No route retired, no new route-independent STATUS entry warranted by these finite results.

## Cleanup and verification
All downloaded hashes verified; report hash appended. Working-card diffcheck passed. Remote owned /tmp/edq-gcd-head-tail-budget-20260907-root removed after /proc cwd audit showed no active process and exact9file inventory checked. No owned Lean process ever started this turn; final ps showed none. All exec handles CLOSED:90098,62285(partialupload failed before compute),75661(correctedupload),71412(run),75297(download),60320(analysisupload),71197(download),83070(cleanup). Initial local cp used wrong working-dir-relative path, corrected before execution; final frozen inputs verified remotely. No remaining scratch or remote research jobs.