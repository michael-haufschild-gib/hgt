# BAG controlled shrinking physical cutoffs

01ax. HARD physical-profile regularity route. Corpus:
HTGeometry/SmoothWeight and SmoothBlockWindow; actual sharp comparison
ChiPrimeGaussianCubicSharpEdges. Search70658 nonpartial66019files,
coverage1248917/current1248922,noerrors,refreshincomplete. All20candidates
and20source statements inspected; ranked hits mostly irrelevant. Exact
rg/source inspection found the block window and derivative APIs.

Canonical relative cutoff eta_delta=blockWindow(1+delta,2-delta,delta),
0<delta<1/2. Smooth,compact,range[0,1],zero outside(1,2),one on
[1+delta,2-delta]. Existing corpus gives all pointwise derivative bounds
C_k/delta^k and integrability. Missing first-variation uniformity is NOT
implied by that whole-band estimate: integrate only two transition strips.
Every positive derivative vanishes on the plateau by local constancy,
and outside the support by the existing support theorem. Their union
has length at most2delta. Thus integral|eta_delta^(k)|<=2C_k delta^(1-k).
This is dependency-closed paper proof; Lean audit pending.

For the actual physical family choose delta=N^-3/4 and eta_N(x)=eta_delta(x/N).
Must additionally attach the original sharp/smooth error to this SELECTED
family, and prove all Gaussian/log/tau amplitude derivative budgets.
The existing existential choice uses an abstract ContDiffBump and supplies
no quantitative derivative control; do not transfer bounds to that choice.
No physical cancellation or RH theorem claimed.

01ax progress: relative derivative budgets and physical support/plateau
scratch3704 PASS. Production ChiCubicControlledCutoff40228emptyPASS,
154lines/API5 before final index/axiom. Original selected sharp/smooth
error scratch96304 PASS. A common private band-comparison lemma now
replaces duplicate edge-cardinality proofs; optimized full scratch audit
running. No raised resource limit or full/umbrella build. Selected-family
attachment not marked closed until production/final axioms pass.

01ax CLOSED: selected relative cutoff plus ALL positive derivative L1 budgets
and physical band properties; its ORIGINAL sharp/smooth error*log²N/N->0
now attached to that same explicit family. ChiCubicControlledCutoff151lines/API5;
ChiPrimeGaussianCubicSharpEdges adds selected error theorem and shared
private band comparison, preserving and reauditing prior public results.
Production40228/38864emptyPASS; finalcombinedaxiom7869 all6standard3;
index61984PASS/APIrows/importonce; lint62496terminal1 threeunrelated
unreachable(ZetaSquareStirlingAFE,ZetaSquareStirlingCarrier,UnframedPromoterNoGo),
362warnings,noownederror. P2/P3/frontier updated. No resource-limit override.
Active next scratch /tmp/bag-reciprocal-fourier-01ax.lean: generic exact
reciprocal Fourier step. Actual height interchange/amplitude regularity,
full moving-profile energy and subsequent arithmetic/RH still open.
