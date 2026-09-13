# Collision geometry under a moment-preserving source interaction

## Question and objects

Does varying the compensated product interaction near the observed entry/return intervals encounter an ordinary fold of a double-zero curve, a triple zero, or neither? A fold makes continuation in one source parameter fail without making the spectral zero triple. A triple zero instead requires a local description involving three zeros. The earlier return trajectories did not determine which geometry occurred.

The source is multiplied by `1+lambda*(a*h1+b*h2)+kappa*lambda²*a*b*h12`. The functions h1,h2 use cosine frequencies (2,4,6) and (3,5,7), have coefficient absolute sum 1 and positive highest coefficient, and annihilate source mass and second moment. The product h12=h1*h2−c0−c4*cos(4*x) annihilates the same two moments. Parameters and their independently recomputed higher-precision versions are saved. The signed direction (a,b) is normalized to Euclidean length 1. The transform has the exact algebraic form `F=X+lambda*D+kappa*lambda²*W`, retaining every deformation component.

Here q=5 and the real primitive character is periodic with residue values (0,1,-1,-1,1). Its source on x>=0 is `K5(x)=2*exp(x/2)*sum(n>=1) chi5(n)*exp(−pi*n²*exp(2*x)/5)`. Its undeformed cosine transform is the completed character L-function at s=1/2+i*t. Coefficients h1,h2,h12 are recomputed using K5. The region is 19.4<=t<=21.4 in direction (-,+). The positive multiplier bound does not assert positivity of K5.

## Outcome

Both grid resolutions found the same two admitted critical points. All 28 cell/resolution tasks completed without a recorded screen or root-solver error. A further point near 20.56444 had kappa≈1.33421 and remained outside scope and unvalidated.

| Numerical classification | t | lambda | kappa | F_tt / scale | F_lambda / scale | F_ttt / scale |
|---|---:|---:|---:|---:|---:|---:|
| ordinary double-zero parameter fold | 19.4962438558 | 0.0180586422244 | 0.338402350916 | 0.00078301438144 | -1.63372768087e-160 | -0.0132773512665 |
| numerical triple zero | 19.5607518089 | 0.0180816112076 | 0.33821214966 | -2.22275874949e-162 | -0.0667335151577 | -0.0122080289644 |

Each derivative is the derivative of the unnormalized transform divided by the same positive scale `exp(-pi*t/4)*(1+t*t)^0.875`; it is not a derivative of the normalized transform. This distinction matters for the third derivative away from a triple zero.

At the first point, F=F_t=F_lambda≈0 while F_tt is nonzero. The independently differenced collision chart has nonzero kappa second derivative, supporting an ordinary parameter fold. At the second, F=F_t=F_tt≈0 and F_ttt is nonzero, supporting a numerical triple zero. The determinant of the derivative of (F,F_t) with respect to (lambda,kappa) equals `lambda²*(D*W_t−D_t*W)` and is numerically nonzero at both. Thus the triple-zero candidate has two independent source-parameter directions; it is not an apparent triple produced by a degenerate choice of parameters. Exact existence and a certified local cusp theorem remain unproved.

In the table order, the scaled unfolding determinants are approximately −0.00288275 and −0.00298193; the chart values of kappa second derivative are −0.276915 and +0.273207. The two finite-difference formulas agree within 1e-55 at 160 digits; changing both precision and step changes their values by less than 1e-35.

The sufficient multiplier bounds are below 0.025626. The two distinct kappa values differ by about 0.0001902. Their proximity does not establish that either lies on the continuation of the previously tracked return witness, or that either causes the observed return interval.

## Validation and limitations

The two resolutions use 8 and 16 subintervals per cell. The collision chart eliminates the two source parameters through `A=X*W_t−X_t*W`, `B=D*W_t−D_t*W`, `C=X*D_t−X_t*D`, `lambda=-A/B`, `kappa=B*C/A²`. Both kappa prime and F_tt are monitored. Zeros or poles of A/B need separate charts; sign-change searches are not exhaustive. No global discriminant classification is claimed.

All admitted candidates were refined at 100/160 digits with higher-precision moment coefficients; maximum difference in (t,lambda,kappa) is below 1.383e-99. Independent 190-digit character-source quadrature checks F,F_t,F_tt,F_lambda,F_ttt at each candidate and at height+.125. Maximum discrepancy in the stated scale is below 1.788e-190. These are agreement checks, not interval error enclosures. The source sum uses 40 terms and x<=4; previous cutoff refinements informed this choice.

An extra nested-differentiation check timed out after 35.180 seconds and returned no candidate rows; its owned process group was cleaned. A bounded retry checks the unfolding determinant and computes kappa second derivative from symmetric differences of kappa and kappa prime, using steps 1e-20/1e-32 at 100/160 digits. The two formulas and precisions agree within the reported numerical tolerances. Both supplement records are retained, and both times are charged to the same family cap. The timeout is a validation-method failure, not evidence against either candidate.

Total guarded wall time, including both supplements: 302.845 seconds; recorded worker time: 1242.656 seconds; worker time lost in the terminated supplement is unavailable and excluded from this lower-bound total. The original family uses at most 14 processes and the supplement at most 4, with native numerical threads 1. Outputs were downloaded and original hashes verified before reporting. REMOTE-SHA256SUMS preserves each original manifest. No Lean builds or new premise-free formal certification.

## Consequence for HB/RH and next discriminator

The conductor-5 observation shows that these source constraints permit both ordinary two-zero folds and a numerical three-zero collision. A model restricted to an isolated pair of zeros may therefore miss local geometry under mixed interventions. The positive salvage is an explicit candidate and a nondegenerate two-parameter description that can be checked analytically. Neither carrier comparison nor moment preservation identifies the complete HB causal action or supplies its extinction mechanism. These are deformed completions, not alleged off-line zeros of undeformed zeta or L-functions.

The next discriminating question is whether the triple-zero branch is actually connected to the known entry/return witness, including any exchange with a third original zero. A local cubic normal form alone cannot answer that ancestry question. Repeating generic square-root/cubic splitting or enlarging an unqualified no-hit screen would be predictable or insufficient.

## Reproduction

Run from this folder in an isolated Python environment with the versions recorded in environment.json: `python guard.py experiment.py`. The input source parameters, finite regions, cached ordinates, code hashes and corpus-search coverage are retained. This reruns the frozen family and overwrites its output files, so use a fresh copy to preserve this record. Classification supplements, where present, have their own guards and frozen protocols.
