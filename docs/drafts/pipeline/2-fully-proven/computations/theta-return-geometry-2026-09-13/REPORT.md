# Collision geometry under a moment-preserving source interaction

## Question and objects

Does varying the compensated product interaction near the observed entry/return intervals encounter an ordinary fold of a double-zero curve, a triple zero, or neither? A fold makes continuation in one source parameter fail without making the spectral zero triple. A triple zero instead requires a local description involving three zeros. The earlier return trajectories did not determine which geometry occurred.

The source is multiplied by `1+lambda*(a*h1+b*h2)+kappa*lambda²*a*b*h12`. The functions h1,h2 use cosine frequencies (2,4,6) and (3,5,7), have coefficient absolute sum 1 and positive highest coefficient, and annihilate source mass and second moment. The product h12=h1*h2−c0−c4*cos(4*x) annihilates the same two moments. Parameters and their independently recomputed higher-precision versions are saved. The signed direction (a,b) is normalized to Euclidean length 1. The transform has the exact algebraic form `F=X+lambda*D+kappa*lambda²*W`, retaining every deformation component.

Here the literal source is `Phi(x)=exp(x/2)*sum(n>=1) 2*pi*(2*pi*n^4*exp(4*x)−3*n²*exp(2*x))*exp(−pi*n²*exp(2*x))`, with undeformed transform `Xi(t)=2*integral Phi(x)*cos(t*x) dx` over x>=0. The finite regions are 161.9<=t<=164.2 in direction (+,-), and 111.0<=t<=111.7 in direction (-,+).

## Outcome

Neither grid found an admitted critical point with lambda>0,0<kappa<1 and the sufficient multiplier bound<1. There were 28 completed cell/resolution tasks. Two ordinary root-solver failures occurred near t=111.58, one at each resolution; these intervals remain unresolved. Two distinct stationary chart points near 111.15656 and 162.97630 had negative kappa and were excluded by the frozen scope. They were not independently validated.

This is a finite sign-change screen, not exclusion of triple zeros, folds, even-multiplicity monitor roots or singular collision charts. No candidate reached the higher-precision/source-validation stages. The no-hit result does not establish a structural distinction between theta and conductor-5.

## Validation and limitations

The two resolutions use 8 and 16 subintervals per cell. The collision chart eliminates the two source parameters through `A=X*W_t−X_t*W`, `B=D*W_t−D_t*W`, `C=X*D_t−X_t*D`, `lambda=-A/B`, `kappa=B*C/A²`. Both kappa prime and F_tt are monitored. Zeros or poles of A/B need separate charts; sign-change searches are not exhaustive. No global discriminant classification is claimed.

Guarded wall time: 38.706 seconds; recorded worker time: 205.816 seconds. Up to 14 processes, native numerical threads 1. No classification supplement was needed because no candidate met admission. Outputs were downloaded and original hashes verified before reporting. REMOTE-SHA256SUMS preserves the original manifest. No Lean builds or new premise-free formal certification.

## Consequence for HB/RH and next discriminator

This finite non-detection does not remove any full-route obstruction or establish that theta forbids triple zeros. Its positive salvage is the explicit two-parameter collision chart, with unresolved brackets and singular-chart exclusions exposed. The separately run conductor-5 comparison found both an ordinary fold and a numerical triple-zero candidate, but this weak theta non-detection cannot establish arithmetic specificity. A useful next theta question must identify a specific branch or source constraint; enlarging this no-hit screen alone is not admitted. Neither calculation identifies the complete HB action or supplies source-enforced extinction.

## Reproduction

Run from this folder in an isolated Python environment with the versions recorded in environment.json: `python guard.py experiment.py`. The input source parameters, finite regions, cached ordinates, code hashes and corpus-search coverage are retained. This reruns the frozen family and overwrites its output files, so use a fresh copy to preserve this record. Classification supplements, where present, have their own guards and frozen protocols.
