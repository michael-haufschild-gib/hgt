# Incidence-weighted perturbation and logarithmic damping radius

- **ID:** thim-incidence-weighted-damping
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper), Lean pending
- **Statement:** For N≥2, the radius 1/(96(N+1)(log N)²) certifies D≤−1/2 on every nonempty prefix whose radical endpoint is below 6(N+1).

## Goal

Replace repeated worst-case coefficient charging by exact divisor-incidence
counts. Retain uniformity over infinite radical fibers and arbitrary positive
powers. Full all-ε≥0 defect control remains open.

## Gates

- [x] Current-source inspection and broad corpus search.
- [x] Dependency-closed paper proof below.
- [ ] Scratch proof and actual-source Lean audit.
- [ ] Every declaration's axiom closure, wiring, index/lint, ledger, cleanup.

## Paper proof [PROVED HERE]

For two paths f,g bounded in magnitude by B, write a(j)=|f(j)−g(j)|.
The product expansion gives edge-defect error at most B(3a(j)+a(j+1)).
Summing gives 4B Σ_{j=1}^{M+1}a(j). For divisor responses, triangle inequality
and exact incidence counting give
Σ_{j=1}^K|s_c(j)−s_b(j)|≤Σ_{d≤N}|c(d)−b(d)| floor(K/d).
Hence prefix-defect error is at most 4B times that weighted coefficient sum.
This is a general finite-horizon tool; no squarefree assumption is required.

For ε≥0, |c_ε(d)−μ(d)|≤ε log d. Since log1=0, remove d=1 before the
harmonic estimate: Σ_{d=2}^N1/d=H_N−1≤log N. Therefore
Σ_{d≤N}log(d)/d≤(log N)², and the floor-weighted budget is at most
εK(log N)². The established six-horizon envelope gives B=2, so
|D_ε(M)−D_0(M)|≤8ε(M+1)(log N)².

For M+1<6(N+1), ε≤1/(96(N+1)(log N)²) makes this error at most1/2.
Strict integer-energy margin D_0≤−1 proves D_ε≤−1/2. Transfer from finite
radical representatives, or a Bertrand prime for the rough state, gives the
same certificate on every endpoint with R_N(M+1)<6(N+1), independent of height.
Positive powers inherit it. Positivity follows from N≥2. Compared with the
previous explicit radius, the improvement factor is N/log N>1.

The aggregate response budget itself is at most1/16 on finite certified
prefixes. It controls any individual response there. Thus at prime-family
N=6p−1,k=30p,p>5, response remains at least31/16 while all positive-power
defects are at most−1/2; k remains the first unit-envelope failure.

## Baseline and novelty

Known: finite-sum triangle inequality, divisor-incidence floor reciprocity,
exponential tangent bound, H_N≤1+log N, product perturbation. New formulation:
incidence-weighted defect stability and improved explicit damping radius on
infinite radical fibers. Observation baseline TH10 https://arxiv.org/abs/1009.5281;
shifted-correlation baseline CMS16 https://arxiv.org/abs/1612.03136. No external
priority claim; no optimality of96 or radius order claimed.

Broad query `sum absolute response coefficient difference divisor floor weighted
perturbation harmonic logarithm`: partial=false,74139 files,pending0,
generation1454954. All20 candidate and20 source-argument statements inspected.
Existing weighted floor identities and harmonic bounds support the proof;
no matching incidence-weighted defect perturbation theorem in returned hits.
Compiler coverage mixed. Local source supplies exact reciprocity in
BezoutValuationIncidence/FermiCellJumpReciprocityAndPronicTailBridge.lean and
Mathlib.NumberTheory.Harmonic.Bounds; their applicability remains to be verified
in the scratch proof. The core scratch proof now verifies both directly and
establishes the general incidence-weighted defect bound without warnings.

Mathlib-filtered harmonic query returned partial=false,74141 files,pending0,
generation1454970. All20 candidates and20 source arguments inspected. Harmonic
upper bounds found; the new proof uses Mathlib's root harmonic theorem directly.

## Reusable transport law

For any squarefree-supported coefficient weight c and any real upper bound C,
a certificate D_N(k−1;c)≤C for every2≤k<6(N+1) transfers to every nonempty
prefix whose endpoint radical is below6(N+1). The rough state uses a Bertrand
prime and the other states use their minimal radical representative. This
transfer does not depend on damping or the sign of C.
