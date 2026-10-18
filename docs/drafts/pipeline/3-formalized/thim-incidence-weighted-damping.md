# Incidence-weighted perturbation and logarithmic damping radius

- **ID:** thim-incidence-weighted-damping
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean verified)
- **Statement:** For N≥2, throughout 0≤ε≤1/(96(N+1)(log N)²), the damped coefficient μ(d)d^(−ε) certifies D≤−1/2 on every nonempty prefix whose radical endpoint is below 6(N+1).

## Goal

Replace repeated worst-case coefficient charging by exact divisor-incidence
counts. Retain uniformity over infinite radical fibers and arbitrary positive
powers. Full all-ε≥0 defect control remains open.

## Gates

- [x] Current-source inspection and broad corpus search.
- [x] Dependency-closed paper proof below.
- [x] Scratch proof and actual-source Lean audit.
- [x] Every declaration's axiom closure, wiring, index/lint, ledger, cleanup.

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
Mathlib.NumberTheory.Harmonic.Bounds. Full scratch and actual-source proofs
verify both directly, including the general incidence-weighted defect bound,
without warnings.

Mathlib-filtered harmonic query returned partial=false,74141 files,pending0,
generation1454970. All20 candidates and20 source arguments inspected. Harmonic
upper bounds found; the new proof uses Mathlib's root harmonic theorem directly.

## Reusable transport law

For any squarefree-supported coefficient weight c and any real upper bound C,
a certificate D_N(k−1;c)≤C for every2≤k<6(N+1) transfers to every nonempty
prefix whose endpoint radical is below6(N+1). The rough state uses a Bertrand
prime and the other states use their minimal radical representative. This
transfer does not depend on damping or the sign of C.

## Verification

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/DivisorIncidencePerturbationAndLogarithmicDamping.lean` (340 lines).
- SHA256: `d1f497e8a2da771becdca4b43c18fe731dea85ab38e8fd8afd3a5327cedf90a5`.
- Full scratch and actual-source `lake --old env lean` exited 0 without warnings.
  All 19 public theorems, one definition and one private helper have exactly
  {propext, Classical.choice, Quot.sound} as axiom closure. Audited
  2 additional compiler-generated helpers;
  all 23 closures use only standard Lean axioms.
- `logs/thim-incidence-audit.json` checks every closure, 20 public baseline
  docstrings, all 20 public API entries with source positions, source/dependency hashes,
  fresh artifacts, unique umbrella import, MainTheorems reachability,
  whitespace and prohibited declarations. The API generator omits private
  declarations; the private helper and its generated proofs are axiom-audited.
- Evidence: `logs/thim-incidence-{lean,axioms,index,lint}.txt`.
  Index exited 0. `lint --check-generated` exited 1 with
  2 external findings, recorded exactly in audit JSON.
  No new-leaf or prohibited-declaration finding. Shared index freshness may
  change during concurrent edits; no globally clean gate is claimed.
- All owned jobs terminal; nine owned temporary files removed and verified absent.
  README not edited. No full/umbrella builds, numerical experiments, added axioms,
  heartbeat changes, commits or pushes. Continuing research goal remains active.

## Next conjecture — weighted coefficient neighborhood (unproved)

For N≥2 put K=6(N+1) and
W_N(c)=Σ_{d≤N}|c(d)−μ(d)| floor(K/d).
Conjecture: every squarefree-supported c with W_N(c)≤1/20 has
D_N(M;c)≤−1/2 for every M≥1 with R_N(M+1)<6(N+1).

Proposed mechanism, not yet Lean-verified: the aggregate incidence budget
controls every response error up to K by W. Hence the Möbius magnitude-two
envelope gives |s_c|≤2+W. The new perturbation theorem should give
|D_c−D_μ|≤4(2+W)W≤41/100<1/2. Combine the strict Möbius margin with the
new finite-certificate transfer law. A stronger candidate uses the exact
quadratic condition 4(2+W)W≤1/2 instead of the convenient radius 1/20.
The unit coefficient is charged with weight K, so the gauge obstruction is
not bypassed. Audit all endpoints, constants, support and hypotheses before
claiming this result; full all-ε≥0 damping control is a separate open problem.

Preliminary field-filtered query `squarefree coefficient perturbation weighted
divisor incidence neighborhood negative prefix defect`: partial=false,
74142 files,pending0,generation1455029. All20 candidate and20 source-argument
statements inspected. Hits include rough-sign rigidity, gauge obstructions,
radical/power transport and coefficient recovery, but no matching quantitative
weighted-neighborhood certificate in returned hits. Broaden before new code;
mixed source/compiler coverage is not universal formal verification.
