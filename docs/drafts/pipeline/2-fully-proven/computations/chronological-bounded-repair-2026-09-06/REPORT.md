# Bounded chronological heat repair: finite experiment

**Status:** numerical evidence only; no result enters a Lean proof. The frozen
bounded-array convergence target remains open. The separate
[Lean rigidity theorem](../../../3-formalized/chronological-damping-convergence-rigidity.md)
proves that vanishing geometric-depth damping converges in full L² exactly when
raw Möbius prefixes converge. This experiment tests finite alternatives and
their cancellation, not that theorem.

## Question and models

For h(t)=1/t−1/(e^t−1), measure
||e^(−t)+Σ_(k≤N)a_k h(kt)||₂ on (0,∞). Compare:

- Raw coefficients μ(k).
- Logarithmic taper μ(k)(1−log k/log(N+1)).
- Geometric-depth coefficients Σ_(d|k)μ(k/d)(−ε)^(d−1), with ε tuned in [0,1/2].
- Arithmetic Abel coefficients μ(k)e^(−τk/N), with τ tuned in [0,30].
- Vectors in coefficient boxes |a_k|≤1 and |a_k|≤2.

The scalar tuning routines are numerical searches, not global-optimum
certificates. The box results are retained feasible vectors, also not certified
optima. The exponential kernel and coefficient-controlled RH interface are
classical; see [Darses–Hillion (2021)](https://cml.centre-mersenne.org/item/10.5802/cml.71.pdf).
No novelty claim is made for the kernel or numerical optimization.

## Results

Independent validation L² norms, rounded to three significant figures:

| N | Raw μ | Log taper | Tuned depth | Tuned Abel | Box 1 | Box 2 |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 0.215 | 0.558 | 0.215 | 0.215 | 1.31e−4 | 1.09e−4 |
| 32 | 0.309 | 0.448 | 0.187 | 0.0688 | 1.44e−5 | 1.26e−5 |
| 64 | 0.110 | 0.378 | 0.110 | 0.0925 | 1.76e−6 | 1.57e−6 |
| 128 | 0.00352 | 0.324 | 0.00199 | 0.00239 | 2.26e−7 | 2.22e−7 |
| 256 | 0.0592 | 0.285 | 0.0592 | 0.0349 | 3.14e−8 | 3.00e−8 |
| 512 | 0.0837 | 0.252 | 0.0747 | 0.0167 | 4.12e−9 | 4.03e−9 |

At N=512 the box-1 vector has maximum magnitude 0.9999999940514069 and
Σa_k/k≈−2.98e−11. Its squared error divides into 1.013e−17 below t=1/N,
6.792e−18 on [1/N,1), and 3.350e−20 above 1. Small-t control remains material
even for this very accurate finite fit.

### Interventions on retained vectors

These ablations change coefficients without reoptimizing the remaining ones.

| N, box | Original | Zero coefficients with μ(k)=0 | Reset first 8 to μ |
|---|---:|---:|---:|
| 128, 1 | 2.26e−7 | 0.886 | 0.172 |
| 128, 2 | 2.22e−7 | 0.902 | 0.235 |
| 512, 1 | 4.12e−9 | 0.913 | 0.140 |
| 512, 2 | 4.03e−9 | 1.28 | 0.220 |

The retained cancellation uses broad coefficient changes, including
nonsquarefree indices. This does **not** prove those indices are necessary for
all successful vectors. Resetting a prefix breaks its coordination with the
tail; it does not disprove approximation with an exactly prescribed prefix.

## Numerical checks and solver failure

Integrate in x=log t. Training uses 20-point Gauss rules on intervals of length
at most 1. Validation uses 36-point rules on shifted intervals of length at most
0.8; both split at t=1/N and t=1. A further 52-point check covers N=128,512.
The integral of the target squared reproduces 1/2.

The lower endpoint is δ=10^(−30)/(1+2N)². Since |h|≤1, omitted energy is at
most 10^(−30) for all tested coefficient boxes. For t≥80 the design includes
the exact energy (Σa_k/k)²/80 of the algebraic tail. Its exponentially small
correction is omitted: writing S=Σa_k/k, the elementary bound |E(t)|≤9e^(−t)
gives a tail-energy discrepancy at most
18|S|e^(−80)/80 + (81/2)e^(−160).

Kernel evaluation uses a Bernoulli expansion below 0.25 and stable exponential
expressions above it. Against 80-digit mpmath, 100 kernel samples differ by at
most 3.46e−16. An additional 112 residual points per vector, for boxes 1 and 2
at N=128,512, differ from direct 80-digit sums by at most 1.62e−14. This is a
spot check, not interval certification. At N=512 the two main quadratures'
relative energy differences are 8.13e−9 and 1.19e−8. The 52-point norms agree
to the displayed precision.

Initial trust-region solves failed basic monotonicity: increasing N or allowing
a larger box sometimes worsened the returned error. Objective scaling alone
did not fix the conditioning. The refinement compares bounded-variable least
squares at two scales with an independent singular-mode construction. For the
latter, A=UΣVᵀ and a linear program minimizes ||a||∞ subject to canceling the
first r output modes. Orthogonal correction removes equality tolerances; every
candidate is checked against its coefficient box and rescored with the full A.
At N=512 the retained box-1 vector cancels the first 30 modes.

Zero-padding a retained vector supplies a candidate at the next N; every box-1
vector is also a box-2 candidate. Thus previously found feasible bounds survive.
Independent validation confirms both monotonicities. At the largest N the
quadrature dual lower bounds are negative and uninformative, so **optimality
is not established**. Smooth-looking finite decay is not an asymptotic rate.

## Interpretation and reproducibility

The useful lead is coordinated arithmetic repair with a coefficient budget.
Neither the raw sequence nor the one-parameter families reproduce these finite
fits. The hard missing theorem is a construction and full L² estimate uniform
over all cutoffs. Nothing here controls a limit or proves RH.

All numerical work ran on the authorized Runpod, in
`/root/chronological-bounded-repair-20260906`, with up to four worker processes
and four BLAS threads per worker. Run scripts in this order:

```sh
python3 experiment.py
python3 check_optimizer.py
python3 refine_experiment.py
python3 diagnostics.py
```

Plotting uses matplotlib; it was installed in the task's isolated `deps/`
directory and selected with PYTHONPATH. That installation is not included in
the downloaded data. `environment.json` records runtime versions.

- `results.json`, `result_N.json`: refined measurements and solver diagnostics.
- `summary.json`: compact comparison; `diagnostics.json`: ablations and 80-digit checks.
- `coeff_MODEL_N.csv`: explicit retained coefficient vectors, with μ for comparison.
- `profile_N.npz`, `comparison.png`: error profiles and comparison plot.
- `screening_results.json`, `optimizer_scaling_check.json`: failed initial optimizer
  checks, retained to prevent interpreting those outputs as minima.
- `candidate_pool_N.npz`: best candidates before enforcing nesting across N.
- `results_bundle.tar.gz`: downloaded scripts and numerical artifacts; excludes dependencies.

No owned computation remains running after collection.
