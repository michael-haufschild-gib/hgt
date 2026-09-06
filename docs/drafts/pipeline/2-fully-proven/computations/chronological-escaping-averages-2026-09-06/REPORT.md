# Escaping cutoff averages and release of monotonicity

**Exploratory finite evidence. RH and [R] remain open.** All numerical
mathematics ran on the authorized Runpod. No numerical output enters Lean.

The residual is r_N(t)=exp(−t)+Σ_(k≤N)a_k h(kt), with
h(t)=1/t−1/(exp(t)−1). Positive averaging over raw cutoffs j∈[M,N] means
α_j≥0, Σα_j=1, and a_k=μ(k)Σ_(j≥k)α_j. Thus every coefficient through M
is exactly μ(k), the remaining Möbius signs are preserved, nonsquarefree
coefficients vanish, and |a_k|≤1. Every integer cutoff in each prescribed
window is available to the optimizer.

## Frozen H-test: move the frozen prefix with N

Independently validated full-norm estimates:

| N | M=1 | M=N/64 | M=N/16 | M=N/4 | M=N/2 |
|---:|---:|---:|---:|---:|---:|
| 512 | 1.68243e−8 | 1.68997e−8 | 2.35911e−8 | 1.51201e−7 | 9.04794e−6 |
| 2048 | 1.29397e−9 | 3.94170e−9 | 8.63240e−9 | 3.52501e−7 | 9.03098e−6 |
| 8192 | 1.01503e−9 | 2.52826e−9 | 9.24296e−9 | 7.15486e−8 | 5.93328e−6 |

The half-prefix restriction has a substantial finite cost. At N=8192,
M=4096, the positive-average vector uses five raw cutoffs from 4885 to 7966.
Its quadrature primal norm is 5.93328017e−6 and floating dual bound is
5.93327376e−6. Half-prefix primal and dual values nearly coincide at all
three tested N. This is good numerical evidence about these finite programs,
not an interval certificate or a proof of an asymptotic floor.

The feasible sets are nested at fixed N. Every retained wider-window candidate
was compared against candidates from all narrower windows. The reported errors
respect the resulting monotonicity. Errors across different N need not be
monotone when M grows with N; the quarter-prefix row illustrates this.

## Independently frozen J-test: which restriction causes the penalty?

Keep N=8192, M=4096 and C=1 fixed. Relax the coefficient constraints in stages:

| Tail family | Validated error | Frozen head exact? |
|---|---:|:---:|
| Positive cutoff averages; monotone envelope | 5.93328e−6 | Yes |
| Preserve Möbius signs; allow nonmonotone envelope | 1.29339e−8 | Yes |
| Signed squarefree unit box | 1.20479e−8 | Yes |
| Full unit box | 6.05440e−9 | Yes |

The prediction frozen before J was a sign-preserving error ≤1e−8.
**That target was not attained.** Its impossibility was not certified either:
the three relaxed programs have zero retained dual lower bounds. The full-box
result cannot be relabeled as passing the sign-preserving prediction.

The sign-preserving vector has 636 increases in its envelope along successive
squarefree indices. It lies outside the monotone family. Thus the large finite
half-prefix cost is substantially reduced without changing Möbius signs,
unfreezing earlier coefficients, or increasing C. Allowing nonsquarefree
coefficients gives a further finite improvement. None establishes a uniform
construction as N→∞.

## Numerical protocol and limitations

H uses fully corrective Wolfe minimum-norm search plus deterministic
interpolative SVD and simplex linear programs cancelling leading singular
modes. Previous valid averages are filtered and renormalized as candidates;
all narrower-window incumbents remain available in wider windows. All
retained probabilities are nonnegative and normalized. Solver failure or
stagnation is not treated as mathematical infeasibility.

J uses deterministic SVD with rank constrained by numerical singular-value
resolution, bounded linear programs for exact leading modes, and balanced
programs trading the remaining modal residuals. Coefficients are corrected,
clipped into their prescribed boxes and evaluated through the full kernel.
Each relaxed family retains candidates from its stricter families.

Training uses 24-point Gauss quadrature per logarithmic panel; validation uses
shifted, narrower panels with order 60. The omitted interval (0,δ),
δ=1e−30/(1+2N)², has energy at most 1e−30 by the coefficient bound.
The [80,∞) algebraic tail energy (Σa_k/k)²/80 is included; the remaining
exponential term has norm bounded by
(1+(1−exp(−80))⁻²)exp(−80)/sqrt(2) for C=1. Interior quadrature accuracy is
empirically checked, not certified by intervals.

Each retained vector has 32 independent residual spot checks at 80 digits.
The largest discrepancy for the displayed N=8192 H cases is 3.12e−14;
for J it is 5.40e−14. Independent quadratures agree at the displayed precision.
These checks do not prove optimality or provide rigorous error bars.

## Mathematical consequence and remaining estimate

Growing-prefix repair remains numerically possible at these cutoffs in the
original unit box. Positive averages impose an additional monotonicity
constraint with a visible finite cost. The next source estimate must control
the actual residual of bounded coefficients as the frozen prefix grows;
neither finite mode cancellation nor small error at these three N supplies it.

The attempted positive-divisor and reflected-Mellin estimates did not close
this gap. A bounded reflected zeta quotient does not establish L² convergence
of the actual arithmetic truncations. This is precisely a separate step in
[Báez-Duarte's proof](https://arxiv.org/pdf/math/0205003), where RH is used.
No RH assumption was imported into this investigation.

## Reproduce and inspect

Remote directory: `/root/chronological-escaping-averages-20260906`.
Dependency scripts: sibling `/root/chronological-arithmetic-averaging-20260906`,
specifically `kernel_reference.py` and `averaging.py`.
Run `python3 escaping.py`, then `python3 release_monotonicity.py` on Runpod.
Python 3.8.10, NumPy 1.24.4, SciPy 1.10.1, mpmath 1.3.0; 32 logical CPUs.
H used four workers with four BLAS threads each and took 43.15 seconds including
validation; J used three such workers and took 12.59 seconds including validation.

`search.json` / `results.json`: complete H solver diagnostics and validation.
`coeff_N_M.csv` and `support_N_M.csv`: actual vectors and positive probabilities.
`final_N_M.npz`: vectors, probabilities and rescaled residual profiles.
`release_results.json`: J searches and checks; `release_KIND.csv` / `.npz`
contain its vectors. Raw solver output is retained in `run.log` and `release.log`.
`plot_results.py` renders `.png` and `.pdf`; on Runpod set
PYTHONPATH to `/root/chronological-bounded-repair-20260906/deps` for plotting.
Scripts, outputs and this report are downloaded for future inspection.
