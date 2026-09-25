# Arithmetic power damping versus positive cutoff averaging

**Exploratory numerical evidence, not a proof or certified optimization.**
All mathematical computation ran on the authorized Runpod. No result enters Lean.
Original [R] and power-damping [G] remain open.

For h(t)=1/t−1/(exp(t)−1), compare actual residuals
exp(−t)+Σ_(k≤N)a_k h(kt). Power damping uses a_k=μ(k)k^(−ε).
Positive cutoff averaging chooses α_j≥0, Σα_j=1 and
a_k=μ(k)Σ_(j≥k)α_j. Hence |a_k|≤1, Möbius signs are preserved, and
nonsquarefree coefficients remain zero. No zero ordinates enter fitting.

## Outcome

| N | Best power ε found | Power error | Positive-average error | Active cutoffs |
|---:|---:|---:|---:|---:|
| 128 | 0.00155796 | 2.51501e−3 | 6.55005e−7 | 13 |
| 512 | 0.0271738 | 6.77149e−2 | 1.68243e−8 | 22 |
| 2048 | 0.0405768 | 1.51729e−1 | 1.29397e−9 | 29 |
| 8192 | 0.0638938 | 1.70686e−1 | 1.01503e−9 | 35 |

Errors use independent validation quadratures. At N=8192 the final vector
cancels 34 fitted singular modes; its selected cutoffs range from 5 to 7995,
with 10/50/90-percent mass quantiles 73/302/1286. Terminal-cutoff mass is zero
in every retained vector. The N=8192 initial Wolfe vector had error 1.74707e−9;
mode refinement improved it. Retained errors decrease across tested cutoffs.

**Interpretation.** Large finite improvements do not require changing Möbius
signs or inserting nonsquarefree coefficients. Positive mixtures of raw
prefixes already achieve errors near 1e−9. This identifies a smaller family
worth a source estimate. It proves neither asymptotic convergence nor a
lower error floor. Earlier unrestricted C=1 fixed-prefix fits reached
3.50601e−10 at N=4096, so these averages do not outperform every earlier fit.

The finite best power parameters increase over these four cutoffs; this does
not decide the existence of a vanishing ε_N schedule. Separately, an exact
Lean proof excludes ε_N log N→0: successful damping must transfer a cofinally
positive fraction of Abel mass away from the terminal cutoff. The convex
vectors are outside that excluded near-identity regime.

## Protocol and checks

- Power search: ε∈[0,4], mixed logarithmic/linear grid, local scalar refinement
  around the eight best grid points. No global optimum claim.
- Convex search: fully corrective Wolfe minimum-norm column generation on
  raw-residual columns, with nonnegative simplex coefficients. N=128,512,2048
  ended in active-vertex stagnation; N=8192 hit the 2000-iteration limit.
  Best feasible vectors were retained. These are not convergence certificates.
- Refinement: deterministic interpolative SVD, candidate ranks 8 through 45,
  simplex linear programs annihilating leading right singular modes, then
  equality correction, nonnegative clipping and renormalization. Every
  retained vector was reevaluated through the actual heat kernel. Smaller
  initial Wolfe candidates were also available at larger cutoffs. Solver
  failure at a rank is not evidence of mathematical infeasibility.
- Training: 24-point Gauss quadrature per logarithmic panel. Validation uses
  shifted, narrower panels and order 48 for power fits, order 60 for final
  averages. Both endpoint tails are handled separately. On (0,δ), with
  δ=1e−30/(1+2N)², the elementary coefficient bound gives energy at most 1e−30.
  On [80,∞), the algebraic tail energy (Σa_k/k)²/80 is included exactly;
  the remaining exponential term has norm at most
  (1+(1−exp(−80))⁻²)exp(−80)/sqrt(2) for |a_k|≤1, far below reported errors.
  Interior quadrature errors are checked empirically, not with intervals.
- Each final average has 52 residual spot checks at 80 decimal digits.
  Maximum discrepancy from floating-point evaluation is 8.51e−15. Independent
  full-norm quadratures agree at the reported precision. The largest power-fit
  residual discrepancy is 1.74e−14. Such spot checks are not rigorous error bars.
- Floating quadrature dual bound at N=128 is 6.54864e−7, close to its primal
  6.55005e−7. At larger N the retained dual lower bounds are zero: they cannot
  certify optimality, stagnation, or a nonzero continuum distance.

## Reproduce and locate outputs

Remote directory: `/root/chronological-arithmetic-averaging-20260906`.
Python 3.8.10, NumPy 1.24.4, SciPy 1.10.1, mpmath 1.3.0; 32 logical CPUs.
`averaging.py` and `refine.py` each use four worker processes with four BLAS
threads per worker. The initial run including validation took 31.00 seconds;
the largest refinement solve took 13.51 seconds, excluding validation.

Run `python3 averaging.py`, then `python3 refine.py`, in the remote directory.
`kernel_reference.py` is the reused helper; do not run its older experiment
driver. `plot_results.py` renders saved results; the remote plotting dependency
path is `/root/chronological-bounded-repair-20260906/deps` via PYTHONPATH.

`results.json` / `validation.json`: initial fits and validation.
`refined_results.json`: final choices, rank diagnostics and independent checks.
`refined_coeff_N.csv`: final actual coefficient vectors.
`refined_support_N.csv`: positive cutoff probabilities.
`refined_N.npz`: coefficients and complete α arrays. Initial vectors, scripts
and solver outputs are preserved for comparison. `arithmetic-averaging.png`
and `.pdf` show errors, monotone envelopes and sparse cutoff distributions.

**Remaining mathematical task:** control the full uncancelled residual for
arbitrarily large cutoffs. Fixed-rank mode feasibility has no quantitative
bound tying rank to cutoff, and cannot be upgraded by an unsupported diagonal
argument. Pointwise convergence or tests on a dense collection do not supply
the uniform norm estimate needed for a Hilbert-space convexity argument.
