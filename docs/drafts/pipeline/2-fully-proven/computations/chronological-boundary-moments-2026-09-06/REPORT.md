# Exact boundary-moment repair: finite experiment

Exploratory numerical data, not a proof or a certified continuum bound.
The frozen K-test and its mathematical constraints are in
`../../1-in-progress/chronological-boundary-moment-repair.md`.

At N=512,2048,8192, freeze the first N/2 coefficients to Möbius. For each
m=0,…,8, impose exact harmonic charge zero, coefficient sum −2, and the first
m odd Taylor cancellation moments. Select the unique tail with minimum sum
of squared coefficients. There is no full-residual optimization or clipping.

## Results

| N | Best m | Full norm | Coefficient bound | Best m within unit box | Unit-box norm |
|---:|---:|---:|---:|---:|---:|
| 512 | 3 | 4.04774603e-06 | 1 | 3 | 4.04774603e-06 |
| 2048 | 8 | 5.74057967e-07 | 1.66872904 | 7 | 1.28472776e-06 |
| 8192 | 5 | 5.20263969e-07 | 1 | 5 | 5.20263969e-07 |

At N=512, moving from m=3 to m=8 raises the full error from 4.04774603e−6
to 1.59427516e−5 and the coefficient bound from 1 to 10.2558158. At N=8192,
all nine cases retain the unit bound; the best is m=5, error 5.20263969e−7.
Neither norm nor budget behavior in m can be extrapolated to every cutoff.
The frozen qualitative prediction of a coefficient/error tradeoff appears
in these cases; this is not an asymptotic obstruction.

The error below t=1/N is already tiny at the best moment orders. The full
error is concentrated outside that Taylor-scale interval. Exact derivatives
and harmonic charge therefore do not settle the missing approaching-zero
remainder. `summary.json` gives the regional fractions for each selected case.

## Numerical audit and limitations

The moment Gram systems and tail coordinates use 100 decimal digits. All
27 systems solved. High-precision scaled moment residuals range from about
1e−101 to 1e−93. Floats saved in CSV are separately checked against every
scaled moment; those residuals include rounding of the coefficients.

Training uses composite Gauss–Legendre order 24 in log t. Validation uses
order 60 on shifted, narrower log intervals, without reusing training nodes.
Both cover the near-zero endpoint; the omitted left energy is bounded using
the actual coefficient maximum. At t≥80, the algebraic charge contribution
S²/80 is included exactly for the saved float vector. The remaining tail norm
is bounded by [1+C/(1−exp(−80))²]exp(−80)/sqrt(2), with C the actual budget.
Four actual residual evaluations per vector, at Nt=.01,1,10,100, are recomputed
with 100 digits. These are checks, not rigorous quadrature error intervals.

Maximum independent quadrature norm difference: 1.162e-16.

Maximum high-precision residual spot difference: 2.956e-14.

Maximum saved-float scaled moment defect: 1.193e-15.

Largest omitted-left energy bound: 2.625e-29.

## Reproduction and files

All mathematical computation ran on authorized Runpod
`root@157.157.221.29:27094`, directory
`/root/chronological-boundary-moments-20260906`.
Three worker processes, four BLAS threads each. Python 3.8.10, NumPy 1.24.4,
SciPy 1.10.1, mpmath 1.3.0. Run `python3 moments.py` in that directory.
It imports `kernel_reference.py` from sibling
`/root/chronological-arithmetic-averaging-20260906`; that helper is also
archived locally under the corresponding earlier computation folder.
Plotting uses Matplotlib from
`PYTHONPATH=/root/chronological-bounded-repair-20260906/deps python3 summarize.py`.

`results.json` and per-N JSON: all moment coordinates, diagnostics and timings.
`coeff_N_m.csv`: every actual saved coefficient and its Möbius reference.
`vectors_N.npz`: all vectors and weighted validation residuals.
`run.log`: raw output. `summary.json`: selected cases and aggregate checks.
`boundary-moments.png/.pdf`: plots of full error and tail coefficient cost.

No zero ordinates were supplied to the construction. No numerical result is
used in Lean. The fixed-dimensional obstruction and growing-jet source have
separate paper proofs; these data establish neither of those theorems nor RH.

Total computation and validation time: 9.183 seconds.
