# Testing the arithmetic minimum balance on actual nonzero points

**Status:** exploratory numerical results, not proof certificates. No computation is used in Lean. The separate [formal result](../../../3-formalized/arithmetic-minimum-phase-completeness.md) proves existence statements symbolically.

## Question and actual source

Does the exact real arithmetic balance used by the minimum classes distinguish zeros or exclude off-line points? The full source inverse proves that this balance is equivalent to `Re(zeta(s)/(s(s+1)))=0`. We solved that real equation, then checked the full complex zeta value and the actual remainder profiles. This is a falsification test for the real projection, not a search for off-line zeta zeros.

## Method

All calculations ran in `/root/hgt-rh-minimum-phase-20260906` on the specified Runpod. `scan.py` used 8 worker processes, one BLAS/OpenMP thread each, and 55-digit mpmath arithmetic for zero heights, continuation, and zeta evaluation. It attempted real parts `0.45` and `0.55` from each of the first 24 critical-line zero approximations, in five parameter steps. The root solver was secant; failures and full continuation paths are retained. The solver returns approximate roots, not certified enclosures ([mpmath documentation](https://mpmath.org/doc/current/calculus/optimization.html)).

`remainder_kernel.py` retains the prior direct-prefix plus Euler–Maclaurin implementation. Actual profiles were evaluated on every integer modulus `1..256`, using heads `ceil(6|t|)+512` and `ceil(9|t|)+512`, with tail orders 10 and 14. These sums use complex128 arithmetic; higher precision was used in the independent check.

`verify.py` recomputed five selected projected roots with 100-digit arithmetic and 300 bisection steps on independently checked numerical sign-changing brackets. It also recomputed each selected minimum modulus using high-precision Hurwitz tails, two head sizes, and orders 12 and 18. Four worker processes were used. Neither the brackets nor the asymptotic errors are rigorous interval certificates.

## Results

- Of 48 attempted targets, 41 converged and 7 failed. Five converged paths have a step or total height shift exceeding one; this is a post-scan diagnostic, not a certificate of branch identity. Large jumps and repeated destinations must not be counted as successful local continuation.
- The 41 converged targets contain 39 distinct numerical points at 30 significant digits. Of the 36 targets without a large-jump warning, 31 have equal finite-grid `X` and `Y` minimum indices; 32 retain the reference zero's finite-grid `X` minimum index.
- Every converged point has a nonzero computed zeta value; the smallest magnitude is about `0.09194`. The largest projected residual in the 55-digit scan is below `2.25e-58`.
- Across the full scan, changing heads and orders changes `W` by at most `2.59e-12` and `X` by at most `3.61e-13`.
- In the independent five-point check, the projected residual is below `5.60e-99`; the maximum change in the selected `W` value is below `1.01e-35`.

Two independently checked examples, both with finite-grid minimum indices `X=Y=2`:

| Real part | Height | Zeta value, approximately |
|---|---|---|
| 0.45 | 13.9988148694419788264663657191 | `-0.01562932616 - 0.11477028605 i` |
| 0.55 | 14.3838578308655512694098202754 | `0.02917511688 + 0.19901027985 i` |

They satisfy the real balance to working precision while the omitted imaginary discrepancies are approximately `0.0005876184` and `-0.0009658683`. Their finite-grid labels are not certified global minimum classes.

## Interpretation

The projected balance and observed minimum patterns admit off-line nonzeros on the actual source. Such points are not counterexamples to RH. They are counterexamples, numerically, to treating this real condition as a sufficient zero or location test. The symbolic Lean theorems establish the existence obstruction without relying on these approximations.

Retain the complex discrepancy or supply another independent constraint. Merely restating its required imaginary vanishing at zeros leaves the RH source problem open.

## Files

- `results.json`: all continuation paths, failures, selected finite-grid minima, and precision comparisons.
- `summary.json`, `analysis.json`: scan counts, large-jump warnings, duplicate-destination count, and verification summary.
- `verification.json`: independent bisection and high-precision remainder values.
- `scan.py`, `verify.py`, `remainder_kernel.py`, `hurwitz_kernel.py`: reproducible code. The kernel files are unchanged copies from the preceding minimum-class experiment.

All results were downloaded. The remote cleanup check found no remaining owned experiment processes.
