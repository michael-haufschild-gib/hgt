# Arithmetic minimum classes: exploratory tests

These computations are diagnostics, not proof certificates. All numerical work ran on the specified Runpod in `/root/hgt-rh-minimum-classes-20260906`. Scripts and downloaded results are retained here. No numerical result enters Lean.

## Questions and method

For the actual remainder

`R_s(n)=sum_(k=1..n)k^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`,

`W_p=p^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(pn))`,

put `u=conjugate(s)`, `X_p=p Re(mu(p)W_p/[u(u+1)])`, and `Y_p=p^(4 Re(s)-1) Re(mu(p)W_p/[u(u+1)])`.

The first frozen test proposed that neither profile attains a negative global minimum at a nontrivial zero. At `Re(s)=1/2`, the profiles coincide and the previously derived paper asymptotic gives tail lower boundary `-zeta(2) Re(1/(u+1))/12`. A finite value below this boundary challenges the proposed principle. The independent second test proposed divisor dominance `|W_(pq)|<=|W_p|` at zeros.

`scan.py` tests the first 96 critical-line zero approximations at every modulus `1..256`, plus real-part shifts to `0.4`, `0.6`, and `0.8` at the first 16 heights: 144 points total. Eight process workers use vectorized NumPy partial sums and one BLAS/OpenMP thread each. Heights and zeta values use 45-digit mpmath. Ordinary arithmetic sums use complex128, with head lengths `ceil(6|t|)+512` and `ceil(9|t|)+512`; tail orders are 10 and 14. Positive-real Hurwitz tail sums use [SciPy's two-argument zeta function](https://docs.scipy.org/doc/scipy/reference/generated/scipy.special.zeta.html). Recorded software: Python 3.8.10, NumPy 1.24.4, SciPy 1.10.1, mpmath 1.3.0.

`verify.py` recomputes four selected witnesses through independent complex Hurwitz remainders, at 75 digits, with larger heads and orders 12/18. `verify_dominance.py` checks the strongest divisor-dominance violation at 80 digits. These checks still use asymptotic tails, not rigorous interval enclosures.

## Outcomes

All 96 critical-line tests contain a finite `X_p` below the paper tail boundary. For example:

| Zero index | Witness modulus | `mu(p)` | `X_p` | Tail lower boundary |
|---|---:|---:|---:|---:|
| 1 | 2 | -1 | -0.006966745987 | -0.001017700928 |
| 12 | 6 | 1 | -0.004528788137 | -0.000064488426 |
| 49 | 15 | 1 | -0.002877875672 | -0.000010323085 |
| 81 | 30 | -1 | -0.003426977108 | -0.000005014321 |

The finite-grid minimizing modulus varies across 19 values. Its Möbius sign is negative in 80 tests and positive in 16. Both primes and squarefree composites occur. These are observed minima over `1..256`, not certified global class labels. At 42 of the 48 shifted nonzero controls, the observed minimizing index equals that of the corresponding critical-line zero. Thus a finite-grid label alone does not determine location; those controls do not refute a theorem whose hypothesis includes `zeta(s)=0`.

The largest head/order drift in `W` is about `3.76e-12`; for `X`, about `5.15e-13`. At the four independently checked witnesses, tail-order drift in `W` is below `8e-36`, and scan discrepancies in `X` are below `3.49e-16`. These are consistency diagnostics, not certified error bounds.

Divisor dominance fails strongly in the numerical tests. At the 67th zero approximation, with height about `176.4414342977104`, the independently checked values are

`|W_1| = 0.00928334494211443`,

`|W_19| = 5.10141213062091`,

giving ratio about `549.523061184344`. The two high-precision tail checks drift by less than `1.34e-37`. Uniform decay of `W_p` as `p` grows does not imply monotonicity at individual multiplicative steps.

## Mathematical interpretation and limits

The minimum-avoidance proposal failed its falsification test. Its positive survivor is now stronger than the numerical observation: [the formal arithmetic mean argument](../../../3-formalized/arithmetic-zero-minimum-classes.md) proves that every critical-line zero has a finite value below the same explicit boundary. This uses exact inversion, a telescoping reciprocal-square bound, and algebra; no computed zero is used. Combining that finite undershoot with the existing paper asymptotic forces an attained negative minimum on paper. The asymptotic-to-attainment step is not claimed as a theorem of the new Lean module.

The independent divisor-dominance proposal is numerically rejected, not declared a Lean counterexample. The proved positive replacement is the actual power-decay envelope, which retains the possibility of large finite excursions. Neither experiment locates all zeta zeros, proves RH false, or supplies the missing exclusion of off-line zeros in the finite-label classes.

Files: `scan.py`, `analyze.py`, `verify.py`, `verify_dominance.py`, `results.json`, `analysis.json`, `verification.json`, and `dominance-verification.json`.
