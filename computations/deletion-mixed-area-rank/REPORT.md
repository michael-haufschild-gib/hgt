# Literal deletion mixed-area rank diagnostic

**Outcome:** the proposed rank-at-most-two law is strongly disfavored at each of
three tested approximate zeta zeros. This is a floating-point diagnostic, not a
proved counterexample. Placement in this computation directory does not mean
the rank conjecture, zero approximations, or error bounds are fully proved.

Run on the user-designated Runpod, 2026-09-06, Python 3.8.10, NumPy 1.24.4,
mpmath 1.3.0. Six worker processes, one BLAS/OpenMP thread per worker, 32 CPUs
available. Recorded execution time: 0.93 seconds, excluding SSH and transfer.
Reproduce there with `python3 mixed_area.py --workers 6 > mixed-area-results.json`.
The script and downloaded raw JSON are in this directory. No remote worker
remained after completion.

## Quantity and checks

Labels are `[2,3,5,7]`. For `x_p(n;s)=(1-p*[p divides n])*n^(-s)`, compute

`A_pq(N;s) = (1/2) sum_{m<n<=N} (x_p(m;s)x_q(n;s)-x_q(m;s)x_p(n;s))`.

The products are holomorphic: **no conjugation**. Test the Pfaffian
`P=A_12*A_34-A_13*A_24+A_14*A_23`, which must vanish for an antisymmetric
four-by-four matrix of rank at most two. Normalize its magnitude by the sum of
the magnitudes of these three product terms, solely as a diagnostic scale.

Checkpoints are 13,440; 53,760; 215,040; 860,160, all complete periods of the
unweighted coefficients. The vector implementation accumulates the prefix
*before* the current jump. It agrees with a scalar recurrence through 4,200
terms within `3.66e-14` entrywise and `5.88e-14` for the Pfaffian. An independent
70-decimal recurrence through 2,100 terms agrees within `1.78e-14` entrywise.
An extended-precision full run at the first zero reproduces the displayed
Pfaffian; that run still uses the same binary64-rounded exponent.

mpmath supplies approximate zeros 1, 2, and 5 at 70 decimal precision. The main
NumPy runs round these parameters to binary64. Raw JSON retains the original
decimal parameters, mpmath zeta residuals, endpoint targets, every area matrix,
and every Pfaffian term. Residuals at the high-precision parameters are not
rigorous zero certificates or residual bounds for rounded parameters.

## Results

At the largest cutoff:

| Approximate zero | Pfaffian | Normalized magnitude |
|---:|---:|---:|
| 1 | `2.6016384083 + 1.7874383517 i` | 0.23734 |
| 2 | `-10.3564783147 - 3.1662699330 i` | 0.63903 |
| 5 | `-8.2177110926 - 4.4918853814 i` | 0.39488 |

The changes from the preceding checkpoint are small relative to these values;
no trend toward zero is visible. Each zero also has a control shifted right by
0.1. Additional controls are `s=1.25`, `s=2`, and `s=1+3i`; their Pfaffians are
also nonzero at the recorded cutoffs. These controls are not zeta zeros.

## Consequence and limits

The first decisive step of the candidate architecture was “a zero forces
decomposable joint area.” These data argue against investing in its proof.
The different identity for the oriented area of endpoint vectors does not
justify it: a chronological area adds contributions from many different pairs
of times.

Existing coprime cross-completion proves convergence throughout the positive
half-plane. This diagnostic supplies neither a quantitative tail certificate
nor a certified root enclosure, so it does not formally falsify the infinite
zero-specific statement. No computed value enters Lean. No sign or rank claim
about hypothetical off-line zeros follows. An exact replacement law would need
new mathematical support; rescaling rows or appending the known endpoint
determinant identity does not repair the tested condition.

See [candidate and second-pass audit](../../../1-in-progress/euler-deletion-mixed-area-rank.md).
