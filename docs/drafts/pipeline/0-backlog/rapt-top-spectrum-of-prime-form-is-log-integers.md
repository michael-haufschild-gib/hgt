# The top spectrum of the prime form is the logarithms of the integers

- **ID:** rapt-top-spectrum-of-prime-form-is-log-integers
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** RP29 (spectral gap below the pole), RAPT §9 topic 2 (matched operator of a finite
  prime set: energies `γ + log m + d(m)`).
- **Statement:** For each fixed `k`, `log N − λ_k(P_N) → E_k`, the `k`-th smallest value of
  `E(m) = γ + log m + Σ_{p | m} log p/(p − 1)` over `m ≥ 1` (with multiplicity).

## Goal

The finite-`Q` matched operator has the energies `E(m)` for `Q`-smooth `m`; the conjecture is the
passage to all primes for the actual form on `[1, N]`. It says that Weil's prime form realizes the
multiplicative monoid spectrally: the multiplicative walk (pole gauge, harmonic measure) has, up to
the horizon, the spectrum `{log m + d(m)}`, whose heat trace is the Euler product
`Π_p (1 + e^{−t log p/(p−1)} Σ_k p^{−kt})`, `≈ ζ(t)`.

## Evidence

`log N − λ_k(P_N)` for `k = 1..10`:
- `N = 8000`: 0.557, 1.838, 2.099, 2.465, 2.518, 2.728, 3.100, 3.176, 3.197, 3.244
- `N = 64000`: 0.560, 1.861, 2.123, 2.491, 2.546, 2.753, 3.126, 3.208, 3.230, 3.270
- `E(m)`: 0.577 (1), 1.964 (2), 2.225 (3), 2.589 (5), 2.657 (4), 2.847 (7), 3.215 (11), 3.324 (9),
  3.350 (8), 3.356 (13).
The order of `m` (1, 2, 3, 5, 4, 7, 11, 9, 8, 13) is reproduced exactly; the offsets decrease
like `1/log N`.

## Approach

Lower bounds: product valuation modes `Π_{p|m} ψ_{p, v_p(m)}(v_p(n)) n^{−1/2}`, with
`ψ_{p,k} = 1_{j ≥ k} − (p − 1)^{−1} 1_{j = k − 1}` (exact eigenvectors of the valuation tower),
and the finite-`Q` horizon-defect limit (`tendsto_sieveHorizonDefect_adjunction`). Upper bounds: a
sharp Poincaré inequality on the complement of the first `k − 1` modes. `k = 2` is proved (RP37,
`eventually_atomicWeilForm_below_pole_two_log_two`): `E_2 = γ + 2 log 2 = E(2)`, with the two-scale
Poincaré inequality (finite-prime chain ⊕ tensorized rough fibres) as the template for `k ≥ 3`.

## Log
- 2026-10-28 — created in 0-backlog.
- 2026-10-28 — `k = 2` formalized (RP37).
- 2026-10-28 — all `k`: the codimension bound is formalized (RP39). With `eventually_fullPrimeMatrix_eigenvalue_near` and the simple levels (`matchedSieveEnergy_injective`), the conjecture follows by Courant–Fischer. The eigenvalue-index form `log N − λ_k → E_k` is not yet a Lean statement.
