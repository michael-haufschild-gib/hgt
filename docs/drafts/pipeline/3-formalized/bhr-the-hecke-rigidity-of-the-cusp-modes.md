# BHR — the Hecke rigidity of the cusp modes

- **ID:** bhr-hecke-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** continuation of `bhr-the-hecke-eigenforms-of-the-cusp-channel.md`; ASH open topic 4.
- **Statement:** Let `f ∈ S(λ)` with `T_p f = c_p f` for every prime `p`, and `a_n(y) = ∫₀¹ f(x+iy) e(−nx) dx`.
  1. `c_p a_n(y) = [p ∣ n] a_{n/p}(py) + p a_{pn}(y/p)` for all `n, y > 0`.
  2. If `a_1 ≡ 0` and `a_{−1} ≡ 0` then `f = 0`.
  3. Two Hecke eigenforms in `S(λ)` with the same `(c_p)` and the same `a_{±1}` coincide.
  4. Every eigenvalue of the cusp spectrum carries a Hecke eigenform with `a_1 ≢ 0` or `a_{−1} ≢ 0`.

## Paper proof
1. The zeroth-to-`n`-th coefficient formula of `T_p` (corpus `coefficient_heckeT`), with `T_pF = c_pF` on `y > 0`.
2. `a_0 ≡ 0`. For `|n| ≥ 2` pick a prime `p ∣ n`, `n = pm`; (1) at index `m`, height `py`: `p a_n(y) = c_p a_m(py) −
   [p ∣ m] a_{m/p}(p²y)`, with `|m|, |m/p| < |n|`. Strong induction gives `a_n ≡ 0` for all `n`; each horocycle slice is
   continuous and `1`-periodic with vanishing Fourier coefficients, hence zero.
3. Apply (2) to `f − f'`.
4. (2) and `exists_heckeEigenform`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheHeckeRigidityOfTheCuspModes.lean`, wired into `BlackHoleRingdown.lean`,
checked with `lake --old env lean`, no messages. Axioms of `eq_of_heckeData`, `exists_heckeMaassForm_firstCoeff`:
`propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.HeckeCusp`) |
|---|---|
| (1) | `fourierCoeff`, `hecke_recursion` |
| (2) | `eq_zero_of_firstCoeff_eq_zero` |
| (3) | `eq_of_heckeData` |
| (4) | `exists_firstCoeff_ne_zero`, `exists_heckeMaassForm_firstCoeff` |

## Not formalized
- The modal equation fixes `a_{±1}` up to a scalar (decaying solutions of `a'' = (4π² − λ/y²)a`), which would bound
  joint Hecke eigenspaces by two, and by one with mirror parity.

## Log
- 2026-11-08 — created and formalized.
