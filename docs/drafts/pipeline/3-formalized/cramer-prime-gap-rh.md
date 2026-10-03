# Cramér: under RH, primes in (x, x + K√x log x]

Stage: 3-formalized (2026-10-03). Loop cycle 230 (MUST-729).

## Lean
`formal/GaloisForLFunctions/RHTower/CramerPrimeGapRH.lean` (wired after `VonKochPrimeCounting`):
`zeroShortWeight_eq_of_riemannHypothesis`, `tsum_zeroShortWeight_le_of_riemannHypothesis`,
`psi_add_sub_psi_ge_of_riemannHypothesis`, `exists_prime_of_theta_lt`, `cramer_zero_part_le`,
`cramer_gain_pos`, `exists_prime_in_sqrt_log_window_of_riemannHypothesis`. Axioms clean.

## Proof
Two-window squeeze (corpus `psi_window_ge_sub_zeroShortWeight`) + RH weight `x^{−1/2}min(1, Y cosWeight)`;
split at `S = 6x/h`; `h = K√x log x`; `ψ − θ ≤ C√x`.
