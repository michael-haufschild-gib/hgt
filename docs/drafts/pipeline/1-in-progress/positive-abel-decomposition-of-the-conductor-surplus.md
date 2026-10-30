# Positive Abel decomposition of the conductor surplus

- **ID:** CONDUCTOR-SURPLUS-ABEL-SQUARES
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [O1](weil-positivity-five-structural-mechanisms.md)
- **Target:** An exact positive Fourier-square decomposition of `E_m(c) − E_1(c/m)`.

Put `x=c/m`, `M=∫φ²`, and

`A_m(n)=(m/φ(m))Σ_{1≤a≤n,(a,m)=1}1/a − H_n`.

The proposed identity is

`E_m(c) − E_1(c/m) = (2/M)Σ_{n≥1} A_m(n) ∫_{nx}^{(n+1)x}|φ̂(2πt)|²dt`.

Every `A_m(n)` is nonnegative by the proved harmonic sieve inequality. The finite Abel identity gives this sum plus the boundary term `A_m(N)T((N+1)x)`, where `T(y)=∫ᵧ^∞|φ̂(2πt)|²dt`. The finite-sieve harmonic asymptotic makes `A_m(N)` bounded for fixed `m`; integrability makes the Fourier tail vanish. Passing to the limit should prove the identity without a new analytic premise.

## Inputs and gap

- `Conductor/CoprimeFourierOrder.lean` proves the prefix order and the resulting rescaled pole inequality.
- `HTGeometry.sum_mul_weight_eq` gives finite summation by parts.
- `tendsto_sievedHarmonic_sub_sieveEuler` supplies the centered harmonic limit.
- Needed: explicit boundary convergence, the exact series identity, and its axiom audit.
- This resolves a conductor surplus. The complete finite-horizon all-vector decomposition remains separate.
