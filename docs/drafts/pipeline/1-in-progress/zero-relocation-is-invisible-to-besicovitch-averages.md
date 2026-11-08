# Rational zero relocation and Besicovitch averages

- **ID:** zero-relocation-is-invisible-to-besicovitch-averages
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** The actual symmetric rational zero-relocation multiplier preserves zeta's vertical mean-square class and Fourier means above the critical line, while destroying Bohr almost periodicity in the absolutely convergent half-plane.

## Candidate proof

Use the literal `zeroRelocationFactor`, whose vertical limit is `1` and whose denominator has zeros only on `Re s=1/2`. On every line `σ>1/2`, bounded Cesàro square means of zeta and uniform smallness of the multiplier error above a fixed height imply that the mean square of `ζ(R−1)` tends to zero. Cauchy–Schwarz then preserves each Fourier mean and the square mean. Integrate from height `1` to avoid the pole at `s=1`.

This mechanism needs only convergence of the multiplier to one; the proposed `O(t^-2)` rate is stronger than necessary. It does not assume RH or exclude any actual zeta zero. The existing ordinary Dirichlet-series obstruction distinguishes the perturbed function despite identical limiting averages.

## Audit questions

- Verify the corpus's mean-square bound for every required abscissa.
- Keep the monic normalization `R(σ+it)→1`. A separate normalization `R(1)=1` must be proved for the chosen parameters; it cannot be inserted by rescaling without changing the vertical limit.
- Do not infer an AAL-violating zero configuration for actual zeta from the multiplier alone.

## Status

Paper argument identified. Exact mean-square APIs and formalization pending.
