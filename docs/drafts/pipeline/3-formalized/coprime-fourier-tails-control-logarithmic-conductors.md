# Coprime Fourier tails control logarithmic conductors

- **ID:** COPRIME-TAIL-CONDUCTOR-COERCIVITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [O1](../1-in-progress/weil-positivity-five-structural-mechanisms.md)
- **Target:** For the tilted unit spline, a constant `a > 0` independent of `c,m` satisfies `a(log m − log c) ≤ E_m(c)` for all `c > 0`, `m ≥ 1`.

## Proof

Write `M = ∫φ²` and `J = ∫₁^∞ |φ̂(2πt)|² dt > 0`. In the positive coprime series for `E_m(c)`, retain `1 ≤ k ≤ floor(m/c)`. Every retained Fourier tail is at least `J`. The exact harmonic sieve inequality gives

`(φ(m)/m) H_N ≤ Σ_{k≤N,(k,m)=1} 1/k`.

Hence `E_m(c) ≥ (2J/M) H_floor(m/c)`. Since `H_floor(x) ≥ log x` for `x > 0`, the target follows with `a = 2J/M`. All factors of the totient cancel. Combining `tameDifferent(m) ≤ log m` yields coercivity against the conductor eigenvalue `γ + log m + tameDifferent(m)` with only logarithmic overlap loss.

## Audit

- Existing inputs: `hasSum_completedConductorEnergy`, `sieveDensity_mul_harmonicSum_le`, `integral_shellSpectrum_tiltedUnitSpline_pos`.
- The prime-divisor sieve has density `φ(m)/m` by Euler's product formula, and coprimality with its primorial is coprimality with `m`.
- `shellTail_mul_harmonicSum_le_completedConductorEnergy` proves the finite-prefix bound; `shellTail_mul_log_le_completedConductorEnergy` gives the logarithmic floor. `exists_tiltedUnitSpline_uniform_logarithmic_conductor_coercivity` discharges the profile conditions and proves the coefficient positive.
- Module: `RenormalizedArithmeticPotentialTheory/Conductor/CoprimeFourierOrder.lean`. Exact Lean check passed; capstone axioms are precisely `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.
- This scalar law alone does not supply O1's all-vector identity or edge payment.

## Gates

- [x] Exact target and source identified.
- [x] Dependency-closed paper proof audited.
- [x] Lean theorem, umbrella import and axiom audit.
