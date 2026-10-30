# Coprime Fourier tails control logarithmic conductors

- **ID:** COPRIME-TAIL-CONDUCTOR-COERCIVITY
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [O1](weil-positivity-five-structural-mechanisms.md)
- **Target:** For the tilted unit spline, a constant `a > 0` independent of `c,m` satisfies `a(log m − log c) ≤ E_m(c)` for all `c ≥ 1`, `m ≥ 1`.

## Mechanism

Write `M = ∫φ²` and `J = ∫₁^∞ |φ̂(2πt)|² dt > 0`. In the positive coprime series for `E_m(c)`, retain `1 ≤ k ≤ floor(m/c)`. Every retained Fourier tail is at least `J`. The exact harmonic sieve inequality gives

`(φ(m)/m) H_N ≤ Σ_{k≤N,(k,m)=1} 1/k`.

Hence `E_m(c) ≥ (2J/M) H_floor(m/c)`. Since `H_N ≥ log(N+1)`, this proves the target with `a = 2J/M` when `m ≥ c`; nonnegativity covers `m < c`. All factors of the totient cancel. Combining `tameDifferent(m) ≤ log m` yields coercivity against the conductor eigenvalue `γ + log m + tameDifferent(m)` with only logarithmic overlap loss.

## Audit

- Existing inputs: `hasSum_completedConductorEnergy`, `sieveDensity_mul_harmonicSum_le`, `integral_shellSpectrum_tiltedUnitSpline_pos`.
- Verify the prime-divisor sieve has density `φ(m)/m` and the same coprimality predicate as `m`.
- Formalize the finite prefix comparison and floor/logarithm step.
- This scalar law alone does not supply O1's all-vector identity or edge payment.

## Gates

- [x] Exact target and source identified.
- [ ] Dependency-closed paper proof audited.
- [ ] Lean theorem, umbrella import and axiom audit.
