# Global squared-depth dissipation for the actual heat divisor

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q3/functional.
- **Target:** For `t>0`, the sum of squared imaginary parts of all nonreal heat
  zeros, with multiplicity, is finite and obeys
  `E(b)+2∫_a^b N(t)dt≤E(a)` for `0<a≤b`.

## Candidate mechanism

For a finite simple conjugation-invariant packet with velocity
`z_i'=2Σ_{j≠i}(z_i−z_j)⁻¹`, symmetrization gives
`E'=-4Σ_{i<j}(Im z_i−Im z_j)²/|z_i−z_j|²≤-2N`.
Every conjugate pair contributes exactly four. Real exterior zeros contribute
nonpositive imaginary work. For the actual heat function, prove this sign from
the full canonical product after placing every nonreal zero inside the packet.
The existing collision continuation then supplies the integrated inequality.

## Canonical-product input

`RHTower.logDeriv_eq_tsum_of_even` supplies the absolutely convergent
renormalized field `Σ(1/(z−a)+1/a)` for every even entire function with the
proved order-one envelope. Apply it to `riemannHeat t`. The finite nonreal
copy set is closed under `a↦−a`, so its counterterms sum to zero. Each real
exterior copy contributes imaginary part `−Im z/|z−a|²`. Thus the exterior
work has the required sign before taking the regular part at a simple zero.

## Exact unresolved inputs

- Specialize the full field and pass its sign to the regular part at each zero.
- Use the uniform Ki–Kim–Lee confinement on positive-time intervals.
- Collision continuation for the global finite sum.

Finiteness of `E(0)` is separate and presently unproved. Positive-time
dissipation alone does not bound growth as `t↓0`.
