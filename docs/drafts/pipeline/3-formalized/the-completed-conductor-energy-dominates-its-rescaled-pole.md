# Completed conductor energy dominates its rescaled pole

- **ID:** COMPLETED-CONDUCTOR-RESCALING-ORDER
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [O1](../1-in-progress/weil-positivity-five-structural-mechanisms.md)
- **Target:** `E_m(c) ≥ E_1(c/m)` for every supported `C²` profile of positive square mass, `c > 0`, and `m ≥ 1`.

## Proof

For `T(x)=∫ₓ^∞|φ̂(2πt)|²dt`, the two energies are

`E_m(c) = (2/M) Σ_{a≥1} (m/φ(m)) 1_{(a,m)=1} T(ac/m)/a`,

`E_1(c/m) = (2/M) Σ_{a≥1} T(ac/m)/a`.

Every prefix of the difference of their harmonic weights is nonnegative by `sieveDensity_mul_harmonicSum_le`, applied to the prime divisors of `m`. Write these differences as `d_n`, their prefixes as `S_n`, and `w_n=T((n+1)c/m)`. Abel summation gives `Σ_{n<N} d_n w_n = S_N w_N + Σ_{n<N} S_{n+1}(w_n−w_{n+1}) ≥ 0`. Thus each pole prefix is bounded by the corresponding conductor prefix and hence by the complete conductor energy. Passing to the pole-series limit proves the target.

Together with the existing upper bound `E_m(c) ≤ (m/φ(m))E_1(c/m)`, this identifies the conductor scale directly. Below touching, the lower bound gives `E_m(c) ≥ log(m/c) + completeWeilSelfFinitePart φ 1`. Nonnegativity extends this to all overlaps with the constant replaced by its minimum with zero.

## Audit

- Existing pole-minimality compares `E_m(c)` with `E_1(c)`, at the same overlap. This target compares with the larger energy at `c/m`.
- Arithmetic bridge: Euler's totient product and prime-divisor coprimality identify the sieve density as `φ(m)/m`.
- Analytic transfer: `HTGeometry.sum_mul_weight_eq` and the two convergent Fourier series.
- `density_mul_weighted_harmonic_le_coprime` proves weighted sieve domination. `completedShellEnergy_div_conductor_le` proves the rescaled pole order; `log_conductor_sub_log_overlap_le_completedEnergy` gives the full-coefficient logarithmic floor.
- Module: `RenormalizedArithmeticPotentialTheory/Conductor/CoprimeFourierOrder.lean`. Exact Lean check passed; all three capstones use only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.
- This order law does not identify the complete finite-horizon matrix with its conductor limit.

## Gates

- [x] Exact target and corpus distinction identified.
- [x] Dependency-closed paper proof audited.
- [x] Exact Lean theorem, umbrella import and axiom audit.
