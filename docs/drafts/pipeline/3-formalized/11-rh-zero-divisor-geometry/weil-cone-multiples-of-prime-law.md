# Multiples-of-a-prime law of the Weil cone

- **ID:** MC-180
- **Stage:** 1-in-progress (paper proof complete; Lean written, not yet built)
- **Type:** THEOREM (paper)
- **Source:** MC conjecture loop cycle 180 (`mc-conjecture-loop-2026-09-28.md`); HF L172(b) semiprime-floor survivor
- **Statement:** If `lam` is full-cone Weil-positive and `|lam(n) − Λ(n)| ≤ C(1 + Λ(n))`, then for every prime `p` the sums `G_p(k) = Σ_{n≤k, p∣n}(lam − Λ)(n)/n` tend neither to `+∞` nor to `−∞`. If also `lam ≥ 0` on the multiples of `p` other than `p`, then `Σ_{p∣n, n≠p} lam(n)/n < ∞`.

## Goal
This is the first notch law valid for deviations of full size (`d ≍ Λ`, bounded composite weights). Every earlier notch result needed `d` to be small. Consequences:
- a Weil-positive weight system of bounded size carries finite harmonic mass on the multiples of each fixed prime, as `Λ` does;
- constant semiprime floors `lam(pq) ≥ c > 0` are not Weil-positive. HF L172(b) recorded these as surviving every multiplicative resonator.

## Paper proof
1. **Notch-boundedness.** If `|d| ≤ C(1 + Λ)`, then `d` satisfies the four `NotchSmall` size bounds at the fixed level `η = 2C`. This follows from Mertens, the square-root Chebyshev bound and the dyadic `n^{−3/2}` tail.
2. **Fibre law at a fixed level.** Run the refined-notch scale bound with `η` fixed. The errors are `C_η + η K log L` and the main term is `κ₁ Y log L`, where `κ₁` and `K` depend only on the twist `q = |Σ c_a e^{itλ(a)}|²`. So a `q`-fibre level `Y` that holds eventually satisfies `Y ≤ (K/κ₁) η`.
3. **Pinning.** For every Weil-positive `lam`, the harmonic windows `Σ d(n) φ(log n − L)/n` are `O(L^{−2})`. The local mass `Σ_{|log n − Z| ≤ ½} |d|/n` is at most `C(2 log 4 + 18)e^{½}`. The block identity then bounds the partial sums `Σ_{n<N} d(n)/n`.
4. **The twist `q = |1 + ε p^{it}|²`.** The main weight is `(1 + ε² + 2ε/√p) n^{−½}` off `pℕ` and `(1 + ε² + ε(√p + 1/√p)) n^{−½}` on `pℕ`. So the `q`-fibre sum equals `(1 + ε² + 2ε/√p) Σ_{n≤k} d/n + ε(√p − 1/√p) G_p(k)`.
   - If `G_p → ±∞`, take `ε = ±1`. The first coefficient is positive, the first sum is bounded and `√p > 1`, so the fibre sum exceeds every level. This contradicts step 2.
5. **Summability.** `Σ_{n≤k, p∣n} Λ(n)/n ≤ log p` (only powers of `p` contribute). With `lam ≥ 0` the partial sums of `lam/n` over `pℕ \ {p}` are monotone. Unbounded partial sums would force `G_p → +∞`.
6. **Semiprime floors.** Summability over `pℕ` gives `Σ_q c/(pq) < ∞` over primes `q`, which contradicts the divergence of `Σ 1/q`.

## Lean (written 2026-10-01, build pending)
- `PrimeSmallDeviationArithmetic`: `NotchBounded`, `NotchSmall.notchBounded`, `notchBounded_of_abs_le`. Checked clean with `lake env lean`.
- `WeilLittleOVonMangoldtRigidity`: `exists_ramp_scale_bound_bounded_of` (fixed-level core) and `le_of_log_scale_bound`. `exists_ramp_scale_bound_of` and `exists_tail_inv_le` are re-derived from them. Not yet built.
- New module `WeilConeMultiplesOfPrimeLaw`. Not yet built.
  - Main results: `exists_twistFibre_level_bound`, `exists_abs_sum_coneDeviation_div_le`, `twistMainWeight_primeSet`, `not_tendsto_atTop_multiplesSum`, `not_tendsto_atBot_multiplesSum`.
  - Corollaries: `summable_multiples_of_nonneg`, `not_weilPositiveFull_of_semiprime_floor`.
- The build was stopped by the system for low memory. Dependents (`WeilRoughFibreSignLaw`, `WeilFibreBochnerLaw`) need a rebuild after the refactor. The new module is not yet wired into `RHTower.lean`.

## Log
- 2026-10-01: created in 1-in-progress (cycle 180); paper proof complete; Lean written.

## Lean status (2026-10-01, final)
- Stage: 3-formalized. STATUS MUST-611.
- Compiled with `lake env lean` with no errors or warnings: `PrimeSmallDeviationArithmetic`, `WeilLittleOVonMangoldtRigidity` (refactor), `WeilRoughFibreSignLaw` and `WeilFibreBochnerLaw` (re-checked against the refactor), `WeilConeMultiplesOfPrimeLaw` (new). Oleans written with `lake env lean -o`.
- `#print axioms` (in a scratch file) gives `[propext, Classical.choice, Quot.sound]` for every main theorem.
- Wired into `GaloisForLFunctions/RHTower.lean` after `WeilFibreBochnerLaw`. Collision scan clean. The singleton prime-set helpers were renamed `primeSingleton`/`primePairCoeff` to avoid ambiguity with existing `primeSet`/`pairCoeff` in other namespaces.
- `lake build` audit deferred. Other agents' edits invalidated upstream modules (the `ThetaCuspHawkingBM…` and `Sieve.Ingham…` chains), so a module build would recompile hundreds of modules. The ~45 oleans removed by the memory-killed build were rebuilt one at a time.
- Main theorems: `not_tendsto_atTop_multiplesSum`, `not_tendsto_atBot_multiplesSum`, `summable_multiples_of_nonneg`, `not_weilPositiveFull_of_semiprime_floor`.
- Infrastructure: `exists_twistFibre_level_bound`, `exists_abs_sum_coneDeviation_div_le`, `localMass_le_of_abs_le`, `twistMainWeight_primeSingleton`, `sum_multiples_vonMangoldt_div_le`, `NotchBounded`, `notchBounded_of_abs_le`, `exists_ramp_scale_bound_bounded_of`, `le_of_log_scale_bound`.

## Open (next cycle)
- **Growing prime sets.** Fixed-`p` tests leave harmonic mass on integers with no prime factor below a slowly growing `z(n)` (rough semiprimes) unconstrained. The twist envelope costs `coordBound P = Π p^{2β_p}`. Reaching `z → ∞` needs an envelope of size `max a·a'` instead of a product.
- **Signed composite weights.** The summability corollary needs `lam ≥ 0` on `pℕ`. For signed `lam` only non-divergence holds.
