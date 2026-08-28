# Index / near-miss rigidity (C8) — state after the second assault (2026-08-28)

Card: `docs/drafts/pipeline/1-in-progress/index-parity-near-miss-rigidity.md` (full record there).

## Where attack surface A ended

- **T2/E mining verdict:** no proved corpus layer meets the carrier spec. "Signed subhalf
  continuation" is T2's OPEN item; the CCM window cluster states explicitly that all-x one-sided
  subpower θ-error bounds ⟺ the RH window gate (receiver, not supply).
- **Ingham closure:** ALL-x one-sided `ψ(x)−x ≥ −Kx^θ` already implies no zeros right of θ
  (Landau nonneg-Mellin + no real zeros of ζ in (0,1)) — the all-x spec is quasi-RH, circular.
- **Uniform anomaly upgrade:** under finite κ the anomaly law is UNIFORM (von Koch on the
  on-line rest): `ψ(x) = x − Σ_quad 2Re(x^ρ/ρ) + O(√x log²x)`. Refutation needs only ONE
  unbounded scale sequence in the (measure-1/3) deep valley.
- **Complete no-go taxonomy (all-x technologies exhausted):** (i) zero-side evaluations blind by
  self-inclusion (all quadratic/variance carriers — the hypothetical zero's term sits inside the
  bound's own proof); (ii) relative-scale sieve bounds blind to o(h) (kill only β=1);
  (iii) exact ζ-identities blind by resonance-vanishing (Σ_{m≤x}m^{−ρ} kills its own resonance
  because ζ(ρ)=0); (iv) resonant-phase exponential sums = Vinogradov–Korobov = the zero-free
  region wall. In-world (κ=1-counterfactual) routes unwind to (i) and (iv): REDISCOVERED wall.
- **C11 (purified target, = C8 in sequence form):** ∀ γ>0, φ, β∈(1/2,1), δ>0 ∃ arbitrarily
  large u with cos(γu+φ) ≤ −1/2 and (ψ(e^u)−e^u)e^{−βu} ≥ −δ. Not a lemma — new technology by
  construction; uncharted (no known obstruction), not known-hard. A is PARKED at C11.

## Permanent Lean assets from A (umbrella-wired, axioms propext/Classical.choice/Quot.sound)

- `HTGeometry/CosineValleyWindowFloor.lean`: `cosDeepSublevel` def; period-window measure exactly
  2π/3 at EVERY window position (indicator-periodicity + interval-integral transfer);
  n-window exactness; `le_volume_cosDeepSublevel_inter_Ioc` (≥ (b−a)/3 − 2π/3 in every window);
  `le_volume_cos_valley_window` (valley of cos(γu+φ) in (0,U] has measure ≥ U/3 − 2π/(3γ), all
  γ>0, φ — affine transport via `Real.map_volume_mul_left` + `measure_preimage_add_right`);
  `exists_valley_mem_of_volume_compl_lt` (pigeonhole: complement measure < floor ⟹ G meets the
  valley; NO measurability of G needed — outer-measure monotonicity).
- `RHTower/WindowBudgetUnconditionalSupply.lean`: `primeWindowSupply_of_pos` (WindowBudget's
  interface Prop at EVERY L>0, from `exists_prime_log_window`, removing Bertrand's log 2 bound);
  `exists_prime_sin_pos/neg_unconditional` (sine steering with floor √2/2 at EVERY frequency,
  cofinally); `exists_prime_mirrorTiltIncrement_pos/neg_unconditional` (defect walk steers both
  ways at every interior strip point). Missing forever at this level: AMPLITUDE (single primes
  move walks by ~log q; the valley demands x^β).

## Lean traps hit this cycle

- `Mathlib.MeasureTheory.Integral.Periodic` moved to
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic` (olean path).
- `Function.Periodic.intervalIntegral_add_eq` needs NO integrability hypothesis.
- `le_or_lt` unknown in this toolchain — use `le_or_gt`; ENNReal `0 ≤ x` is `exact zero_le`
  (implicit arg, NOT `zero_le _`); `mul_le_mul_left'` deprecated → `gcongr`;
  interval-integral ↔ volume via `integral_indicator` + `Set.indicator_indicator` +
  `integral_indicator_const` + `simp [MeasureTheory.measureReal_def]`.
- Lint currently reports 3 unreachable modules from OTHER agents (TwoLocalProjectiveTrotter…,
  UniversalRecurrenceOccupation…, WeightedComplexSumConcentration) — pre-existing, not ours.

## Next

Loop continues on the parent programme's live track: CP-1/2/3 (theta-kernel CP/deficit
domination card) on the Lean split foundation (`ThetaTailKernelGeometricDeficitSplit`):
Schur-test for D against M's square family on separation-restricted packets is the first
theorem candidate (CP-1).
