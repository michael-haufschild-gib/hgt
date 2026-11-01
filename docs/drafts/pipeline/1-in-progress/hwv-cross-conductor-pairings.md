# Cross-conductor pairings of the complete Weil form against the conductor margin

- **ID:** hwv-cross-conductor
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** HWV README §8 topic 1 (top coprime stratum); `totient_mul_conductorEnergy_eq`
- **Statement:** Bound the cross-conductor pairings `⟨W_{c,N} r_e, r_{e'}⟩`, `e ≠ e'`, and the
  quasimode residuals below the conductor margin `E_m(c) ≍ E(c/m)`, uniformly in `N`.

## Goal
Positivity of the top coprime stratum against the strata below with `N`-independent constants.

## Status (tilted unit spline, overlap `c = (log N)^α`)
- Relative bound (residual channel / `√(E_e E_{e'})`), conductors up to `(log N)^A`:
  `O(c⁸ (log N)^{−1+ε})`, so below the margins for every `α < 1/8`
  (`exists_relative_conductorDeviation_sum_le`, from CACT bilinear residuals).
- Whole space below `1/9`: every conductor family, lcm margins for all `m ≤ N`
  (`eventually_conductorGram_ge_floor`, `eventually_lcmCrossPairings_le_margin`).
- Each fixed conductor below `1/8` (`eventually_lcmCrossPairings_le_margin_below_one_eighth`).
- RH ⇔ conductor Gram over all conductors PSD at every `2K(log N)^{1/8}`
  (`riemannHypothesis_iff_conductorGram_nonneg_eighthRoot`).
- Mean square: residual channels `o(Σ E_e²)` for `e ≤ N^θ`, all `α < 1/2`
  (`tendsto_conductorDeviation_rhComplete`).
- Exact identities: lcm law (`sum_moebius_starPoleEnergy_completeWeil`,
  `totient_mul_conductorEnergy_eq_lcm`); conductors are a basis (`eq_sum_conductorCoordinate`).

## Open
- The constant at the eighth root: the leading `c/log N` term of the bilinear residual against
  the margin constant `κ₀`, at `c⁸ ≍ log N`.
- Whole space from `1/9` to `1/8`: the complement of the polylogarithmic conductor subspaces.
  Open in the corpus; structure and route on `off-pole-nonratio-cross-and-one-eighth-weil-positivity.md`.

## No-go closure
- **Exact killing theorem/mechanism:** the generic relative bound has the RH exponent `1/8`;
  at every multiple of `(log N)^{1/8}` quadratic control over all conductors is RH.
- **Strongest positive survivor:** lcm law, conductor basis, relative bound for every `α < 1/8`,
  whole space below `1/9`, mean square past `1/8`.
- **New insight:** what remains is a constant, not an exponent; averages cannot decide because
  the mean square is carried by the large margins.
- **Status:** modules `TheConductorGramIsGradedByTheLcm`, `TheCrossConductorPairings`.

## Log
- 2026-11-01 — created; two HWV modules.
