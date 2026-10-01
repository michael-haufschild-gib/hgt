# Exponential density of the Speiser shadow set

- **ID:** SPEISER-SHADOW-EXP
- **Stage:** 3-formalized
- **Type:** DENSITY THEOREM (unconditional)
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 72; builds on MUST-571, MUST-595/600
- **STATUS:** MUST-602

## Theorems [L]

Module `formal/GaloisForLFunctions/RHTower/SpeiserShadowExponentialDensity.lean` (wired, clean,
standard axioms).

- `exists_speiserShadow_exponential_density`. There are `A', K' ≥ 0` with the following property.
  For all large `U`, with `L = log U`, there are admissible `T₁ ∈ (U/4, U/4+1)` and
  `T₂ ∈ (U/2−1, U/2)` such that, for every `2 ≤ κ ≤ L/2 − 2`, the heights of `[T₁+½, T₂−½]` lying
  in the shadow `[γ − |β−½|, γ + |β−½|]` of some zero with `|β−½| ≥ κ/L` have measure
  `≤ A'(T₂−T₁)e^{−κ/2400} + K'L²`.
- `signs_of_not_mem_kappaShadow`. Off the κ-shadow set, at height `t ≥ 100`:
  - the Hadamard sign holds at every `Re s ≥ ½ + κ/L`;
  - `ζ' ≠ 0` at every `0 < Re s ≤ ½ − κ/L`.
- `sum_mul_sub_half_le_of_layer_bound`. A generic layer lemma: the tail moment
  `Σ_{Re w ≥ ½+κ/L} m_w(Re w − ½)` is bounded from exponential layer counts in steps `2/L`.
- `volume_speiserShadow_le`. Shadow measure ≤ 2 × tail moment.

## Relation to MUST-593/594

The same statement type (exceptional heights of density `e^{−cκ}` for the Hadamard and Speiser signs at distance `≥ κ/log T`) previously had `c = 10^{−9}/180`. The scale-data route paid for the `ζ'/ζ` box bound. Here `c = 1/2400`, from the corpus's direct near-line zero density, via the local disk laws. The exceptional set is explicit: it is the κ-shadow set.

## Limits

- The windows are the admissible `[T₁,T₂] ⊂ (U/4, U/2)` of MUST-571, not arbitrary dyadic intervals.
- `c = 1/2400` is inherited from the two-length mollifier. Selberg's `1/4` or Conrey's `8/7` would need stronger mollified gates.
- Fixed `κ` never gives density 0. That is (L).

## Addendum (cycle 73): dyadic windows [L]

`eventually_speiserShadow_dyadic_le`: for all large `T` and `2 ≤ κ ≤ log(4T)/2 − 2`, the κ-shadow set in `[T+2, 2T−2]` has measure `≤ A'Te^{−κ/2400} + K' log²(4T)`. The proof takes `U = 4T` in the admissible-window theorem.

## Addendum (cycle 100): area density one for the local RH signs [L] — MUST-618

Module `R:SpeiserShadowAreaDensity`.

- `exists_localSignFail_far_area`: at horizontal distance `≥ κ/L`, the failure set of both local signs in the window has area `≤ A'(T₂−T₁)e^{−κ/2400} + K'L²`. The proof uses product sets `[0,1] × κ-shadow` and `signs_of_not_mem_kappaShadow`.
  - Hadamard: `ξ ≠ 0`, `Re ξ'/ξ ≥ 0` for `Re s > ½`.
  - Speiser: `ζ' ≠ 0` for `Re s < ½`.
- `exists_hadamardSpeiser_area_density_one`: for every `ε > 0` and all large `U`, admissible windows exist on which the failure set `localSignFailSet T₁ T₂` (inside `0 < Re s < 1`) has area `≤ ε(T₂ − T₁)`.

Before this, the corpus had 58% of the area (`eventually_volume_hadamardSign_ge`, from the linear off-line moment). The improvement comes from the exponential near-line density at a fixed `κ = κ(ε)` plus the near-line strip of area `(2κ/L)ΔT`.

## Addendum (cycle 101): Hadamard failure area is `O(T/log T)` [L] — MUST-620

Module `R:HadamardFailAreaCriticalScale`.

`exists_hadamardFail_area_le_div_log`: there is `C ≥ 0` such that, for all large `U` and on admissible windows, the Hadamard failure set has area `≤ C(T₂−T₁)/log U`. The failure set is `{½ < Re s, T₁+½ ≤ Im s ≤ T₂−½, ¬(ξ ≠ 0 ∧ Re ξ'/ξ ≥ 0)}`.

This is the natural critical-scale order. Speiser's sign fails only on the countable set of zeros of `ζ'`, which has area 0, so the Hadamard bound is the whole area content of MUST-618.

Proof:
- **Near strip.** Failures with `Re s − ½ < 2/L` have area `≤ (4/L)ΔT`.
- **Far failures.** These lie in the rectangles `hadamardRect ρ` of zeros with `b ≥ 2/L`, of total area `≤ 2Σ m b²` (`volume_hadamardFail_window_le`).
- **Layer trick.** `b² ≤ (4/L)Σ_{1≤k≤M}[b ≥ 2k/L]b` (`sq_le_four_div_mul_sum_indicator`), so `Σ m b² ≤ (4/L)Σ_k tail(2k)` (`sum_mul_sq_le_of_tail`).
- **Tail bound.** Each tail is bounded by the MUST-602 layer bound at the clipped scale `min(2k, L/2−2)`.
- **Sum.** `Σ_k ≤ (2/π)(2402·1201·D + (L/4+1)²KL)`, and `L³ ≪ ΔT`.
