# Cofinal prime sawtooth incidence — formalized closure

- **ID:** `ccm-cofinal-prime-sawtooth-incidence-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-cofinal-prime-sawtooth-incidence-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCM.CCMSawtoothDilationMean` — the sawtooth, its mean, the bounded
  primitive, and the integration by parts.
- `GaloisForLFunctions.RHTower.CCM.CCMSawtoothDilationIncidence` — the arithmetic weight, the coordinate
  change, the synthesis, and the limit.
- `GaloisForLFunctions.RHTower.CCM.CCMSawtoothExteriorTail` — the exterior half-line and the full prime
  series.
- `GaloisForLFunctions.RHTower.SawtoothFourierSeries` — `tendsto_sum_sawtoothSine`, identifying the
  card's series `∑_{k≥1} sin(kθ)/k` with the closed-form sawtooth on `(0, 2π)`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)` | `sawUnit`, `sawWave`, `sawWave_eq_of_mem_Ioo`, `abs_sawWave_le`, `sawWave_add_two_pi`, and `tendsto_sum_sawtoothSine` | the sawtooth in closed form `S(x) = π(1/2 - {x/2π})`, with sup bound and period; the sine-series and closed-form definitions are proved to agree, so the closed form is not merely a definitional choice |
| `(2)` | `integral_sawUnit_dilate_piece`, `integral_sawUnit_dilate`, `integral_sawWave_dilate` | the `j`-th period of the fast factor contributes exactly `1/(12n²)`, uniformly in `j`, and there are `n` of them. The card uses Parseval on the sine series; the Lean proof pushes the dilation out of the integrand, translates each period, and integrates a quadratic — the mean is elementary, not spectral |
| integration setup | `integral_quadratic`, `integral_congr_of_Ioo`, `intervalIntegrable_sawUnit`, `intervalIntegrable_sawUnit_dilate` | interval integrals do not see the endpoint where the periodic closed form breaks, so the discontinuity of `S` costs nothing |
| `(3)`–`(4)` | `periodic_sawUnitDilate`, `sawDilatePrimitive`, `sawDilatePrimitive_periodic`, `abs_sawDilatePrimitive_le` | the centered product has period one and mean zero, hence a periodic primitive; `1/3` is an admissible uniform constant in unit normalization (the card's `C₀ = 2π³/3` is the same statement in the `2π` normalization) |
| `(24)` | `integral_sawUnit_comp_mul`, `abs_integral_sawUnit_le` | dilation divides the sawtooth primitive by the dilation, and the undilated primitive is bounded by `1/8` on the whole line |
| `(10)`, `(15)` | `endpointProfile`, `endpointProfile_mul_shift` | the endpoint profile shift identity |
| `(16)` | `sum_one_div_Icc_le_log`, `sum_vonMangoldt_div_le_log_sq` | sharpened to an inequality with no error term: `∑_{2 ≤ n ≤ N} 1/n ≤ log N`, so the visible weight is at most `log² N` exactly |
| `(17)` | `lseriesSummable_vonMangoldt_two`, `lseries_vonMangoldt_two` | absolute summability and the value `-ζ'(2)/ζ(2)`, from mathlib's von Mangoldt L-series identity |
| integration by parts | `intervalIntegrable_of_bound`, `integral_eq_integral_indicator`, `integral_deriv_mul_primitive` | the card's `(9)` holds only a.e. because `S` jumps. The Lean route proves a distributional integration by parts by Fubini on `{a ≤ t ≤ u ≤ b}`: `∫_a^b φ'(u)∫_a^u g = φ(b)∫_a^b g - ∫_a^b φ g`, valid for bounded measurable `g`. Only the smooth factor is differentiated |
| `(5)`–`(6)` | `continuous_sawDilatePrimitive`, `integral_sawDilateCentered_eq`, `abs_integral_weight_mul_sawDilateCentered_le` | against a `C¹` weight vanishing at both window ends, the dilated product agrees with its own mean up to `1/3` times the total variation of the weight, uniformly in the dilation |
| `(18)`, `(21)` | `abs_integral_invSqWeight_mul_sawDilate_partial_le`, `abs_integral_invSqWeight_mul_sawDilate_window_le` | the exterior window estimate with the absolute constant `13/8`, obtained per period and telescoped; no bounded-variation theory and no harmonic-sum tail bound |
| improper forms | `integrableOn_invSqWeight_mul_sawDilate`, `tendsto_integral_invSqWeight_mul_sawDilate`, `abs_integral_Ioi_invSqWeight_mul_sawDilate_le`, `abs_integral_Ioi_invSqWeight_mul_sawDilate_sub_mean_le` | both estimates on `(0,∞)`; integrability from the uniform bound `∫_L^T ‖·‖ ≤ 1/4`, and the limits are uniform in the outer endpoint |
| `(20)` | `image_Ioi_exp_scale`, `integral_comp_exp_scale_Ioi`, `integral_expWeight_Ioi_eq_invSqWeight` | the additive and multiplicative readings of the full exterior integral agree |
| `(22)`–`(23)` | `summable_fullPrimeResponse`, `tendsto_integral_Ioi_invSqWeight_mul_sawDilate`, `tendsto_fullPrimeResponse` | the series converges absolutely, uniformly in `L ≥ 1`, dominated by `(13/8)Λ(n)n^{-2}`; Tannery's theorem gives `P_L^full → (1/12)∑Λ(n)n^{-2}`, which by `(17)` is `-(π²/12)ζ'(2)/ζ(2)` in the card's normalization |

## Axioms

`#print axioms` on every theorem of all four modules returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Verification performed

- `lake env lean` on a scratch file importing all four modules: no errors, 205 declarations checked
  across this batch.
- `#print axioms` on every theorem: clean.
- Nothing the card proves is left unformalized; the card's remaining gates are its own open research
  items (constrained-prolate endpoint amplitude asymptotics, subleading incidence, true Weil
  Rayleigh-excess transfer).
