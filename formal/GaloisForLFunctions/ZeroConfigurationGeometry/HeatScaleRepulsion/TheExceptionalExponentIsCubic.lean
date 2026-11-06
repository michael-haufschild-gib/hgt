import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TheExceptionalSetHasAPowerSaving
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureAmplifiedInghamHuxleyDensity

/-!
# The exponent of the heat exceptional set

For `0 < κ ≤ 8`, the heights `X ∈ [T, 2T]` with `Λ_X log X > κ` have measure at most
`T^{1 − κ³/41943040000}` (`volume_localNewman_scaled_gt_le_exceptionalExponent`,
`exceptionalExponent_of_le`), and off a set of the same size every zero of `H_τ` over the unit window
is real for `τ ≥ 2κ/log X`.

The saving is cubic because of the level.  With `η = κ/64`, the complex saddle runs at
`|ζ| ≤ T^{η³/40000}`, and the second moment makes large values rare at that saving.  The zero shadow
saves `η/3` by Ingham–Huxley, far more, so large values are the only binding term.  The union bound
over a net of the unit window costs half of a saving, and the shadow-versus-moment comparison costs
the other half.
-/

set_option autoImplicit false

open Complex Set Filter MeasureTheory
open _root_.RHTower _root_.RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- **Atypical heights at an explicit level.**  For `ε ≤ η/6` the heights that are not typical at
level `T^ε` have measure at most `T^{1−ε/2}`: the shadows save `η/3 ≥ 2ε`, the second moment saves
`ε`. -/
theorem volume_not_zetaTypicalHeight_le_rpow_of_level {η ε : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hε : 0 < ε) (hεη : ε ≤ η / 6) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η ε T t} ≤
        ENNReal.ofReal (T ^ (1 - ε / 2)) := by
  have hε1 : ε ≤ 1 := by linarith only [hεη, hη8]
  set σ : ℝ := 1 / 2 + η / 4 with hσdef
  have hσ : 1 / 2 < σ := by rw [hσdef]; linarith only [hη]
  have hσ1 : σ ≤ 1 := by rw [hσdef]; linarith only [hη8]
  set g : ℝ := 1 - inghamHuxleyExponent σ * (1 - σ) with hg
  have hgη : η / 3 ≤ g := by
    have h := inghamHuxleyExponent_mul_le (s := η / 4) (by positivity) (by linarith only [hη8])
    rw [hg, hσdef]
    linarith only [h]
  have hg0 : 0 < g := by linarith only [hgη, hη]
  set ε' : ℝ := min 1 g with hε'
  have hε'0 : 0 < ε' := lt_min one_pos hg0
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  obtain ⟨C₁, hC₁, B, T₁, hT₁, hshadow⟩ :=
    exists_volume_zetaZeroShadow_le_inghamHuxley hσ hσ1 hε'0 hε'1
  obtain ⟨C₂, hC₂, hlarge⟩ := exists_volume_zetaLargeNear_le_rpow hε hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε') * (1 - σ) with hE
  have hEg : E ≤ 1 - g / 2 := by
    have hεg : ε' ≤ g := min_le_right _ _
    have h12 : 1 - σ ≤ 1 / 2 := by linarith only [hσ]
    have h0 : 0 ≤ 1 - σ := by linarith only [hσ1]
    rw [hE]
    have : ε' * (1 - σ) ≤ g / 2 := by nlinarith only [hεg, h12, h0, hε'0, hg0]
    nlinarith only [this, hg]
  have hdg : ε ≤ g / 2 := by linarith only [hεη, hgη]
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow B (c := ε / 2) (by positivity) (C₁ + C₂))
  refine ⟨max (max T₁ T₂) 6, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT6 : 6 ≤ T := le_trans (le_max_right _ _) hT
  have hT1 : 1 ≤ T := by linarith only [hT6]
  have hsub : {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η ε T t} ⊆
      (zetaZeroShadow σ 2 ∩ Icc T (2 * T)) ∪ zetaLargeNear T (T ^ ε) := by
    rintro t ⟨ht, hnt⟩
    by_contra hno
    simp only [mem_union, mem_inter_iff, not_or, not_and] at hno
    exact hnt ⟨ht, fun hs => hno.1 hs ht, hno.2⟩
  have hpoly1 : 1 ≤ (1 + Real.log T) ^ B :=
    one_le_pow₀ (by linarith only [Real.log_nonneg hT1])
  have hTE : T ^ E ≤ T ^ (1 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hEg, hdg])
  have hsum : C₁ * (1 + Real.log T) ^ B * T ^ E + C₂ * T ^ (1 - ε) ≤ T ^ (1 - ε / 2) := by
    have hTd : 0 ≤ T ^ (1 - ε) := by positivity
    have h1 : C₁ * (1 + Real.log T) ^ B * T ^ E ≤ C₁ * (1 + Real.log T) ^ B * T ^ (1 - ε) := by
      gcongr
    have h2 : C₂ * T ^ (1 - ε) ≤ C₂ * (1 + Real.log T) ^ B * T ^ (1 - ε) := by
      calc C₂ * T ^ (1 - ε) = C₂ * 1 * T ^ (1 - ε) := by ring
        _ ≤ C₂ * (1 + Real.log T) ^ B * T ^ (1 - ε) := by gcongr
    have h3 : (C₁ + C₂) * (1 + Real.log T) ^ B * T ^ (1 - ε) ≤ T ^ (ε / 2) * T ^ (1 - ε) := by
      gcongr
      exact hT₂ T hTT₂
    have h4 : T ^ (ε / 2) * T ^ (1 - ε) = T ^ (1 - ε / 2) := by
      rw [← Real.rpow_add (by linarith only [hT6])]
      ring_nf
    nlinarith only [h1, h2, h3, h4]
  calc volume {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η ε T t}
      ≤ volume ((zetaZeroShadow σ 2 ∩ Icc T (2 * T)) ∪ zetaLargeNear T (T ^ ε)) := measure_mono hsub
    _ ≤ volume (zetaZeroShadow σ 2 ∩ Icc T (2 * T)) + volume (zetaLargeNear T (T ^ ε)) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * (1 + Real.log T) ^ B * T ^ E) + ENNReal.ofReal (C₂ * T ^ (1 - ε)) :=
        add_le_add (hshadow T hTT₁) (hlarge T hT6)
    _ = ENNReal.ofReal (C₁ * (1 + Real.log T) ^ B * T ^ E + C₂ * T ^ (1 - ε)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (T ^ (1 - ε / 2)) := ENNReal.ofReal_le_ofReal hsum

/-- **The explicit exponent** `θ(κ) = 1 − η³/160000`, `η = min(κ/64, 1/8)`. -/
def exceptionalExponent (κ : ℝ) : ℝ :=
  1 - min (κ / 64) (1 / 8) ^ 3 / 160000

theorem exceptionalExponent_lt_one {κ : ℝ} (hκ : 0 < κ) : exceptionalExponent κ < 1 := by
  have hη : 0 < min (κ / 64) (1 / 8 : ℝ) := lt_min (by positivity) (by norm_num)
  have h : 0 < min (κ / 64) (1 / 8 : ℝ) ^ 3 / 160000 := by positivity
  unfold exceptionalExponent
  linarith only [h]

/-- In the range `κ ≤ 8` the exponent is `1 − κ³/41943040000`. -/
theorem exceptionalExponent_of_le {κ : ℝ} (hκ : κ ≤ 8) :
    exceptionalExponent κ = 1 - κ ^ 3 / 41943040000 := by
  have hmin : min (κ / 64) (1 / 8 : ℝ) = κ / 64 := min_eq_left (by linarith only [hκ])
  rw [exceptionalExponent, hmin]
  ring

/-- **The heat exceptional set with its exponent.** -/
theorem volume_localNewman_scaled_gt_le_exceptionalExponent {κ : ℝ} (hκ : 0 < κ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume {X | X ∈ Icc T (2 * T) ∧ κ < localNewmanConstant X * Real.log X} ≤
        ENNReal.ofReal (T ^ exceptionalExponent κ) := by
  set η : ℝ := min (κ / 64) (1 / 8) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη8 : η ≤ 1 / 8 := min_le_right _ _
  have hE0 : 0 < powerLevel η := by
    unfold powerLevel
    positivity
  have hη2 : η ^ 2 ≤ 1 := by nlinarith only [hη, hη8]
  have hEη : powerLevel η ≤ η / 6 := by
    unfold powerLevel
    have h : η ^ 3 ≤ η := by nlinarith only [hη, hη2]
    linarith only [h, hη]
  have hE1 : powerLevel η ≤ 1 := by linarith only [hEη, hη8]
  obtain ⟨T₁, hbad⟩ := volume_not_zetaTypicalHeight_le_rpow_of_level hη hη8 hE0 hEη
  obtain ⟨T₂, hrare⟩ := volume_not_powerTypicalWindow_le_of_typical (θ₁ := 1 - powerLevel η / 2) hη
    (by linarith only [hE1]) (by linarith only [hE0]) hbad
  have hexp : 1 - powerLevel η / 2 + (1 - (1 - powerLevel η / 2)) / 2 = exceptionalExponent κ := by
    rw [exceptionalExponent, powerLevel, ← hηdef]
    ring
  rw [hexp] at hrare
  exact volume_localNewman_scaled_gt_le_of_window hκ hrare

/-- **Reality of the heat zeros off the exceptional set.**  Off a set of measure
`T^{θ(κ/2)}`, every zero of `H_τ` over the unit window is real for `τ ≥ κ/log X`. -/
theorem volume_nonreal_heat_le_exceptionalExponent {κ : ℝ} (hκ : 0 < κ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume {X | X ∈ Icc T (2 * T) ∧ ∃ τ z, κ / Real.log X ≤ τ ∧ riemannHeat τ z = 0 ∧
        |z.re - X| ≤ 1 ∧ z.im ≠ 0} ≤ ENNReal.ofReal (T ^ exceptionalExponent (κ / 2)) := by
  obtain ⟨T₀, hvol⟩ := volume_localNewman_scaled_gt_le_exceptionalExponent (κ := κ / 2)
    (by positivity)
  refine ⟨max T₀ 8, fun T hT => ?_⟩
  refine (measure_mono ?_).trans (hvol T ((le_max_left _ _).trans hT))
  rintro X ⟨hXT, τ, z, hτ, hz, hre, him⟩
  refine ⟨hXT, ?_⟩
  have hT8 : 8 ≤ T := (le_max_right _ _).trans hT
  have hlog : 0 < Real.log X := Real.log_pos (by linarith only [hT8, hXT.1])
  have hτΛ := le_localNewmanConstant_of_nonreal hz him hre
  have hstart := (div_le_iff₀ hlog).mp hτ
  have hh := mul_le_mul_of_nonneg_right hτΛ hlog.le
  linarith only [hstart, hh, hκ]

end

end GaloisForLFunctions.ZeroConfigurationGeometry
