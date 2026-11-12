import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquareOfTheCubicThetaUnfolds

/-!
# The square of the projected theta function unfolds

The projected cubic theta function `θ_s = cubicSourceResidualFunction` (MMD) is automorphic for the
level-three group with the cubic multiplier `κ` (`sourceTheta_automorphy`) and equals its absolutely
convergent Fourier series `Σ_h b(v, h) e(ξ_h z)` at every height (`cubicSourceResidualFunction_fourier_expansion`),
with `b(v, h) = T_s(h) v K_{1/3}(4π|ξ_h| v)` for `h ≠ 0`. Its coefficients `T_s` are the arithmetic
ones: `T_s(h b³) = |b| T_s(h)`, `T_s(−h) = T_s(h)`, and the squarefree formula of MMD.

* `integral_cuspCharacterSeries_sq` (**Parseval on `P`**): for summable `a`,
  `∫_P (Σ_h a_h e(ξ_h z))² dz = |P| Σ_h a_h a_{−h}`.
* `integral_sq_mul_incompleteEisenstein` (**Rankin–Selberg for a square**): for `F` of multiplier `κ`
  whose horizontal Fourier series converge absolutely,
  `∫_{D_Γ} F² E(·∣ψ) = |P| ∫_0^∞ ψ(v) Σ_h a(v, h) a(v, −h) v^{−3} dv`.
* `integral_sourceThetaSq_mul_incompleteEisenstein`: the instance `F = θ_s`, unconditional for
  continuous `ψ` of compact support in `(0, ∞)`, with
  `b(v, h) b(v, −h) = T_s(h)² v² K_{1/3}(4π|ξ_h| v)²` for `h ≠ 0` (`sourceAmplitude_mul_neg`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein

/-! ### Parseval on the period parallelogram -/

theorem tracePhase_continuous (h : O) : Continuous (fun z : ℂ => tracePhase (cuspFrequency h * z)) := by
  change Continuous (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I *
    ((cuspFrequency h * z) + starRingEnd ℂ (cuspFrequency h * z))))
  fun_prop

theorem norm_cuspCharacterSeries_le (a : O → ℂ) (ha : Summable (fun h => ‖a h‖)) (z : ℂ) :
    ‖cuspCharacterSeries a z‖ ≤ ∑' h : O, ‖a h‖ := by
  unfold cuspCharacterSeries
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun h => ?_))
  · exact ha.congr fun h => by rw [norm_mul, tracePhase_norm, mul_one]
  · rw [norm_mul, tracePhase_norm, mul_one]

/-- **Parseval on `P`.** `∫_P (Σ_h a_h e(ξ_h z))² dz = |P| Σ_h a_h a_{−h}`. -/
theorem integral_cuspCharacterSeries_sq (a : O → ℂ) (ha : Summable (fun h => ‖a h‖)) :
    ∫ z in periodDomain, cuspCharacterSeries a z ^ 2 = periodArea * ∑' h : O, a h * a (-h) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hSc : Continuous (cuspCharacterSeries a) := cuspCharacterSeries_continuous a ha
  have hfin : volume periodDomain ≠ ⊤ := by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top
  have hi : ∀ h : O, Integrable (fun z : ℂ => a h * (cuspCharacterSeries a z *
      tracePhase (cuspFrequency h * z))) (volume.restrict periodDomain) := fun h =>
    integrableOn_periodDomain_of_continuous _
      (continuous_const.mul (hSc.mul (tracePhase_continuous h)))
  have hpt : ∀ (h : O) (z : ℂ), ‖a h * (cuspCharacterSeries a z * tracePhase (cuspFrequency h * z))‖ ≤
      ‖a h‖ * ∑' k : O, ‖a k‖ := by
    intro h z
    rw [norm_mul, norm_mul, tracePhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_cuspCharacterSeries_le a ha z) (norm_nonneg _)
  have hint_le : ∀ h : O, ∫ z in periodDomain,
      ‖a h * (cuspCharacterSeries a z * tracePhase (cuspFrequency h * z))‖ ≤
        ‖a h‖ * (∑' k : O, ‖a k‖) * (volume periodDomain).toReal := by
    intro h
    have hc : IntegrableOn (fun _ : ℂ => ‖a h‖ * ∑' k : O, ‖a k‖) periodDomain :=
      integrableOn_const (μ := volume) hfin
    calc _ ≤ ∫ _ in periodDomain, ‖a h‖ * ∑' k : O, ‖a k‖ :=
          setIntegral_mono_on (hi h).norm hc periodDomain_measurable (fun z _ => hpt h z)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
  have hsum : Summable (fun h : O => ∫ z in periodDomain,
      ‖a h * (cuspCharacterSeries a z * tracePhase (cuspFrequency h * z))‖) :=
    Summable.of_nonneg_of_le (fun h => integral_nonneg fun z => norm_nonneg _) hint_le
      ((ha.mul_right _).mul_right _)
  have hsq : ∀ z : ℂ, cuspCharacterSeries a z ^ 2 =
      ∑' h : O, a h * (cuspCharacterSeries a z * tracePhase (cuspFrequency h * z)) := by
    intro z
    calc cuspCharacterSeries a z ^ 2 = cuspCharacterSeries a z * cuspCharacterSeries a z := sq _
      _ = ∑' h : O, cuspCharacterSeries a z * (a h * tracePhase (cuspFrequency h * z)) :=
          tsum_mul_left.symm
      _ = _ := tsum_congr fun h => by ring
  simp_rw [hsq]
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  calc ∑' h : O, ∫ z in periodDomain, a h * (cuspCharacterSeries a z * tracePhase (cuspFrequency h * z))
      = ∑' h : O, periodArea * (a h * a (-h)) := tsum_congr fun h => by
        have hk := cuspCharacterSeries_fourier a ha (-h)
        simp only [cuspFrequency_neg, neg_neg] at hk
        rw [integral_const_mul, hk]
        ring
    _ = _ := tsum_mul_left

/-! ### Rankin–Selberg for a square -/

/-- **Rankin–Selberg for a square.** Let `F` have multiplier `κ` and absolutely convergent horizontal
Fourier series `F(z + jv) = Σ_h a(v, h) e(ξ_h z)`. If `F² ψ(v)` is integrable on the strip, then
`∫_{D_Γ} F² E(·∣ψ) = |P| ∫_0^∞ ψ(v) Σ_h a(v, h) a(v, −h) v^{−3} dv`. -/
theorem integral_sq_mul_incompleteEisenstein (F : HyperbolicSpace → ℂ)
    (hF : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = complexCharacter M * F w)
    (a : ℝ → O → ℂ) (hsum : ∀ v : ℝ, 0 < v → Summable (fun h => ‖a v h‖))
    (hexp : ∀ (v : ℝ) (hv : 0 < v) (z : ℂ), F (upperPoint z v hv) = cuspCharacterSeries (a v) z)
    (ψ : ℝ → ℂ) (hint : IntegrableOn (unfolded (fun w => F w ^ 2) ψ) cuspStripSet hyperbolicVolume) :
    ∫ w in levelSet, F w ^ 2 * incompleteEisenstein ψ w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), ψ v * (periodArea * ∑' h : O, a v h * a v (-h)) / (v : ℂ) ^ 3 := by
  have hF2 : ∀ (M : levelThree) (w : HyperbolicSpace),
      F (complexMatrix M • w) ^ 2 = (complexCharacter M)⁻¹ * F w ^ 2 := by
    intro M w
    have h3 := complexCharacter_cube M
    have hne : complexCharacter M ≠ 0 := by
      intro h
      rw [h] at h3
      norm_num at h3
    rw [hF, mul_pow]
    field_simp
    linear_combination F w ^ 2 * h3
  refine (integral_mul_incompleteEisenstein_eq_constantTerm (fun w => F w ^ 2) hF2 ψ hint).trans ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hlift : ∀ z : ℂ, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z =>
    cuspCoordinateLift_positive v z hv
  simp only [hlift, hexp v hv]
  rw [integral_cuspCharacterSeries_sq (a v) (hsum v hv)]

/-! ### The projected theta function -/

/-- The projected cubic theta function `θ_s`. -/
abbrev sourceTheta : HyperbolicSpace → ℂ := cubicSourceResidualFunction

/-- `θ_s` has multiplier `κ` on the level-three group. -/
theorem sourceTheta_automorphy (M : levelThree) (w : HyperbolicSpace) :
    sourceTheta (complexMatrix M • w) = complexCharacter M * sourceTheta w := by
  have h := cubicSourceResidualFunction_automorphy
    ⟨(M : SL(2, O)), RationalSource.levelThree_le_rationalExtension M.2⟩ w
  rw [RationalSource.extendedComplexCharacter_restrict M] at h
  exact h

/-- For `h ≠ 0`, `b(v, h) b(v, −h) = T_s(h)² v² K_{1/3}(4π|ξ_h| v)²`. -/
theorem sourceAmplitude_mul_neg (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    rationalSourceModeAmplitude v h * rationalSourceModeAmplitude v (-h) =
      rationalSourceResidualFourierCoefficient h ^ 2 * (v : ℂ) ^ 2 *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) ^ 2 := by
  rw [rationalSourceModeAmplitude_bessel v hv h hh,
    rationalSourceModeAmplitude_bessel v hv (-h) (neg_ne_zero.mpr hh),
    rationalSourceResidualFourierCoefficient_neg, cuspFrequency_neg, norm_neg]
  ring

/-- **Rankin–Selberg for `θ_s²`.** For `ψ` continuous and supported in `[a, b] ⊂ (0, ∞)`:
`∫_{D_Γ} θ_s² E(·∣ψ) dμ = |P| ∫_0^∞ ψ(v) Σ_h b(v, h) b(v, −h) v^{−3} dv`. -/
theorem integral_sourceThetaSq_mul_incompleteEisenstein (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hsupp : ∀ v, v ∉ Set.Icc a b → ψ v = 0) :
    ∫ w in levelSet, sourceTheta w ^ 2 * incompleteEisenstein ψ w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), ψ v * (periodArea * ∑' h : O,
        rationalSourceModeAmplitude v h * rationalSourceModeAmplitude v (-h)) / (v : ℂ) ^ 3 := by
  have hc : Continuous (unfolded (fun w => sourceTheta w ^ 2) ψ) :=
    (cubicSourceResidualFunction_continuous.pow 2).mul (hψ.comp hyperbolicHeight_continuous)
  have hint : IntegrableOn (unfolded (fun w => sourceTheta w ^ 2) ψ) cuspStripSet hyperbolicVolume := by
    refine (cuspStrip_integrable_continuous a b ha _ hc).of_forall_sdiff_eq_zero
      cuspStripSet_measurable fun w hw => ?_
    have hv : hyperbolicHeight w ∉ Set.Icc a b := fun hv => hw.2 ⟨hw.1, hv⟩
    simp only [unfolded, hsupp _ hv, mul_zero]
  exact integral_sq_mul_incompleteEisenstein sourceTheta sourceTheta_automorphy
    rationalSourceModeAmplitude rationalSourceModeAmplitude_summable
    cubicSourceResidualFunction_fourier_expansion ψ hint

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
