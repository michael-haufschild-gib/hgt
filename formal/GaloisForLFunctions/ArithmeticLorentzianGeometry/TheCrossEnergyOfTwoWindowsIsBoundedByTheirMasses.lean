import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheArchimedeanCrossEnergyIsOneSided

/-!
# The cross energy of two windows is bounded by their masses

`TheArchimedeanCrossEnergyIsOneSided` bounds the Lévy cross term of two windows by
`‖G_m‖₂‖G_n‖₂` times the Lévy mass of their pair window, `2w ω(s − w)`. Integrating the correlation
first loses nothing: `∫ |c_{mn}| ≤ ‖G_m‖₁‖G_n‖₁ ≤ w ‖G_m‖₂‖G_n‖₂` by Fubini, where the pair window
charged `2w`. The cross penalty halves.

* **The correlation** (`continuous_pairCorr`, `integral_abs_pairCorr_le`): `τ ↦ c_{mn}(τ)` is
  continuous, supported in `[−w, w]`, and `∫ |c_{mn}| ≤ ‖G_m‖₁ ‖G_n‖₁`.
* **One pair** (`integral_levy_abs_pairCorr_le`, `integral_levy_abs_pairCorr_eq_zero`): at
  log-distance `s ≥ 2w` the Lévy-weighted correlation is at most `ω(s − w) ‖G_m‖₁ ‖G_n‖₁`; at
  `s ≤ −2w` it vanishes on `(0, ∞)`.
* **The Lévy energy with masses** (`levyEnergy_windowTest_ge_masses`) and **the halved cross
  penalty** (`levyEnergy_windowTest_ge_fubini`):
  `levyEnergy f ≥ Σ levyEnergy G_m − (wN/2)[(2(1 + 1/λ)/(1 − κ)) D_N(y) + L_λ,κ |y|²]`.
* **The Markov form** (`eventually_markovEnergy_windowTest_ge_fubini`): the lower bound of
  `eventually_markovEnergy_windowTest_ge_sharp` with both cross constants halved.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

variable {G : ℕ → ℝ → ℝ} {w : ℝ}

/-! ### The correlation of two windows -/

theorem pairCorr_eq_setIntegral (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) (τ : ℝ) :
    pairCorr G m n τ = ∫ v in Set.Icc 0 w, G m v * G n (v + τ) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by
    rw [hGsupp m v hv, zero_mul]).symm

theorem continuous_pairCorr (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) : Continuous (pairCorr G m n) := by
  have h : Continuous fun τ => ∫ v in Set.Icc 0 w, G m v * G n (v + τ) :=
    continuous_parametric_integral_of_continuous (f := fun τ v => G m v * G n (v + τ))
      (((hG m).continuous.comp continuous_snd).mul
        ((hG n).continuous.comp (continuous_snd.add continuous_fst))) isCompact_Icc
  exact (funext fun τ => pairCorr_eq_setIntegral hGsupp m n τ) ▸ h

theorem integrable_abs_pairCorr (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) :
    Integrable fun τ => |pairCorr G m n τ| := by
  refine (continuous_pairCorr hG hGsupp m n).abs.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-w) w) isCompact_Icc fun τ hτ => ?_
  have : w < |τ| := by
    by_contra h
    exact hτ (abs_le.mp (not_lt.mp h))
  rw [pairCorr_eq_zero hGsupp m n this, abs_zero]

/-- **Fubini**: `∫ |c_{mn}| ≤ ‖G_m‖₁ ‖G_n‖₁`. -/
theorem integral_abs_pairCorr_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) :
    ∫ τ, |pairCorr G m n τ| ≤ (∫ v, |G m v|) * ∫ v, |G n v| := by
  set F : ℝ → ℝ → ℝ := fun τ v => |G m v| * |G n (v + τ)|
  have hFc : Continuous (Function.uncurry F) :=
    ((hG m).continuous.comp continuous_snd).abs.mul
      ((hG n).continuous.comp (continuous_snd.add continuous_fst)).abs
  have hFs : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro (K := Set.Icc (-w) w ×ˢ Set.Icc 0 w)
      (isCompact_Icc.prod isCompact_Icc) fun p hp => ?_
    obtain ⟨τ, v⟩ := p
    simp only [Function.uncurry_apply_pair, F]
    by_cases hv : v ∈ Set.Icc 0 w
    · by_cases hvτ : v + τ ∈ Set.Icc 0 w
      · exfalso
        exact hp ⟨⟨by linarith [hv.2, hvτ.1], by linarith [hv.1, hvτ.2]⟩, hv⟩
      · rw [hGsupp n _ hvτ, abs_zero, mul_zero]
    · rw [hGsupp m _ hv, abs_zero, zero_mul]
  have hF : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hFc.integrable_of_hasCompactSupport hFs
  have hpt : ∀ τ, |pairCorr G m n τ| ≤ ∫ v, F τ v := fun τ => by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    simp only [F, abs_mul]
  have hleft : Integrable fun τ => ∫ v, F τ v := hF.integral_prod_left
  calc ∫ τ, |pairCorr G m n τ| ≤ ∫ τ, ∫ v, F τ v :=
        integral_mono (integrable_abs_pairCorr hG hGsupp m n) hleft hpt
    _ = ∫ v, ∫ τ, F τ v := integral_integral_swap hF
    _ = ∫ v, |G m v| * ∫ τ, |G n τ| := by
        refine integral_congr_ae (ae_of_all _ fun v => ?_)
        simp only [F]
        rw [integral_const_mul, integral_add_left_eq_self (fun τ => |G n τ|) v]
    _ = (∫ v, |G m v|) * ∫ v, |G n v| := integral_mul_const _ _

/-! ### One pair -/

theorem integrableOn_levy_abs_pairCorr (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) {s : ℝ} (hs : 2 * w ≤ |s|)
    (m n : ℕ) :
    IntegrableOn (fun t => archLevyDensity t * |pairCorr G m n (t - s)|) (Set.Ioi 0) := by
  have hwin := (window_integrable_and_le hw0 hs).1
  refine Integrable.mono' (hwin.const_mul (windowNorm G m * windowNorm G n))
    ((RHTower.measurable_archLevyDensity.mul
      ((continuous_pairCorr hG hGsupp m n).comp (continuous_sub_right s)).abs.measurable)
      |>.aestronglyMeasurable) ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht => ?_))
  have hω : 0 ≤ archLevyDensity t := (archLevyDensity_pos ht).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hω (abs_nonneg _))]
  by_cases hmem : t ∈ Set.Icc (s - w) (s + w)
  · rw [Set.indicator_of_mem hmem]
    have := abs_pairCorr_le hG hGsupp m n (t - s)
    nlinarith
  · rw [Set.indicator_of_notMem hmem, mul_zero]
    have hout : w < |t - s| := by
      by_contra h
      obtain ⟨h1, h2⟩ := abs_le.mp (not_lt.mp h)
      exact hmem ⟨by linarith, by linarith⟩
    rw [pairCorr_eq_zero hGsupp m n hout, abs_zero, mul_zero]

/-- **One pair to the right**: at log-distance `s ≥ 2w`,
`∫_0^∞ ω(t) |c_{mn}(t − s)| dt ≤ ω(s − w) ‖G_m‖₁ ‖G_n‖₁`. -/
theorem integral_levy_abs_pairCorr_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) {s : ℝ} (hs : 2 * w ≤ s)
    (m n : ℕ) :
    ∫ t in Set.Ioi 0, archLevyDensity t * |pairCorr G m n (t - s)| ≤
      archLevyDensity (s - w) * ((∫ v, |G m v|) * ∫ v, |G n v|) := by
  have hint := integrableOn_levy_abs_pairCorr hG hGsupp hw0 (s := s)
    (by rw [abs_of_nonneg (by linarith)]; exact hs) m n
  have hshift : Integrable fun t => |pairCorr G m n (t - s)| :=
    (integrable_abs_pairCorr hG hGsupp m n).comp_sub_right s
  have hle : ∀ t ∈ Set.Ioi (0 : ℝ), archLevyDensity t * |pairCorr G m n (t - s)| ≤
      archLevyDensity (s - w) * |pairCorr G m n (t - s)| := fun t ht => by
    by_cases hmem : |t - s| ≤ w
    · obtain ⟨h1, h2⟩ := abs_le.mp hmem
      exact mul_le_mul_of_nonneg_right (archLevyDensity_antitoneOn
        (show (0 : ℝ) < s - w by linarith) ht (by linarith)) (abs_nonneg _)
    · rw [pairCorr_eq_zero hGsupp m n (not_le.mp hmem), abs_zero, mul_zero, mul_zero]
  have hω : 0 ≤ archLevyDensity (s - w) := (archLevyDensity_pos (show (0 : ℝ) < s - w by linarith)).le
  calc ∫ t in Set.Ioi 0, archLevyDensity t * |pairCorr G m n (t - s)|
      ≤ ∫ t in Set.Ioi 0, archLevyDensity (s - w) * |pairCorr G m n (t - s)| :=
        setIntegral_mono_on hint (hshift.const_mul _).integrableOn measurableSet_Ioi hle
    _ ≤ ∫ t, archLevyDensity (s - w) * |pairCorr G m n (t - s)| :=
        setIntegral_le_integral (hshift.const_mul _)
          (Filter.Eventually.of_forall fun t => mul_nonneg hω (abs_nonneg _))
    _ = archLevyDensity (s - w) * ∫ τ, |pairCorr G m n τ| := by
        rw [integral_const_mul, integral_sub_right_eq_self (fun τ => |pairCorr G m n τ|) s]
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_pairCorr_le hG hGsupp m n) hω

/-- **One pair to the left**: at log-distance `s ≤ −2w` the correlation vanishes on `(0, ∞)`. -/
theorem integral_levy_abs_pairCorr_eq_zero (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hw0 : 0 < w) {s : ℝ} (hs : s ≤ -(2 * w)) (m n : ℕ) :
    ∫ t in Set.Ioi 0, archLevyDensity t * |pairCorr G m n (t - s)| = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
    have ht0 : (0 : ℝ) < t := ht
    have : w < |t - s| := by rw [abs_of_pos (by linarith)]; linarith
    rw [pairCorr_eq_zero hGsupp m n this, abs_zero, mul_zero]

end GaloisForLFunctions.ArithmeticLorentzianGeometry
