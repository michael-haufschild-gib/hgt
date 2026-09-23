import GaloisForLFunctions.RHTower.Sieve.LadderAnnulus

/-!
# One bilinear block over a cut window, for an arbitrary cofactor coefficient

The two-regime estimate of `Sieve/LadderAnnulus` is stated for the plain Möbius cofactor.  Nothing
in it uses more than `‖a n‖ ≤ 1`: on the annulus the prime polynomial carries the saving and the
cofactor contributes only its mean value bound, on the disc both are bounded in sup.  Collected here
in coefficient-general form, for one block at a time, so that the Ramaré cofactor
`μ(m)/(ω_P(m)+1)` — for which the corpus's ladder was originally built — can use it.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **One block over a frequency set, with the prime polynomial bounded there.** -/
theorem integral_normSq_blockProduct_set_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B D : Finset ℕ)
    (hD0 : (0 : ℕ) ∉ D) {MD : ℕ} (hDM : ∀ n ∈ D, n ≤ MD) {G V : ℝ} (hG : 1 ≤ G) (hV : 0 ≤ V)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEG : E ⊆ Set.Icc (-G) G)
    (hbound : ∀ w ∈ E, ‖primeBlockPoly B w‖ ≤ V) :
    (∫ w in E, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      ≤ V ^ (2 : ℕ) * ((5 * Real.pi / 2 * G + 5 * Real.exp 1 / 2 * (MD : ℝ)) * (D.card : ℝ)) := by
  classical
  have hnormsq : ∀ w : ℝ, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ)
      = ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ) := by
    intro w
    rw [norm_mul, mul_pow]
  have hcontR : Continuous fun w : ℝ => ‖primeBlockPoly B w‖ ^ (2 : ℕ) :=
    ((continuous_primeBlockPoly _).norm).pow 2
  have hcontS : Continuous fun w : ℝ => ‖logPoly a D w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly _ _).norm).pow 2
  have hrw : (∫ w in E, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      = ∫ w in E, ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    exact hnormsq w
  rw [hrw]
  have hint1 : IntegrableOn
      (fun w : ℝ => ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ)) E volume :=
    ((hcontR.mul hcontS).integrableOn_Icc (a := -G) (b := G)).mono_set hEG
  have hint2 : IntegrableOn (fun w : ℝ => V ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ)) E volume :=
    (((hcontS.const_mul _)).integrableOn_Icc (a := -G) (b := G)).mono_set hEG
  have hpt : ∀ w ∈ E,
      ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ)
        ≤ V ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ) := by
    intro w hw
    have hb := hbound w hw
    have h0 : (0 : ℝ) ≤ ‖primeBlockPoly B w‖ := norm_nonneg _
    have hsq : ‖primeBlockPoly B w‖ ^ (2 : ℕ) ≤ V ^ (2 : ℕ) := by nlinarith [hb, h0]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hmono := setIntegral_mono_on hint1 hint2 hEm hpt
  rw [MeasureTheory.integral_const_mul] at hmono
  refine hmono.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hwiden : (∫ w in E, ‖logPoly a D w‖ ^ (2 : ℕ))
      ≤ ∫ w in Set.Icc (-G) G, ‖logPoly a D w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_mono_set hcontS.integrableOn_Icc ?_
      (Filter.Eventually.of_forall hEG)
    exact Filter.Eventually.of_forall fun w => by positivity
  exact hwiden.trans (integral_Icc_normSq_logPoly_le_support a hD0 hDM ha hG)

/-- **One block on the low-frequency disc, with both factors bounded in sup.** -/
theorem integral_normSq_blockProduct_low_le (a : ℕ → ℂ) (B D : Finset ℕ) {w₀ V U : ℝ}
    (hw₀ : 0 ≤ w₀) (hV : 0 ≤ V) (hU : 0 ≤ U)
    (hprime : ∀ w ∈ Set.Icc (-w₀) w₀, ‖primeBlockPoly B w‖ ≤ V)
    (hcof : ∀ w ∈ Set.Icc (-w₀) w₀, ‖logPoly a D w‖ ≤ U) :
    (∫ w in Set.Icc (-w₀) w₀, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      ≤ V ^ (2 : ℕ) * U ^ (2 : ℕ) * (2 * w₀) := by
  classical
  have hcontR : Continuous fun w : ℝ => ‖primeBlockPoly B w‖ ^ (2 : ℕ) :=
    ((continuous_primeBlockPoly _).norm).pow 2
  have hcontS : Continuous fun w : ℝ => ‖logPoly a D w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly _ _).norm).pow 2
  have hrw : (∫ w in Set.Icc (-w₀) w₀, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      = ∫ w in Set.Icc (-w₀) w₀, ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [norm_mul, mul_pow]
  rw [hrw]
  have hint1 : IntegrableOn
      (fun w : ℝ => ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ))
      (Set.Icc (-w₀) w₀) volume := (hcontR.mul hcontS).integrableOn_Icc
  have hint2 : IntegrableOn (fun _ : ℝ => V ^ (2 : ℕ) * U ^ (2 : ℕ)) (Set.Icc (-w₀) w₀) volume :=
    continuous_const.integrableOn_Icc
  have hpt : ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ) ≤ V ^ (2 : ℕ) * U ^ (2 : ℕ) := by
    intro w hw
    have hb := hprime w hw
    have hc := hcof w hw
    have h0 : (0 : ℝ) ≤ ‖primeBlockPoly B w‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖logPoly a D w‖ := norm_nonneg _
    have hsq1 : ‖primeBlockPoly B w‖ ^ (2 : ℕ) ≤ V ^ (2 : ℕ) := by nlinarith [hb, h0]
    have hsq2 : ‖logPoly a D w‖ ^ (2 : ℕ) ≤ U ^ (2 : ℕ) := by nlinarith [hc, h1]
    have hs1 : (0 : ℝ) ≤ ‖logPoly a D w‖ ^ (2 : ℕ) := by positivity
    nlinarith [hsq1, hsq2, hs1, hV, hU]
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc hpt
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
  ring

/-- **One block over a cut window.**  On the annulus the prime polynomial carries the saving; on the
disc the cofactor polynomial does. -/
theorem integral_normSq_blockProduct_annulus_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (B D : Finset ℕ) (hD0 : (0 : ℕ) ∉ D) {MD : ℕ} (hDM : ∀ n ∈ D, n ≤ MD)
    {w₀ G V Vlow U : ℝ} (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    (hV : 0 ≤ V) (hVlow : 0 ≤ Vlow) (hU : 0 ≤ U)
    (hann : ∀ w ∈ Set.Icc (-G) G \ Set.Icc (-w₀) w₀, ‖primeBlockPoly B w‖ ≤ V)
    (hlowP : ∀ w ∈ Set.Icc (-w₀) w₀, ‖primeBlockPoly B w‖ ≤ Vlow)
    (hlowC : ∀ w ∈ Set.Icc (-w₀) w₀, ‖logPoly a D w‖ ≤ U) :
    (∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      ≤ V ^ (2 : ℕ) * ((5 * Real.pi / 2 * G + 5 * Real.exp 1 / 2 * (MD : ℝ)) * (D.card : ℝ))
        + Vlow ^ (2 : ℕ) * U ^ (2 : ℕ) * (2 * w₀) := by
  classical
  have hcont : Continuous fun w : ℝ => ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ) :=
    (((continuous_primeBlockPoly B).mul (continuous_logPoly a D)).norm).pow 2
  have hsplit := setIntegral_Icc_split (f := fun w : ℝ =>
    ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ)) hcont hwG
  have hsubAnn : Set.Icc (-G) G \ Set.Icc (-w₀) w₀ ⊆ Set.Icc (-G) G := Set.sdiff_subset
  have hAnn := integral_normSq_blockProduct_set_le a ha B D hD0 hDM hG hV
    (measurableSet_Icc.diff measurableSet_Icc) hsubAnn hann
  have hLow := integral_normSq_blockProduct_low_le a B D hw₀ hVlow hU hlowP hlowC
  rw [hsplit]
  linarith

end

end RHTower.Sieve
