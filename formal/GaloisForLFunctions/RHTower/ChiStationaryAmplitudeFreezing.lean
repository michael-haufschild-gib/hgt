import GaloisForLFunctions.RHTower.ChiGradedExteriorAmplitude
import Mathlib.Analysis.Calculus.MeanValue

open Complex MeasureTheory
noncomputable section
namespace RHTower

/-- Freezing a complex amplitude at the actual saddle pays a central
Lipschitz cost and both complete exterior variation costs. -/
theorem norm_integral_entropy_grade_amplitude_sub_saddle_le
    {a k h l u L : ℝ} (ha : 0 < a) (hk : 0 < k) (hh : 0 < h)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a)
    (hL : 0 ≤ L) {v v' : ℝ → ℂ}
    (hv : ∀ t ∈ Set.Icc l u, HasDerivAt v (v' t) t)
    (hvi : IntervalIntegrable v' volume l u)
    (hvL : ∀ t ∈ Set.Icc l u, ‖v' t‖ ≤ L) :
    ‖∫ t in l..u, (v t - v a) *
      bourgainOscillation (-k * chiStationaryEntropy a t)‖ ≤
      2 * L * h ^ 2 + 40 * L * a ^ 2 / (k * h) := by
  have hlu : l ≤ u := by linarith
  have haI : a ∈ Set.Icc l u := ⟨by linarith, by linarith⟩
  have hLip (t : ℝ) (ht : t ∈ Set.Icc l u) : ‖v t - v a‖ ≤ L * |t - a| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x hx => (hv x hx).hasDerivWithinAt) hvL (convex_Icc l u) haI ht
  let g : ℝ → ℂ := fun t => bourgainOscillation (-k * chiStationaryEntropy a t)
  let f : ℝ → ℂ := fun t => (v t - v a) * g t
  have hg : Continuous g := continuous_chiStationaryEntropy_grade a k
  have hvC : ContinuousOn v (Set.Icc l u) :=
    fun t ht => (hv t ht).continuousAt.continuousWithinAt
  have hfC : ContinuousOn f (Set.Icc l u) := (hvC.sub continuousOn_const).mul hg.continuousOn
  have hsub {b c : ℝ} (hb : l ≤ b) (hc : c ≤ u) : Set.Icc b c ⊆ Set.Icc l u :=
    fun _ hx => ⟨hb.trans hx.1, hx.2.trans hc⟩
  have hfInt {b c : ℝ} (hbc : b ≤ c) (hb : l ≤ b) (hc : c ≤ u) :
      IntervalIntegrable f volume b c :=
    ContinuousOn.intervalIntegrable_of_Icc hbc (hfC.mono (hsub hb hc))
  have hvInt {b c : ℝ} (hbc : b ≤ c) (hb : l ≤ b) (hc : c ≤ u) :
      IntervalIntegrable v' volume b c := by
    apply hvi.mono_set
    rw [Set.uIcc_of_le hbc, Set.uIcc_of_le hlu]
    exact hsub hb hc
  have hvar {b c : ℝ} (hbc : b ≤ c) (hb : l ≤ b) (hc : c ≤ u) :
      (∫ t in b..c, ‖v' t‖) ≤ L * (c - b) := by
    have hi := intervalIntegral.integral_mono_on hbc (hvInt hbc hb hc).norm
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => L) volume b c)
      (fun t ht => hvL t (hsub hb hc ht))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hi
  have hvSub {b c : ℝ} (hbc : b ≤ c) (hb : l ≤ b) (hc : c ≤ u) :
      ∀ t ∈ Set.uIcc b c, HasDerivAt (fun x => v x - v a) (v' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hbc] at ht
    exact (hv t (hsub hb hc ht)).sub_const (v a)
  have hleft : ‖∫ t in l..(a - h), f t‖ ≤ (16 * a / (k * h)) * (L * a / 2) := by
    have hb := norm_integral_complexAmplitude_mul_entropy_grade_exterior_le
      ha hk hh hl hlh (show a - h ≤ 2 * a by linarith) (Or.inl le_rfl)
      (hvSub hlh le_rfl (by linarith)) (hvInt hlh le_rfl (by linarith))
    have hp := hLip (a - h) ⟨hlh, by linarith⟩
    have he : |(a - h) - a| = h := by
      rw [show (a - h) - a = -h by ring, abs_neg, abs_of_pos hh]
    rw [he] at hp
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hvb := hvar hlh le_rfl (show a - h ≤ u by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hl hL]
  have hright : ‖∫ t in (a + h)..u, f t‖ ≤ (16 * a / (k * h)) * (2 * L * a) := by
    have hb := norm_integral_complexAmplitude_mul_entropy_grade_exterior_le
      ha hk hh (show a / 2 ≤ a + h by linarith) hhu hu (Or.inr le_rfl)
      (hvSub hhu (by linarith) le_rfl) (hvInt hhu (by linarith) le_rfl)
    have hp := hLip u ⟨hlu, le_rfl⟩
    rw [abs_of_nonneg (show 0 ≤ u - a by linarith)] at hp
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hvb := hvar hhu (show l ≤ a + h by linarith) le_rfl
    nlinarith [mul_le_mul_of_nonneg_left hu hL, mul_nonneg hL hh.le]
  have hcenter : ‖∫ t in (a - h)..(a + h), f t‖ ≤ 2 * L * h ^ 2 := by
    have hb : ‖∫ t in (a - h)..(a + h), f t‖ ≤ (L * h) * |(a + h) - (a - h)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le (by linarith : a - h ≤ a + h)] at ht
      dsimp only [f, g]
      rw [norm_mul, norm_bourgainOscillation, mul_one]
      apply (hLip t ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) hL
    apply hb.trans_eq
    rw [abs_of_nonneg (by linarith : 0 ≤ (a + h) - (a - h))]
    ring
  have hsplit : (∫ t in l..u, f t) = (∫ t in l..(a - h), f t) +
      (∫ t in (a - h)..(a + h), f t) + (∫ t in (a + h)..u, f t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hfInt (by linarith : l ≤ a + h) le_rfl hhu) (hfInt hhu (by linarith) le_rfl),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hfInt hlh le_rfl (by linarith)) (hfInt (by linarith) hlh hhu)]
  change ‖∫ t in l..u, f t‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖∫ t in l..(a - h), f t‖ + ‖∫ t in (a - h)..(a + h), f t‖ +
        ‖∫ t in (a + h)..u, f t‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (16 * a / (k * h)) * (L * a / 2) + 2 * L * h ^ 2 +
        (16 * a / (k * h)) * (2 * L * a) := add_le_add (add_le_add hleft hcenter) hright
    _ = _ := by ring

/-- Full model stationary value with the literal complex amplitude at the
saddle and an explicit cost for its height variation. -/
theorem norm_integral_entropy_grade_complexAmplitude_sub_stationary_le
    {a k h l u L : ℝ} (ha : 0 < a) (hk : 0 < k) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a)
    (hL : 0 ≤ L) {v v' : ℝ → ℂ}
    (hv : ∀ t ∈ Set.Icc l u, HasDerivAt v (v' t) t)
    (hvi : IntervalIntegrable v' volume l u)
    (hvL : ∀ t ∈ Set.Icc l u, ‖v' t‖ ≤ L) :
    ‖(∫ t in l..u, v t * bourgainOscillation (-k * chiStationaryEntropy a t)) -
      v a * ((k⁻¹ : ℂ) * ((Real.sqrt (2 * Real.pi * (k * a)) : ℂ) *
        bourgainOscillation (-(Real.pi / 4))))‖ ≤
      2 * L * h ^ 2 + 40 * L * a ^ 2 / (k * h) +
      ‖v a‖ * (4 * k * h ^ 4 / a ^ 2 + 40 * a / (k * h)) := by
  have hlu : l ≤ u := by linarith
  let g : ℝ → ℂ := fun t => bourgainOscillation (-k * chiStationaryEntropy a t)
  let M : ℂ := (k⁻¹ : ℂ) * ((Real.sqrt (2 * Real.pi * (k * a)) : ℂ) *
    bourgainOscillation (-(Real.pi / 4)))
  have hg : Continuous g := continuous_chiStationaryEntropy_grade a k
  have hvC : ContinuousOn v (Set.Icc l u) :=
    fun t ht => (hv t ht).continuousAt.continuousWithinAt
  have hprod : IntervalIntegrable (fun t => v t * g t) volume l u :=
    ContinuousOn.intervalIntegrable_of_Icc hlu (hvC.mul hg.continuousOn)
  have heq : (∫ t in l..u, v t * g t) - v a * (∫ t in l..u, g t) =
      ∫ t in l..u, (v t - v a) * g t := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hprod ((hg.intervalIntegrable l u).const_mul (v a))]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hfreeze := norm_integral_entropy_grade_amplitude_sub_saddle_le
    ha hk hh hl hlh hhu hu hL hv hvi hvL
  have hmodel := norm_integral_chiStationaryEntropy_grade_sub_le ha hk hh hha hl hlh hhu hu
  change ‖(∫ t in l..u, v t * g t) - v a * M‖ ≤ _
  calc
    _ = ‖((∫ t in l..u, v t * g t) - v a * (∫ t in l..u, g t)) +
        v a * ((∫ t in l..u, g t) - M)‖ := by congr 1; ring
    _ ≤ ‖(∫ t in l..u, v t * g t) - v a * (∫ t in l..u, g t)‖ +
        ‖v a * ((∫ t in l..u, g t) - M)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [heq, norm_mul]
      exact add_le_add hfreeze (mul_le_mul_of_nonneg_left hmodel (norm_nonneg _))

end RHTower
