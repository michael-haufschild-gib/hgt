import GaloisForLFunctions.RHTower.PaperThetaSeamDini
import GaloisForLFunctions.RHTower.PaperThetaLocalFourier

/-! # Full symmetric Fourier recovery at the divisor seam

The even Dirichlet kernel combines the two endpoint defects before the
Riemann–Lebesgue limit is taken.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

private theorem dirichlet_even (N : ℕ) (t : ℝ) :
    Period.dirichlet N (-t) = Period.dirichlet N t := by
  induction N with
  | zero => simp [Period.dirichlet, Period.phase]
  | succ N ih =>
    rw [Period.dirichlet_succ, Period.dirichlet_succ, ih]
    simp only [Period.ang, mul_neg, Real.cos_neg]

private theorem seamDini_kernel (z : ℂ) (N : ℕ) (t : Ioo (0 : ℝ) (1/2)) :
    (periodicMode z t.val+periodicMode z (-t.val)+2)*Period.dirichlet N t.val =
      seamDini z t.val * (Real.sin (Period.ang N t.val+Real.pi*t.val) : ℂ) := by
  have ht0 : 0 < t.val := t.2.1
  have hs : Real.sin (Real.pi*t.val) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht0)
      (by nlinarith [Real.pi_pos, t.2.2])).ne'
  have hsC : (Real.sin (Real.pi*t.val) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [seamDini, ← Period.dirichlet_sin N t.val,
    div_mul_eq_mul_div, ← mul_assoc, mul_div_cancel_right₀ _ hsC]

/-- Exact paired error identity for the original symmetric partial sums. -/
theorem seam_error_eq_paired_integral (z : {z : ℂ // XiC z = 0}) (N : ℕ) :
    symmetricPartialSum (circleMode z.val) N (Period.circle 0) + 1 =
      ∫ t in Ico (0 : ℝ) (1/2),
        seamDini z.val t * (Real.sin (Period.ang N t+Real.pi*t) : ℂ) := by
  let f := periodicMode z.val
  let F := fun t => (f (-t)+1)*Period.dirichlet N t
  obtain ⟨C, hb⟩ := exists_bound_circleMode ⟨z.val, Or.inr z.2⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb (Period.circle 0))
  have hfb (t : ℝ) : ‖f t‖ ≤ C := hb (Period.circle t)
  have hm : Measurable F :=
    (((measurable_periodicMode z.val).comp measurable_neg).add measurable_const).mul
      (Period.dirichlet_cont N).measurable
  have hB (t : ℝ) : ‖F t‖ ≤ (C+1)*(2*(N : ℝ)+1) := by
    dsimp [F]
    rw [norm_mul]
    apply mul_le_mul ?_ (Period.dirichlet_bound N t) (norm_nonneg _) (by positivity)
    exact (norm_add_le _ _).trans (by simpa using add_le_add_right (hfb (-t)) 1)
  have hF (a b : ℝ) : IntegrableOn F (Ico a b) :=
    Period.seg_integrable F hm _ a b (fun t _ => hB t)
  have hFn : IntegrableOn (fun t => F (-t)) (Ico (0 : ℝ) (1/2)) :=
    Period.seg_integrable _ (hm.comp measurable_neg) _ _ _ (fun t _ => hB (-t))
  have hbase : IntegrableOn (fun t => f (-t)*Period.dirichlet N t) Period.centerWin :=
    Period.seg_integrable _ (((measurable_periodicMode z.val).comp measurable_neg).mul
      (Period.dirichlet_cont N).measurable) (C*(2*(N : ℝ)+1)) _ _ (fun t _ => by
        change ‖f (-t)*Period.dirichlet N t‖ ≤ _
        rw [norm_mul]
        exact mul_le_mul (hfb (-t)) (Period.dirichlet_bound N t) (norm_nonneg _) hC)
  have hD : IntegrableOn (Period.dirichlet N) Period.centerWin :=
    Period.seg_integrable _ (Period.dirichlet_cont N).measurable (2*(N : ℝ)+1) _ _
      (fun t _ => Period.dirichlet_bound N t)
  have herr : symmetricPartialSum (circleMode z.val) N (Period.circle 0)+1 =
      ∫ t in Period.centerWin, F t := by
    rw [symmetricPartialSum_centered_L1 ⟨z.val, Or.inr (Or.inl z.2)⟩]
    simp only [zero_sub]
    dsimp only [F, f]
    simp_rw [add_mul, one_mul]
    rw [integral_add hbase hD, integral_centered_dirichlet]
  have hsplit : (∫ t in Period.centerWin, F t) =
      (∫ t in Ico (-1/2 : ℝ) 0, F t) + ∫ t in Ico (0 : ℝ) (1/2), F t := by
    rw [← setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico (hF _ _) (hF _ _),
      Ico_union_Ico_eq_Ico (by norm_num : (-1/2 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1/2)]
    rfl
  have href : (∫ t in Ico (-1/2 : ℝ) 0, F t) =
      ∫ t in Ico (0 : ℝ) (1/2), F (-t) := by
    simpa [neg_div] using (Period.seg_translate_scale_rev F 0 (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (0 : ℝ) < 1)).symm
  rw [herr, hsplit, href, ← integral_add hFn (hF _ _)]
  apply integral_congr_ae
  have hzero : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [ae_restrict_mem measurableSet_Ico, ae_restrict_of_ae hzero] with t ht ht0
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  calc
    F (-t)+F t = (periodicMode z.val t+periodicMode z.val (-t)+2)*Period.dirichlet N t := by
      dsimp [F, f]
      rw [neg_neg, dirichlet_even]
      ring
    _ = _ := seamDini_kernel z.val N ⟨t, htp, ht.2⟩

private theorem integrable_phase_product {f : ℝ → ℂ} (hf : Integrable f) (u : ℝ) :
    Integrable (fun t => f t * Period.phase u t) := by
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul (Period.phase_cont u).aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖f t * Period.phase u t‖ ≤ _
    rw [norm_mul, Period.phase_unimod, mul_one]

theorem tendsto_seam_oscillation (z : {z : ℂ // XiC z = 0}) :
    Tendsto (fun N : ℕ => ∫ t in Ico (0 : ℝ) (1/2),
      seamDini z.val t * (Real.sin (Period.ang N t+Real.pi*t) : ℂ)) atTop (𝓝 0) := by
  let f := (Ico (0 : ℝ) (1/2)).indicator (seamDini z.val)
  have hf : Integrable f := (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_seamDini z)
  have he (N : ℕ) : (∫ t in Ico (0 : ℝ) (1/2),
      seamDini z.val t * (Real.sin (Period.ang N t+Real.pi*t) : ℂ)) =
      ((∫ t, f t*Period.phase ((N : ℝ)+1/2) t) -
        ∫ t, f t*Period.phase (-((N : ℝ)+1/2)) t)/(2*Complex.I) := by
    rw [← integral_sub (integrable_phase_product hf _) (integrable_phase_product hf _),
      ← integral_div, ← integral_indicator measurableSet_Ico]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Ico (0 : ℝ) (1/2)
    · simp only [f, indicator_of_mem ht, Period.dirichlet_sine_eq_phase_pair]
      ring
    · simp only [f, indicator_of_notMem ht, zero_mul, sub_self, zero_div]
  simp_rw [he]
  simpa only [sub_self, zero_div] using
    ((Period.tendsto_integral_phase_half_pos f).sub
      (Period.tendsto_integral_phase_half_neg f)).div_const (2*Complex.I)

/-- The literal divisor Fourier series recovers the common trace at the missing seam. -/
theorem circle_seam_recovery (z : {z : ℂ // XiC z = 0}) :
    Tendsto (fun N : ℕ => symmetricPartialSum (circleMode z.val) N (Period.circle 0))
      atTop (𝓝 (-1)) := by
  have h : Tendsto (fun N : ℕ => symmetricPartialSum (circleMode z.val) N (Period.circle 0)+1)
      atTop (𝓝 0) := by
    simp_rw [seam_error_eq_paired_integral]
    exact tendsto_seam_oscillation z
  simpa using h.sub_const 1

end RHTower.PaperThetaEndpoint
