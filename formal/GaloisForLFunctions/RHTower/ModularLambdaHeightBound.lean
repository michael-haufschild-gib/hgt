import GaloisForLFunctions.RHTower.ModularLambdaWindingLog
import GaloisForLFunctions.Bottcher.ModularLambdaCovering

/-!
# `log |λ|` grows at most like `π` times the invariant height

For every `z` in the standard fundamental domain `𝒟` of `SL(2,ℤ)` and every `g ∈ SL(2,ℤ)`,

`|log |λ(gz)|| ≤ π Im z + C`   (`exists_abs_log_norm_modularLambda_smul_le`).

The value `λ(gz)` is one of the six anharmonic images of `w = λ(z)`:
`w, 1 − w, 1/w, 1/(1 − w), w/(w − 1), (w − 1)/w`. Each satisfies
`|log |φ(w)|| ≤ |log |w|| + |log |1 − w||` (`abs_log_norm_anharmElem_le`), so it suffices to bound
`|log |λ|| + |log |1 − λ||` on `𝒟`.

* High in the cusp, `λ(z)e^{−iπz} → 16` uniformly, so `8 e^{−π Im z} < |λ(z)| < 24 e^{−π Im z}`.
  This gives `|log |λ|| ≤ π Im z + log 24`, and `|λ| ≤ 1/2` gives `|log |1 − λ|| ≤ log 2`.
* The rest of `𝒟` lies in a compact subset of `{Im > 0}` on which `λ ≠ 0, 1`, so both logarithms are
  bounded there.
-/

open Filter Topology Set UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.ModularLambdaWinding

open GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

/-- Each anharmonic image `φ(w)` has `|log |φ(w)|| ≤ |log |w|| + |log |1 − w||`. -/
theorem abs_log_norm_anharmElem_le (g : SL(2, ℤ)) (w : Punctured) :
    |Real.log ‖(anharmElem g w : ℂ)‖| ≤ |Real.log ‖(w : ℂ)‖| + |Real.log ‖1 - (w : ℂ)‖| := by
  have h0 : (w : ℂ) ≠ 0 := punct_ne_zero w
  have h1 : 1 - (w : ℂ) ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 (punct_ne_one w)
  have hn0 : ‖(w : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hn1 : ‖1 - (w : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 h1
  have hw1 : ‖(w : ℂ) - 1‖ = ‖1 - (w : ℂ)‖ := norm_sub_rev _ _
  have hmem := anharmonicGroup_subset_sixSet (anharmElem_mem g)
  simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h | h <;> rw [h]
  · simp only [Equiv.Perm.coe_one, id_eq]
    linarith [abs_nonneg (Real.log ‖1 - (w : ℂ)‖)]
  · simp only [anharmS_apply]
    linarith [abs_nonneg (Real.log ‖(w : ℂ)‖)]
  · simp only [anharmT_apply]
    rw [norm_div, hw1, Real.log_div hn0 hn1]
    exact abs_sub _ _
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply]
    rw [show (1 : ℂ) - (w : ℂ) / ((w : ℂ) - 1) = -1 / ((w : ℂ) - 1) by
      field_simp [punct_ne_one w]; ring, norm_div, norm_neg, norm_one, hw1, Real.log_div one_ne_zero hn1,
      Real.log_one, zero_sub, abs_neg]
    linarith [abs_nonneg (Real.log ‖(w : ℂ)‖)]
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply]
    rw [show (1 - (w : ℂ)) / (1 - (w : ℂ) - 1) = -((1 - (w : ℂ)) / (w : ℂ)) by
      rw [show (1 : ℂ) - (w : ℂ) - 1 = -(w : ℂ) by ring, div_neg], norm_neg, norm_div,
      Real.log_div hn1 hn0]
    rw [abs_sub_comm]
    exact abs_sub _ _
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply]
    rw [show (1 : ℂ) - (1 - (w : ℂ)) / (1 - (w : ℂ) - 1) = 1 / (w : ℂ) by
      rw [show (1 : ℂ) - (w : ℂ) - 1 = -(w : ℂ) by ring, div_neg, sub_neg_eq_add]
      field_simp [h0]
      ring, norm_div, norm_one, Real.log_div one_ne_zero hn0, Real.log_one, zero_sub,
      abs_neg]
    linarith [abs_nonneg (Real.log ‖1 - (w : ℂ)‖)]

/-- High in the cusp: `8 < |λ(z)e^{−iπz}| < 24` and `|λ(z)| ≤ 1/2`. -/
theorem exists_cusp_bounds :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ z : ℂ, Y ≤ z.im →
      ‖modularLambda z * Complex.exp (-(Real.pi * Complex.I * z)) - 16‖ < 8 ∧
        ‖modularLambda z‖ ≤ 1 / 2 := by
  have h := tendsto_modularLambda_mul_exp_atImInfty.eventually (Metric.ball_mem_nhds (16 : ℂ)
    (by norm_num : (0 : ℝ) < 8))
  rw [Filter.eventually_comap, eventually_atTop] at h
  obtain ⟨Y₀, hY₀⟩ := h
  refine ⟨max Y₀ 2, by linarith [le_max_right Y₀ 2], fun z hz => ?_⟩
  have hball := hY₀ z.im (le_trans (le_max_left _ _) hz) z rfl
  rw [dist_eq_norm] at hball
  refine ⟨hball, ?_⟩
  have hexp : ‖Complex.exp (-(Real.pi * Complex.I * z))‖ = Real.exp (Real.pi * z.im) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hG : ‖modularLambda z * Complex.exp (-(Real.pi * Complex.I * z))‖ < 24 := by
    have := norm_le_norm_add_norm_sub' (modularLambda z * Complex.exp (-(Real.pi * Complex.I * z)))
      (16 : ℂ)
    rw [show ‖(16 : ℂ)‖ = 16 by norm_num] at this
    linarith
  rw [norm_mul, hexp] at hG
  have hz2 : 2 ≤ z.im := le_trans (le_max_right _ _) hz
  have he : (48 : ℝ) ≤ Real.exp (Real.pi * z.im) := by
    have he3 : (17 / 2 : ℝ) ≤ Real.exp 3 := by
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)
      norm_num at this ⊢; linarith
    have he6 : Real.exp 6 = Real.exp 3 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have hle : Real.exp 6 ≤ Real.exp (Real.pi * z.im) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_gt_three])
    nlinarith
  have hpos := Real.exp_pos (Real.pi * z.im)
  rw [← lt_div_iff₀ hpos] at hG
  calc ‖modularLambda z‖ ≤ 24 / Real.exp (Real.pi * z.im) := hG.le
    _ ≤ 24 / 48 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
    _ = 1 / 2 := by norm_num

/-- **On the fundamental domain**: `|log |λ|| + |log |1 − λ|| ≤ π Im z + C`. -/
theorem exists_log_norm_add_log_norm_one_sub_le :
    ∃ C : ℝ, ∀ z : ℍ, z ∈ ModularGroup.fd →
      |Real.log ‖modularLambda z‖| + |Real.log ‖1 - modularLambda z‖| ≤ Real.pi * z.im + C := by
  obtain ⟨Y, hY1, hY⟩ := exists_cusp_bounds
  -- the compact part
  let K : Set ℂ := {z | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ Y}
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const))
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / 2 + Y)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      obtain ⟨h1, h2, h3⟩ := hz
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 1 / 2 + Y := by rw [abs_of_pos (show 0 < z.im by linarith)]; linarith
  have hKH : ∀ z ∈ K, 0 < z.im := fun z hz => by linarith [hz.2.1]
  have hcont : ContinuousOn (fun z : ℂ =>
      |Real.log ‖modularLambda z‖| + |Real.log ‖1 - modularLambda z‖|) K := by
    have hl : ContinuousOn modularLambda K := fun z hz =>
      (differentiableAt_modularLambda_of_im_pos (hKH z hz)).continuousAt.continuousWithinAt
    refine ((hl.norm.log fun z hz => ?_).abs).add
      (((continuousOn_const.sub hl).norm.log fun z hz => ?_).abs)
    · exact norm_ne_zero_iff.2 (modularLambda_ne_zero_of_im_pos (hKH z hz))
    · exact norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm (modularLambda_ne_one (hKH z hz))))
  obtain ⟨C₀, hC₀⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max C₀ (Real.log 24 + Real.log 2), fun z hz => ?_⟩
  have hπy : 0 ≤ Real.pi * z.im := mul_nonneg Real.pi_pos.le z.im_pos.le
  rcases le_or_gt Y z.im with hzY | hzY
  · -- the cusp
    obtain ⟨hG, hsmall⟩ := hY (z : ℂ) hzY
    have hexp : ‖Complex.exp (-(Real.pi * Complex.I * (z : ℂ)))‖ = Real.exp (Real.pi * z.im) := by
      rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
    have hGlo : 8 < ‖modularLambda z‖ * Real.exp (Real.pi * z.im) := by
      have := norm_sub_norm_le (16 : ℂ) (modularLambda z * Complex.exp (-(Real.pi * Complex.I * z)))
      rw [show ‖(16 : ℂ)‖ = 16 by norm_num, norm_sub_rev, norm_mul, hexp] at this
      linarith
    have hGhi : ‖modularLambda z‖ * Real.exp (Real.pi * z.im) < 24 := by
      have := norm_le_norm_add_norm_sub' (modularLambda z * Complex.exp (-(Real.pi * Complex.I * z)))
        (16 : ℂ)
      rw [show ‖(16 : ℂ)‖ = 16 by norm_num, norm_mul, hexp] at this
      linarith
    have hlampos : 0 < ‖modularLambda z‖ :=
      norm_pos_iff.2 (modularLambda_ne_zero_of_im_pos z.im_pos)
    have hlog : |Real.log ‖modularLambda z‖ + Real.pi * z.im| ≤ Real.log 24 := by
      rw [← Real.log_exp (Real.pi * z.im), ← Real.log_mul hlampos.ne' (Real.exp_pos _).ne']
      rw [abs_le]
      constructor
      · have h8 : Real.log 8 ≤ Real.log (‖modularLambda z‖ * Real.exp (Real.pi * z.im)) :=
          Real.log_le_log (by norm_num) hGlo.le
        have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
        have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
        linarith
      · exact Real.log_le_log (by positivity) hGhi.le
    have h1 : |Real.log ‖modularLambda z‖| ≤ Real.pi * z.im + Real.log 24 := by
      have := abs_sub (Real.log ‖modularLambda z‖ + Real.pi * z.im) (Real.pi * z.im)
      rw [add_sub_cancel_right, abs_of_nonneg hπy] at this
      linarith
    have h2 : |Real.log ‖1 - modularLambda z‖| ≤ Real.log 2 := by
      have hlo : 1 / 2 ≤ ‖1 - modularLambda z‖ := by
        have := norm_sub_norm_le (1 : ℂ) (modularLambda z)
        rw [norm_one] at this; linarith
      have hhi : ‖1 - modularLambda z‖ ≤ 3 / 2 := by
        have := norm_sub_le (1 : ℂ) (modularLambda z)
        rw [norm_one] at this; linarith
      rw [abs_le]
      constructor
      · have := Real.log_le_log (by norm_num) hlo
        rw [one_div, Real.log_inv] at this
        linarith
      · calc Real.log ‖1 - modularLambda z‖ ≤ Real.log (3 / 2) := Real.log_le_log (by linarith) hhi
          _ ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
    have := le_max_right C₀ (Real.log 24 + Real.log 2)
    linarith
  · -- the compact part
    have hzK : (z : ℂ) ∈ K := by
      refine ⟨hz.2, ?_, hzY.le⟩
      have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      have h0 := z.im_pos
      show 1 / 2 ≤ z.im
      nlinarith
    have hb := hC₀ (z : ℂ) hzK
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hb
    have := le_max_left C₀ (Real.log 24 + Real.log 2)
    linarith

/-- **`log |λ|` on every translate of the fundamental domain**:
`|log |λ(gz)|| ≤ π Im z + C` for `z ∈ 𝒟` and `g ∈ SL(2,ℤ)`. -/
theorem exists_abs_log_norm_modularLambda_smul_le :
    ∃ C : ℝ, ∀ z : ℍ, z ∈ ModularGroup.fd → ∀ g : SL(2, ℤ),
      |Real.log ‖modularLambda ((g • z : ℍ) : ℂ)‖| ≤ Real.pi * z.im + C := by
  obtain ⟨C, hC⟩ := exists_log_norm_add_log_norm_one_sub_le
  refine ⟨C, fun z hz g => ?_⟩
  have h := congrArg Subtype.val (anharmElem_eq g z)
  have hv : modularLambda ((g • z : ℍ) : ℂ) = (anharmElem g (lambdaPunct z) : ℂ) := h
  rw [hv]
  exact (abs_log_norm_anharmElem_le g (lambdaPunct z)).trans (hC z hz)

end

end GaloisForLFunctions.RHTower.ModularLambdaWinding
