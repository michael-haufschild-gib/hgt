import GaloisForLFunctions.RHTower.EisensteinMaassSelbergCuspIntegrals

/-!
# The Maass–Selberg relation in the absolutely convergent region

For `Re u > Re v > ½`, `Im v > 0` and `Y ≥ 1`,

`(u−v)(u+v) ∫_𝒟 Λ^Y E_u · Λ^Y E_v dμ = R(u, v, Y)`,

with `R` the cleared right-hand side `msRight`.  The proof is the classical unfolding argument:
the truncated pairing equals `∫_𝒟 Λ^Y E_u · E_v` (the subtracted constant term has zero mean
against the truncated series above height `Y`), the truncation identity turns `Λ^Y E_u` into the
truncated row sum minus `B(u)[y>Y] y^{½−u}`, the row sum unfolds to the strip slab, and both
remaining integrals are the one-dimensional cusp and slab integrals.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Measurability and bounds of the truncated line model -/

theorem msA_ne_zero_of_re {u : ℂ} (hu : 1 / 2 < u.re) : msA u ≠ 0 := by
  unfold msA reflectedCompletedLambda
  apply mul_ne_zero
  · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  · exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)

theorem measurable_cuspConstantPart_im (u : ℂ) :
    Measurable (fun z : ℍ => d4BMCompletedEisensteinCuspConstantPart .scalar u z.im) := by
  simp_rw [cuspConstantPart_eq_msAB]
  have hm : Measurable (fun z : ℍ => ((z.im : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).measurable
  exact (measurable_const.mul (hm.pow_const _)).add (measurable_const.mul (hm.pow_const _))

theorem measurable_truncatedLineModel (u : ℂ) (Y : ℝ) : Measurable (truncatedLineModel u Y) := by
  unfold truncatedLineModel
  refine (continuous_eisensteinLineModel u).measurable.sub ?_
  exact Measurable.ite (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)
    (measurable_cuspConstantPart_im u) measurable_const

theorem measurable_aboveHeight_cpow (u : ℂ) (Y : ℝ) :
    Measurable (fun z : ℍ => if Y < z.im then ((z.im : ℝ) : ℂ) ^ (1 / 2 - u) else 0) := by
  have hm : Measurable (fun z : ℍ => ((z.im : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).measurable
  exact Measurable.ite (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)
    (hm.pow_const _) measurable_const

/-- The bound of the truncated line model on `𝒟`. -/
def truncBound (u : ℂ) (Y : ℝ) : ℝ :=
  ‖msB u‖ * (1 / 2 : ℝ) ^ (1 / 2 - u.re) + ‖msA u‖ * Y ^ (1 / 2 + u.re) + tailConst u

theorem truncBound_nonneg (u : ℂ) {Y : ℝ} (hY : 0 ≤ Y) : 0 ≤ truncBound u Y := by
  unfold truncBound
  have h1 := tailConst_nonneg u
  have h2 : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 - u.re) := Real.rpow_nonneg (by norm_num) _
  have h3 : 0 ≤ Y ^ (1 / 2 + u.re) := Real.rpow_nonneg hY _
  have h4 := norm_nonneg (msB u)
  have h5 := norm_nonneg (msA u)
  nlinarith [mul_nonneg h4 h2, mul_nonneg h5 h3]

theorem norm_truncatedLineModel_le_of_gt' {u : ℂ} {Y : ℝ} {z : ℍ} (hz : z ∈ fd) (hzY : Y < z.im) :
    ‖truncatedLineModel u Y z‖ ≤ tailConst u * Real.exp (-(2 * Real.pi * z.im)) := by
  unfold truncatedLineModel
  rw [if_pos hzY]
  unfold eisensteinLineModel d4BMCompletedEisensteinCuspLeg
  rw [add_sub_cancel_left]
  exact norm_cuspTailPart_le_exp u z.re (half_lt_im_of_mem_fd' hz).le

theorem norm_truncatedLineModel_le_truncBound {u : ℂ} (hu : 1 / 2 ≤ u.re) {Y : ℝ} (hY : 1 ≤ Y)
    {z : ℍ} (hz : z ∈ fd) : ‖truncatedLineModel u Y z‖ ≤ truncBound u Y := by
  have hy := half_lt_im_of_mem_fd' hz
  rcases le_or_gt z.im Y with hzY | hzY
  · unfold truncatedLineModel
    rw [if_neg (not_lt.mpr hzY), sub_zero]
    refine (norm_eisensteinLineModel_le u hy.le).trans ?_
    unfold truncBound
    have h1 : z.im ^ (1 / 2 - u.re) ≤ (1 / 2 : ℝ) ^ (1 / 2 - u.re) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hy.le (by linarith)
    have h2 : z.im ^ (1 / 2 + u.re) ≤ Y ^ (1 / 2 + u.re) :=
      Real.rpow_le_rpow z.im_pos.le hzY (by linarith)
    have h3 : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos])
    have hT := tailConst_nonneg u
    have hB := norm_nonneg (msB u)
    have hA := norm_nonneg (msA u)
    nlinarith [mul_le_mul_of_nonneg_left h1 hB, mul_le_mul_of_nonneg_left h2 hA,
      mul_le_mul_of_nonneg_left h3 hT]
  · refine (norm_truncatedLineModel_le_of_gt' hz hzY).trans ?_
    unfold truncBound
    have h3 : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos])
    have hT := tailConst_nonneg u
    have h2 : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 - u.re) := Real.rpow_nonneg (by norm_num) _
    have h4 : 0 ≤ Y ^ (1 / 2 + u.re) := Real.rpow_nonneg (by linarith) _
    have hB := norm_nonneg (msB u)
    have hA := norm_nonneg (msA u)
    nlinarith [mul_le_mul_of_nonneg_left h3 hT, mul_nonneg hB h2, mul_nonneg hA h4]

/-- Above height `Y`, the truncated model times the line model is bounded (the tail absorbs the
growth of `E_v`). -/
theorem norm_truncatedLineModel_mul_lineModel_le {u v : ℂ} (hu : 1 / 2 ≤ u.re) (hv : 1 / 2 ≤ v.re)
    {Y : ℝ} (hY : 1 ≤ Y) {z : ℍ} (hz : z ∈ fd) :
    ‖truncatedLineModel u Y z * eisensteinLineModel v z‖ ≤
      truncBound u Y * (lineBoundConst v * (1 + Y ^ (1 / 2 + v.re))) +
        tailConst u * ((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
          (2 * lineBoundConst v) := by
  have hy := half_lt_im_of_mem_fd' hz
  rw [norm_mul]
  have hE := norm_eisensteinLineModel_le' hv hy.le
  have hL := lineBoundConst_nonneg v
  have hT := tailConst_nonneg u
  have hC : 0 ≤ (⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊ := by positivity
  rcases le_or_gt z.im Y with hzY | hzY
  · have h1 := norm_truncatedLineModel_le_truncBound hu hY hz
    have hyY : z.im ^ (1 / 2 + v.re) ≤ Y ^ (1 / 2 + v.re) :=
      Real.rpow_le_rpow z.im_pos.le hzY (by linarith)
    have h2 : ‖eisensteinLineModel v z‖ ≤ lineBoundConst v * (1 + Y ^ (1 / 2 + v.re)) :=
      hE.trans (mul_le_mul_of_nonneg_left (by linarith) hL)
    have := mul_le_mul h1 h2 (norm_nonneg _) (truncBound_nonneg u (by linarith))
    nlinarith [mul_nonneg (mul_nonneg hT hC) (by positivity : (0 : ℝ) ≤ 2 * lineBoundConst v)]
  · have hy1 : 1 ≤ z.im := by linarith
    have h1 := norm_truncatedLineModel_le_of_gt' (u := u) hz hzY
    have hexp := exp_neg_le_rpow_of_one_le (a := v.re + 1) hy1
    have hone : (1 : ℝ) ≤ z.im ^ (1 / 2 + v.re) := Real.one_le_rpow hy1 (by linarith)
    have h2 : ‖eisensteinLineModel v z‖ ≤ 2 * lineBoundConst v * z.im ^ (1 / 2 + v.re) := by
      refine hE.trans ?_
      have : (1 : ℝ) + z.im ^ (1 / 2 + v.re) ≤ 2 * z.im ^ (1 / 2 + v.re) := by linarith
      calc lineBoundConst v * (1 + z.im ^ (1 / 2 + v.re))
          ≤ lineBoundConst v * (2 * z.im ^ (1 / 2 + v.re)) := mul_le_mul_of_nonneg_left this hL
        _ = _ := by ring
    have hpow : z.im ^ (1 / 2 - (v.re + 1)) * z.im ^ (1 / 2 + v.re) = 1 := by
      rw [← Real.rpow_add z.im_pos]
      have h0 : (1 / 2 - (v.re + 1) + (1 / 2 + v.re) : ℝ) = 0 := by ring
      rw [h0, Real.rpow_zero]
    have h3 : ‖truncatedLineModel u Y z‖ ≤
        tailConst u * (((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
          z.im ^ (1 / 2 - (v.re + 1))) :=
      h1.trans (mul_le_mul_of_nonneg_left hexp hT)
    have hprod := mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
    have hb : 0 ≤ truncBound u Y * (lineBoundConst v * (1 + Y ^ (1 / 2 + v.re))) := by
      have := truncBound_nonneg u (by linarith : (0 : ℝ) ≤ Y)
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) (1 / 2 + v.re)
      positivity
    calc ‖truncatedLineModel u Y z‖ * ‖eisensteinLineModel v z‖
        ≤ tailConst u * (((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
            z.im ^ (1 / 2 - (v.re + 1))) * (2 * lineBoundConst v * z.im ^ (1 / 2 + v.re)) := hprod
      _ = tailConst u * ((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
            (2 * lineBoundConst v) * (z.im ^ (1 / 2 - (v.re + 1)) * z.im ^ (1 / 2 + v.re)) := by
          ring
      _ = tailConst u * ((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
            (2 * lineBoundConst v) := by rw [hpow, mul_one]
      _ ≤ _ := by linarith

/-! ## Integrability on `𝒟` -/

theorem integrableOn_trunc_mul_trunc {u v : ℂ} (hu : 1 / 2 ≤ u.re) (hv : 1 / 2 ≤ v.re) {Y : ℝ}
    (hY : 1 ≤ Y) :
    IntegrableOn (fun z : ℍ => truncatedLineModel u Y z * truncatedLineModel v Y z) fd volume := by
  refine Integrable.mono' (integrableOn_const (C := truncBound u Y * truncBound v Y)
    (by simp [volume_fd_ne_top]))
    ((measurable_truncatedLineModel u Y).mul (measurable_truncatedLineModel v Y)).aestronglyMeasurable
    ?_
  refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall fun z hz => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_truncatedLineModel_le_truncBound hu hY hz)
    (norm_truncatedLineModel_le_truncBound hv hY hz) (norm_nonneg _)
    (truncBound_nonneg u (by linarith))

theorem integrableOn_trunc_mul_line {u v : ℂ} (hu : 1 / 2 ≤ u.re) (hv : 1 / 2 ≤ v.re) {Y : ℝ}
    (hY : 1 ≤ Y) :
    IntegrableOn (fun z : ℍ => truncatedLineModel u Y z * eisensteinLineModel v z) fd volume := by
  refine Integrable.mono' (integrableOn_const
    (C := truncBound u Y * (lineBoundConst v * (1 + Y ^ (1 / 2 + v.re))) +
      tailConst u * ((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
        (2 * lineBoundConst v)) (by simp [volume_fd_ne_top]))
    ((measurable_truncatedLineModel u Y).mul (continuous_eisensteinLineModel v).measurable).aestronglyMeasurable
    ?_
  exact (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall fun z hz =>
    norm_truncatedLineModel_mul_lineModel_le hu hv hY hz)

theorem integrableOn_aboveHeight_cpow_mul_line {u v : ℂ} (hv : 1 / 2 ≤ v.re) (huv : v.re < u.re)
    {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z : ℍ =>
      (if Y < z.im then ((z.im : ℝ) : ℂ) ^ (1 / 2 - u) else 0) * eisensteinLineModel v z) fd volume := by
  refine integrableOn_fd_of_norm_le
    ((measurable_aboveHeight_cpow u Y).mul (continuous_eisensteinLineModel v).measurable).aestronglyMeasurable
    (β := 1 - u.re + v.re) (by linarith) (C := 2 * lineBoundConst v) fun z hz => ?_
  have hy := half_lt_im_of_mem_fd' hz
  have hL := lineBoundConst_nonneg v
  have hpow : 0 ≤ z.im ^ (1 - u.re + v.re) := Real.rpow_nonneg z.im_pos.le _
  rw [norm_mul]
  split_ifs with hzY
  · have hy1 : 1 ≤ z.im := by linarith
    rw [Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos, re_half_sub]
    have hE := norm_eisensteinLineModel_le' hv hy.le
    have hone : (1 : ℝ) ≤ z.im ^ (1 / 2 + v.re) := Real.one_le_rpow hy1 (by linarith)
    have h2 : ‖eisensteinLineModel v z‖ ≤ 2 * lineBoundConst v * z.im ^ (1 / 2 + v.re) := by
      refine hE.trans ?_
      have : (1 : ℝ) + z.im ^ (1 / 2 + v.re) ≤ 2 * z.im ^ (1 / 2 + v.re) := by linarith
      calc lineBoundConst v * (1 + z.im ^ (1 / 2 + v.re))
          ≤ lineBoundConst v * (2 * z.im ^ (1 / 2 + v.re)) := mul_le_mul_of_nonneg_left this hL
        _ = _ := by ring
    have hpos : 0 ≤ z.im ^ (1 / 2 - u.re) := Real.rpow_nonneg z.im_pos.le _
    calc z.im ^ (1 / 2 - u.re) * ‖eisensteinLineModel v z‖
        ≤ z.im ^ (1 / 2 - u.re) * (2 * lineBoundConst v * z.im ^ (1 / 2 + v.re)) :=
          mul_le_mul_of_nonneg_left h2 hpos
      _ = 2 * lineBoundConst v * (z.im ^ (1 / 2 - u.re) * z.im ^ (1 / 2 + v.re)) := by ring
      _ = 2 * lineBoundConst v * z.im ^ (1 - u.re + v.re) := by
          rw [← Real.rpow_add z.im_pos]; ring_nf
  · simp only [norm_zero, zero_mul]
    positivity

/-- On `𝒟` the truncated row sum against `E_v` is a combination of the two integrable products. -/
theorem truncatedRowSum_mul_eq_on_fd {u : ℂ} (hu : 1 / 2 < u.re) (v : ℂ) {Y : ℝ} (hY : 1 ≤ Y)
    {z : ℍ} (hz : z ∈ fd) :
    truncatedRowSum (1 / 2 + u) Y z * eisensteinLineModel v z =
      (2 / msA u) * (truncatedLineModel u Y z * eisensteinLineModel v z +
        msB u * ((if Y < z.im then ((z.im : ℝ) : ℂ) ^ (1 / 2 - u) else 0) *
          eisensteinLineModel v z)) := by
  have h := truncatedLineModel_eq_truncatedRowSum hu hz hY
  have hA := msA_ne_zero_of_re hu
  rw [h]
  field_simp
  ring

theorem integrableOn_truncatedRowSum_mul_line {u v : ℂ} (hu : 1 / 2 < u.re) (hv : 1 / 2 ≤ v.re)
    (huv : v.re < u.re) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z : ℍ => truncatedRowSum (1 / 2 + u) Y z * eisensteinLineModel v z)
      fd volume := by
  have h1 := integrableOn_trunc_mul_line hu.le hv hY
  have h2 := (integrableOn_aboveHeight_cpow_mul_line hv huv hY).const_mul (msB u)
  have h3 := (h1.add h2).const_mul (2 / msA u)
  refine IntegrableOn.congr_fun h3 (fun z hz => ?_) isClosed_fd.measurableSet
  simp only [Pi.add_apply]
  exact (truncatedRowSum_mul_eq_on_fd hu v hY hz).symm

/-! ## The subtracted constant term has zero mean against the truncated series -/

/-- The integrand `tail_u(x, y) c_v(y)` in coordinates. -/
def tailTimesConst (u v : ℂ) (p : ℝ × ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspTailPart .scalar u p.1 p.2 *
    d4BMCompletedEisensteinCuspConstantPart .scalar v p.2

theorem continuousOn_tailTimesConst_div (u v : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => tailTimesConst u v p / ((p.2 : ℝ) : ℂ) ^ 2)
      {p : ℝ × ℝ | 0 < p.2} := by
  unfold tailTimesConst
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) {p : ℝ × ℝ | 0 < p.2} :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn
  refine ((continuousOn_cuspTailPart_pair u).mul (continuousOn_cuspConstantPart_pair v)).div
    (hc.pow 2) ?_
  intro p hp
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hp))

theorem norm_tailTimesConst_div_le (u : ℂ) {v : ℂ} (hv : 0 ≤ v.re) {p : ℝ × ℝ} (hp : 1 ≤ p.2) :
    ‖tailTimesConst u v p / ((p.2 : ℝ) : ℂ) ^ 2‖ ≤
      tailConst u * ((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
        (‖msB v‖ + ‖msA v‖) * p.2 ^ (-2 : ℝ) := by
  have hy0 : 0 < p.2 := by linarith
  unfold tailTimesConst
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
  have h1 := norm_cuspTailPart_le_exp u p.1 (by linarith : 1 / 2 ≤ p.2)
  have hexp := exp_neg_le_rpow_of_one_le (a := v.re + 1) hp
  have hT := tailConst_nonneg u
  have hC : 0 ≤ (⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊ := by positivity
  have h2 := norm_cuspConstantPart_le hy0 v
  have hle : p.2 ^ (1 / 2 - v.re) ≤ p.2 ^ (1 / 2 + v.re) :=
    Real.rpow_le_rpow_of_exponent_le hp (by linarith)
  have h3 : ‖d4BMCompletedEisensteinCuspConstantPart .scalar v p.2‖ ≤
      (‖msB v‖ + ‖msA v‖) * p.2 ^ (1 / 2 + v.re) := by
    refine h2.trans ?_
    have hB := norm_nonneg (msB v)
    nlinarith [mul_le_mul_of_nonneg_left hle hB]
  have h4 : ‖d4BMCompletedEisensteinCuspTailPart .scalar u p.1 p.2‖ ≤
      tailConst u * (((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
        p.2 ^ (1 / 2 - (v.re + 1))) :=
    h1.trans (mul_le_mul_of_nonneg_left hexp hT)
  have hprod := mul_le_mul h4 h3 (norm_nonneg _) (by positivity)
  have hsq : 0 < p.2 ^ 2 := by positivity
  have hpow : p.2 ^ (1 / 2 - (v.re + 1)) * p.2 ^ (1 / 2 + v.re) = 1 := by
    rw [← Real.rpow_add hy0]
    have h0 : (1 / 2 - (v.re + 1) + (1 / 2 + v.re) : ℝ) = 0 := by ring
    rw [h0, Real.rpow_zero]
  have hBA : 0 ≤ ‖msB v‖ + ‖msA v‖ := by positivity
  calc ‖d4BMCompletedEisensteinCuspTailPart .scalar u p.1 p.2‖ *
        ‖d4BMCompletedEisensteinCuspConstantPart .scalar v p.2‖ / p.2 ^ 2
      ≤ tailConst u * (((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
          p.2 ^ (1 / 2 - (v.re + 1))) * ((‖msB v‖ + ‖msA v‖) * p.2 ^ (1 / 2 + v.re)) / p.2 ^ 2 := by
        gcongr
    _ = tailConst u * ((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
          (‖msB v‖ + ‖msA v‖) * (p.2 ^ (1 / 2 - (v.re + 1)) * p.2 ^ (1 / 2 + v.re)) / p.2 ^ 2 := by
        ring
    _ = tailConst u * ((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
          (‖msB v‖ + ‖msA v‖) * p.2 ^ (-2 : ℝ) := by
        rw [hpow, mul_one, Real.rpow_neg hy0.le, Real.rpow_two, div_eq_mul_inv]

theorem integrableOn_tailTimesConst_div (u : ℂ) {v : ℂ} (hv : 0 ≤ v.re) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun p : ℝ × ℝ => tailTimesConst u v p / ((p.2 : ℝ) : ℂ) ^ 2) (cuspRect Y) := by
  refine Integrable.mono' (integrableOn_rpow_cuspRect (β := -2) (by norm_num)
    (by linarith : 0 < Y) (tailConst u * ((⌈v.re + 1⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈v.re + 1⌉₊) *
        (‖msB v‖ + ‖msA v‖))) ?_ ?_
  · exact ((continuousOn_tailTimesConst_div u v).mono fun p hp => cuspRect_pos (by linarith) hp)
      |>.aestronglyMeasurable (measurableSet_cuspRect Y)
  · refine (ae_restrict_iff' (measurableSet_cuspRect Y)).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    have hp2 : 1 ≤ p.2 := by
      have := hp.2
      simp only [mem_Ioi] at this
      linarith
    exact norm_tailTimesConst_div_le u hv hp2

/-- **Zero mean of the subtracted constant term against the truncated series.** -/
theorem setIntegral_trunc_mul_aboveConst_eq_zero (u : ℂ) {v : ℂ} (hv : 0 ≤ v.re) {Y : ℝ}
    (hY : 1 ≤ Y) :
    ∫ z in fd, truncatedLineModel u Y z *
      (if Y < z.im then d4BMCompletedEisensteinCuspConstantPart .scalar v z.im else 0) = 0 := by
  have hset : MeasurableSet {z : ℍ | Y < z.im} :=
    measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  have h1 : (fun z : ℍ => truncatedLineModel u Y z *
      (if Y < z.im then d4BMCompletedEisensteinCuspConstantPart .scalar v z.im else 0)) =
      {z : ℍ | Y < z.im}.indicator (fun z => tailTimesConst u v (z.re, z.im)) := by
    funext z
    by_cases hz : Y < z.im
    · rw [if_pos hz, Set.indicator_of_mem (show z ∈ {z : ℍ | Y < z.im} from hz)]
      unfold tailTimesConst truncatedLineModel eisensteinLineModel d4BMCompletedEisensteinCuspLeg
      rw [if_pos hz, add_sub_cancel_left]
    · rw [if_neg hz, Set.indicator_of_notMem (show z ∉ {z : ℍ | Y < z.im} from hz), mul_zero]
  rw [h1, setIntegral_indicator hset, setIntegral_fd_above_eq hY, cuspRect,
    setIntegral_prod_eq_iterated (integrableOn_tailTimesConst_div u hv hY)]
  have hinner : ∀ y ∈ Ioi Y, (∫ x in unitIcc, tailTimesConst u v (x, y) / ((y : ℝ) : ℂ) ^ 2) = 0 := by
    intro y hy
    have hy0 : 0 < y := by simp only [mem_Ioi] at hy; linarith
    have : (fun x => tailTimesConst u v (x, y) / ((y : ℝ) : ℂ) ^ 2) =
        fun x => (d4BMCompletedEisensteinCuspConstantPart .scalar v y / ((y : ℝ) : ℂ) ^ 2) *
          d4BMCompletedEisensteinCuspTailPart .scalar u x y := by
      funext x; unfold tailTimesConst; ring
    rw [this, integral_const_mul, setIntegral_unitIcc_cuspTailPart hy0 u, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  simp

/-! ## The identity in the region -/

/-- **Maass–Selberg in the absolutely convergent region.**  For `Re u > Re v > ½`, `Im v > 0`,
`Y ≥ 1`: `(u−v)(u+v)·∫_𝒟 Λ^Y E_u · Λ^Y E_v = R(u, v, Y)`. -/
theorem maassSelberg_region {u v : ℂ} (hv1 : 1 / 2 < v.re) (huv : v.re < u.re)
    (hv : v ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) :
    (u - v) * (u + v) *
        ∫ z in fd, truncatedLineModel u Y z * truncatedLineModel v Y z = msRight u v Y := by
  have hu : 1 / 2 < u.re := by linarith
  have huv0 : u - v ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hupv : u + v ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  -- Step 1: replace the second truncation by the full line model
  have hstep1 : (∫ z in fd, truncatedLineModel u Y z * truncatedLineModel v Y z) =
      ∫ z in fd, truncatedLineModel u Y z * eisensteinLineModel v z := by
    have hdiff : (fun z : ℍ => truncatedLineModel u Y z * truncatedLineModel v Y z) =
        fun z => truncatedLineModel u Y z * eisensteinLineModel v z -
          truncatedLineModel u Y z *
            (if Y < z.im then d4BMCompletedEisensteinCuspConstantPart .scalar v z.im else 0) := by
      funext z
      unfold truncatedLineModel
      ring
    have hi2 : IntegrableOn (fun z : ℍ => truncatedLineModel u Y z *
        (if Y < z.im then d4BMCompletedEisensteinCuspConstantPart .scalar v z.im else 0)) fd volume := by
      have h := (integrableOn_trunc_mul_line hu.le hv1.le hY).sub
        (integrableOn_trunc_mul_trunc hu.le hv1.le hY)
      refine h.congr_fun (fun z _ => ?_) isClosed_fd.measurableSet
      simp only [Pi.sub_apply]
      unfold truncatedLineModel
      ring
    rw [hdiff, integral_sub (integrableOn_trunc_mul_line hu.le hv1.le hY) hi2,
      setIntegral_trunc_mul_aboveConst_eq_zero u (by linarith) hY, sub_zero]
  -- Step 2: the truncation identity for `u`
  have hstep2 : (∫ z in fd, truncatedLineModel u Y z * eisensteinLineModel v z) =
      msA u * ((1 / 2 : ℂ) * ∫ z in fd, truncatedRowSum (1 / 2 + u) Y z * eisensteinLineModel v z) -
        msB u * ∫ z in fd ∩ {z : ℍ | Y < z.im},
          ((z.im : ℝ) : ℂ) ^ (1 / 2 - u) * eisensteinLineModel v z := by
    have hpt : ∀ z ∈ fd, truncatedLineModel u Y z * eisensteinLineModel v z =
        msA u * ((1 / 2 : ℂ) * (truncatedRowSum (1 / 2 + u) Y z * eisensteinLineModel v z)) -
          msB u * ((if Y < z.im then ((z.im : ℝ) : ℂ) ^ (1 / 2 - u) else 0) *
            eisensteinLineModel v z) := by
      intro z hz
      rw [truncatedLineModel_eq_truncatedRowSum hu hz hY]
      ring
    rw [setIntegral_congr_fun isClosed_fd.measurableSet hpt]
    have hi1 := (integrableOn_truncatedRowSum_mul_line hu hv1.le huv hY).const_mul (1 / 2 : ℂ)
      |>.const_mul (msA u)
    have hi2 := (integrableOn_aboveHeight_cpow_mul_line hv1.le huv hY).const_mul (msB u)
    rw [integral_sub hi1 hi2, integral_const_mul, integral_const_mul, integral_const_mul]
    congr 2
    have hset : MeasurableSet {z : ℍ | Y < z.im} :=
      measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
    have hind : (fun z : ℍ => (if Y < z.im then ((z.im : ℝ) : ℂ) ^ (1 / 2 - u) else 0) *
        eisensteinLineModel v z) =
        {z : ℍ | Y < z.im}.indicator
          (fun z => ((z.im : ℝ) : ℂ) ^ (1 / 2 - u) * eisensteinLineModel v z) := by
      funext z
      by_cases hz : Y < z.im
      · rw [if_pos hz, Set.indicator_of_mem (show z ∈ {z : ℍ | Y < z.im} from hz)]
      · rw [if_neg hz, Set.indicator_of_notMem (show z ∉ {z : ℍ | Y < z.im} from hz), zero_mul]
    rw [hind, setIntegral_indicator hset]
  -- Step 3: unfold and evaluate
  rw [hstep1, hstep2, setIntegral_truncatedRowSum_mul_eq hu hv1 huv hv hY,
    setIntegral_slab_eq hu hv1 huv hv hY, setIntegral_cusp_eq hv1 huv hY]
  unfold msRight
  field_simp
  ring

end

end RHTower
