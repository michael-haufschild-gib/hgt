import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLineInvariance
import GaloisForLFunctions.RHTower.EisensteinLineZeroMean
import GaloisForLFunctions.RHTower.EisensteinMaassSelbergAlgebra

/-!
# Bounds and continuity of the Eisenstein line model at every parameter

For every parameter `u ∈ ℂ` and height `Y ≥ 1/2`, the cusp tail of the completed Eisenstein
Fourier model is exponentially small, `‖tail_u(x, Y)‖ ≤ tailConst u · e^{−2πY}`, uniformly in `x`;
hence `‖E_u(x + iY)‖ ≤ ‖B(u)‖ Y^{½−Re u} + ‖A(u)‖ Y^{½+Re u} + tailConst u · e^{−2πY}`.  The model is
jointly continuous in `(x, Y)` on `Y > 0`, so `E_u` is a continuous function on `ℍ`.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The majorant is decreasing in the height -/

theorem eisensteinTailMajorant_eq {Y : ℝ} (hY : 0 < Y) (u : ℂ) (N : ℕ) :
    eisensteinTailMajorant Y u N =
      Real.exp ((‖u‖ + 1) ^ 2 / (4 * Real.pi * Y)) *
        (((N : ℝ) + 1) ^ (⌈3 * (‖u‖ + 1) + 1⌉₊) *
          Real.exp (-(2 * Real.pi * Y) * ((N : ℝ) + 1))) := by
  unfold eisensteinTailMajorant
  have h : Real.sqrt Y * Real.sqrt (1 / Y) = 1 := by
    rw [← Real.sqrt_mul hY.le, mul_one_div_cancel hY.ne', Real.sqrt_one]
  calc (Real.sqrt Y * Real.exp ((‖u‖ + 1) ^ 2 / (4 * Real.pi * Y)) * Real.sqrt (1 / Y)) *
        (((N : ℝ) + 1) ^ (⌈3 * (‖u‖ + 1) + 1⌉₊) * Real.exp (-(2 * Real.pi * Y) * ((N : ℝ) + 1)))
      = (Real.sqrt Y * Real.sqrt (1 / Y)) * (Real.exp ((‖u‖ + 1) ^ 2 / (4 * Real.pi * Y)) *
        (((N : ℝ) + 1) ^ (⌈3 * (‖u‖ + 1) + 1⌉₊) *
          Real.exp (-(2 * Real.pi * Y) * ((N : ℝ) + 1)))) := by ring
    _ = _ := by rw [h, one_mul]

theorem eisensteinTailMajorant_nonneg {Y : ℝ} (hY : 0 < Y) (u : ℂ) (N : ℕ) :
    0 ≤ eisensteinTailMajorant Y u N := by
  rw [eisensteinTailMajorant_eq hY]
  positivity

theorem eisensteinTailMajorant_mono {Y₀ Y : ℝ} (hY₀ : 0 < Y₀) (hY : Y₀ ≤ Y) (u : ℂ) (N : ℕ) :
    eisensteinTailMajorant Y u N ≤ eisensteinTailMajorant Y₀ u N := by
  have hYpos : 0 < Y := hY₀.trans_le hY
  rw [eisensteinTailMajorant_eq hYpos, eisensteinTailMajorant_eq hY₀]
  have h1 : Real.exp ((‖u‖ + 1) ^ 2 / (4 * Real.pi * Y)) ≤
      Real.exp ((‖u‖ + 1) ^ 2 / (4 * Real.pi * Y₀)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have := Real.pi_pos
    nlinarith
  have h2 : Real.exp (-(2 * Real.pi * Y) * ((N : ℝ) + 1)) ≤
      Real.exp (-(2 * Real.pi * Y₀) * ((N : ℝ) + 1)) := by
    apply Real.exp_le_exp.mpr
    have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 2 * Real.pi)) hN
    linarith
  exact mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
    (by positivity)

/-- Uniform bound of the tail terms on `{Y ≥ Y₀}`. -/
theorem norm_eisensteinTailTerm_le_of_le (negative : Bool) (x : ℝ) {Y₀ Y : ℝ} (hY₀ : 0 < Y₀)
    (hY : Y₀ ≤ Y) (u : ℂ) (N : ℕ) :
    ‖eisensteinTailTerm negative x Y N u‖ ≤ eisensteinTailMajorant Y₀ u N :=
  (norm_eisensteinTailTerm_le negative x (hY₀.trans_le hY) u N
    (Metric.mem_ball_self one_pos)).trans (eisensteinTailMajorant_mono hY₀ hY u N)

/-! ## Exponential decay of the tail for `Y ≥ 1/2` -/

/-- The height-free majorant series `(N+1)^k e^{−πN}`. -/
def tailSeriesTerm (u : ℂ) (N : ℕ) : ℝ :=
  ((N : ℝ) + 1) ^ (⌈3 * (‖u‖ + 1) + 1⌉₊) * Real.exp (-Real.pi * (N : ℝ))

theorem tailSeriesTerm_nonneg (u : ℂ) (N : ℕ) : 0 ≤ tailSeriesTerm u N := by
  unfold tailSeriesTerm; positivity

theorem summable_tailSeriesTerm (u : ℂ) : Summable (tailSeriesTerm u) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul (⌈3 * (‖u‖ + 1) + 1⌉₊) Real.pi_pos
  have h' := (summable_nat_add_iff 1).mpr h
  have h'' : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (⌈3 * (‖u‖ + 1) + 1⌉₊) *
      Real.exp (-Real.pi * ((n : ℝ) + 1)) := by
    refine h'.congr fun n => ?_
    push_cast
    ring_nf
  have h3 := h''.mul_right (Real.exp Real.pi)
  refine h3.congr fun n => ?_
  unfold tailSeriesTerm
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

/-- The sum of the height-free majorant series. -/
def tailSeriesSum (u : ℂ) : ℝ := ∑' N : ℕ, tailSeriesTerm u N

theorem tailSeriesSum_nonneg (u : ℂ) : 0 ≤ tailSeriesSum u :=
  tsum_nonneg fun N => tailSeriesTerm_nonneg u N

/-- For `Y ≥ 1/2` the majorant is `e^{−2πY}` times a height-free summable series. -/
theorem eisensteinTailMajorant_le_exp {Y : ℝ} (hY : 1 / 2 ≤ Y) (u : ℂ) (N : ℕ) :
    eisensteinTailMajorant Y u N ≤
      Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) * Real.exp (-(2 * Real.pi * Y)) *
        tailSeriesTerm u N := by
  have hYpos : 0 < Y := by linarith
  rw [eisensteinTailMajorant_eq hYpos]
  unfold tailSeriesTerm
  have hpi := Real.pi_pos
  have h1 : Real.exp ((‖u‖ + 1) ^ 2 / (4 * Real.pi * Y)) ≤
      Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have h2 : Real.exp (-(2 * Real.pi * Y) * ((N : ℝ) + 1)) ≤
      Real.exp (-(2 * Real.pi * Y)) * Real.exp (-Real.pi * (N : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hN : (0 : ℝ) ≤ (N : ℝ) := N.cast_nonneg
    nlinarith [mul_nonneg hpi.le hN]
  calc Real.exp ((‖u‖ + 1) ^ 2 / (4 * Real.pi * Y)) *
        (((N : ℝ) + 1) ^ (⌈3 * (‖u‖ + 1) + 1⌉₊) * Real.exp (-(2 * Real.pi * Y) * ((N : ℝ) + 1)))
      ≤ Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) *
        (((N : ℝ) + 1) ^ (⌈3 * (‖u‖ + 1) + 1⌉₊) *
          (Real.exp (-(2 * Real.pi * Y)) * Real.exp (-Real.pi * (N : ℝ)))) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
          (by positivity)
    _ = _ := by ring

/-- The tail constant `tailConst u`. -/
def tailConst (u : ℂ) : ℝ := 4 * Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) * tailSeriesSum u

theorem tailConst_nonneg (u : ℂ) : 0 ≤ tailConst u := by
  unfold tailConst
  have := tailSeriesSum_nonneg u
  positivity

theorem summable_eisensteinTailTerm (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    Summable (fun N => eisensteinTailTerm negative x Y N u) :=
  Summable.of_norm_bounded (summable_eisensteinTailMajorant hY u)
    (fun N => norm_eisensteinTailTerm_le negative x hY u N (Metric.mem_ball_self one_pos))

/-- Exponential decay of a signed tail for `Y ≥ 1/2`. -/
theorem norm_signedSqrtWhittakerTail_le_exp (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y)
    (u : ℂ) :
    ‖d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative x 0 0 Y‖ ≤
      Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) * Real.exp (-(2 * Real.pi * Y)) *
        tailSeriesSum u := by
  have hYpos : 0 < Y := by linarith
  rw [signedSqrtWhittakerTail_eq_tsum_term]
  have hs := summable_eisensteinTailTerm negative x hYpos u
  calc ‖∑' N : ℕ, eisensteinTailTerm negative x Y N u‖
      ≤ ∑' N : ℕ, ‖eisensteinTailTerm negative x Y N u‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' N : ℕ, Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) * Real.exp (-(2 * Real.pi * Y)) *
          tailSeriesTerm u N := by
        refine Summable.tsum_le_tsum (fun N => ?_) hs.norm
          ((summable_tailSeriesTerm u).mul_left _)
        exact (norm_eisensteinTailTerm_le negative x hYpos u N
          (Metric.mem_ball_self one_pos)).trans (eisensteinTailMajorant_le_exp hY u N)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- **Exponential decay of the cusp tail** for `Y ≥ 1/2`, uniformly in `x`. -/
theorem norm_cuspTailPart_le_exp (u : ℂ) (x : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    ‖d4BMCompletedEisensteinCuspTailPart .scalar u x Y‖ ≤
      tailConst u * Real.exp (-(2 * Real.pi * Y)) := by
  rw [cuspTailPart_scalar_eq]
  have h1 := norm_signedSqrtWhittakerTail_le_exp false x hY u
  have h2 := norm_signedSqrtWhittakerTail_le_exp true x hY u
  calc ‖(2 : ℂ) * (d4BMCompletedEisensteinSignedSqrtWhittakerTail u u false x 0 0 Y +
          d4BMCompletedEisensteinSignedSqrtWhittakerTail u u true x 0 0 Y)‖
      = 2 * ‖d4BMCompletedEisensteinSignedSqrtWhittakerTail u u false x 0 0 Y +
          d4BMCompletedEisensteinSignedSqrtWhittakerTail u u true x 0 0 Y‖ := by
        rw [norm_mul]; norm_num
    _ ≤ 2 * (‖d4BMCompletedEisensteinSignedSqrtWhittakerTail u u false x 0 0 Y‖ +
          ‖d4BMCompletedEisensteinSignedSqrtWhittakerTail u u true x 0 0 Y‖) := by
        gcongr; exact norm_add_le _ _
    _ ≤ 2 * (Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) * Real.exp (-(2 * Real.pi * Y)) *
          tailSeriesSum u + Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) *
          Real.exp (-(2 * Real.pi * Y)) * tailSeriesSum u) := by gcongr
    _ = tailConst u * Real.exp (-(2 * Real.pi * Y)) := by unfold tailConst; ring

/-! ## The constant part and the full model -/

theorem re_half_sub (u : ℂ) : (1 / 2 - u).re = 1 / 2 - u.re := by simp
theorem re_half_add (u : ℂ) : (1 / 2 + u).re = 1 / 2 + u.re := by simp

theorem norm_cuspConstantPart_le {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    ‖d4BMCompletedEisensteinCuspConstantPart .scalar u Y‖ ≤
      ‖msB u‖ * Y ^ (1 / 2 - u.re) + ‖msA u‖ * Y ^ (1 / 2 + u.re) := by
  rw [cuspConstantPart_eq_msAB]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY,
    Complex.norm_cpow_eq_rpow_re_of_pos hY, re_half_sub, re_half_add]

/-- **The uniform bound of the line model** for `Im z ≥ 1/2`. -/
theorem norm_eisensteinLineModel_le (u : ℂ) {z : ℍ} (hz : 1 / 2 ≤ z.im) :
    ‖eisensteinLineModel u z‖ ≤
      ‖msB u‖ * z.im ^ (1 / 2 - u.re) + ‖msA u‖ * z.im ^ (1 / 2 + u.re) +
        tailConst u * Real.exp (-(2 * Real.pi * z.im)) := by
  unfold eisensteinLineModel d4BMCompletedEisensteinCuspLeg
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_cuspConstantPart_le z.im_pos u
  have h2 := norm_cuspTailPart_le_exp u z.re hz
  linarith

/-! ## Joint continuity in `(x, Y)` -/

theorem continuousOn_eisensteinTailTerm_pair' (negative : Bool) (N : ℕ) (u : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => eisensteinTailTerm negative p.1 p.2 N u)
      {p : ℝ × ℝ | 0 < p.2} := by
  simp_rw [eisensteinTailTerm_eq_amplitude_mul_phase]
  unfold eisensteinTailAmplitude
  have hK : ContinuousOn (fun p : ℝ × ℝ =>
      modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * p.2) u) {p : ℝ × ℝ | 0 < p.2} := by
    have := continuousOn_modifiedBesselKOrder_scaled (c := 2 * Real.pi * ((N : ℝ) + 1))
      (by positivity) u
    exact this.comp continuous_snd.continuousOn (fun p hp => hp)
  have hs : Continuous (fun p : ℝ × ℝ => ((Real.sqrt p.2 : ℝ) : ℂ)) := by fun_prop
  have hph : Continuous (fun p : ℝ × ℝ => d4BMCompletedEisensteinFourierPhase negative N p.1) :=
    (continuous_fourierPhase negative N).comp continuous_fst
  exact ((continuousOn_const.mul hs.continuousOn).mul hK).mul hph.continuousOn

theorem continuousOn_signedSqrtWhittakerTail_pair (negative : Bool) (u : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative p.1 0 0 p.2)
      {p : ℝ × ℝ | 0 < p.2} := by
  intro p₀ hp₀
  simp only [mem_setOf_eq] at hp₀
  have hY₀ : 0 < p₀.2 / 2 := by positivity
  have hS : ContinuousOn (fun p : ℝ × ℝ =>
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative p.1 0 0 p.2)
      {p : ℝ × ℝ | p₀.2 / 2 ≤ p.2} := by
    simp_rw [signedSqrtWhittakerTail_eq_tsum_term]
    refine continuousOn_tsum (fun N => (continuousOn_eisensteinTailTerm_pair' negative N u).mono
      (fun p hp => lt_of_lt_of_le hY₀ hp)) (summable_eisensteinTailMajorant hY₀ u)
      fun N p hp => norm_eisensteinTailTerm_le_of_le negative p.1 hY₀ hp u N
  have hmem : {p : ℝ × ℝ | p₀.2 / 2 ≤ p.2} ∈ 𝓝 p₀ := by
    refine mem_nhds_iff.mpr ⟨{p : ℝ × ℝ | p₀.2 / 2 < p.2}, fun p hp => ?_,
      isOpen_lt continuous_const continuous_snd, ?_⟩
    · simp only [mem_setOf_eq] at hp ⊢; exact hp.le
    simp only [mem_setOf_eq]; linarith
  exact (hS.continuousAt hmem).continuousWithinAt

theorem continuousOn_cuspTailPart_pair (u : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => d4BMCompletedEisensteinCuspTailPart .scalar u p.1 p.2)
      {p : ℝ × ℝ | 0 < p.2} := by
  simp_rw [cuspTailPart_scalar_eq]
  exact continuousOn_const.mul ((continuousOn_signedSqrtWhittakerTail_pair false u).add
    (continuousOn_signedSqrtWhittakerTail_pair true u))

theorem continuousOn_cuspConstantPart_pair (u : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => d4BMCompletedEisensteinCuspConstantPart .scalar u p.2)
      {p : ℝ × ℝ | 0 < p.2} := by
  simp_rw [cuspConstantPart_eq_msAB]
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) {p : ℝ × ℝ | 0 < p.2} :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn
  have hslit : ∀ p ∈ {p : ℝ × ℝ | 0 < p.2}, ((p.2 : ℝ) : ℂ) ∈ Complex.slitPlane :=
    fun p hp => Complex.ofReal_mem_slitPlane.mpr hp
  exact (continuousOn_const.mul (hc.cpow_const hslit)).add
    (continuousOn_const.mul (hc.cpow_const hslit))

/-- **Joint continuity of the Fourier model** in `(x, Y)` on `Y > 0`. -/
theorem continuousOn_cuspLeg_pair (u : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => d4BMCompletedEisensteinCuspLeg .scalar u p.1 p.2)
      {p : ℝ × ℝ | 0 < p.2} := by
  unfold d4BMCompletedEisensteinCuspLeg
  exact (continuousOn_cuspConstantPart_pair u).add (continuousOn_cuspTailPart_pair u)

/-- **The line model is continuous on `ℍ`.** -/
theorem continuous_eisensteinLineModel (u : ℂ) : Continuous (eisensteinLineModel u) := by
  have hmap : Continuous (fun z : ℍ => (z.re, z.im)) :=
    UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im
  have h := (continuousOn_cuspLeg_pair u).comp_continuous hmap (fun z => z.im_pos)
  exact h

end

end RHTower
