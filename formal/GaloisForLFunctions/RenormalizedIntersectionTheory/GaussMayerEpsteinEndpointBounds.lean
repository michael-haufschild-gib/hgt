import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinHeightGrowth
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinReciprocity

/-! The Cauchy weight cancels the spectral growth introduced by height
reciprocity. Splitting at the target height leaves integrable powers at
both endpoints of the positive ray. The Gamma normalization remains
holomorphic and nonzero throughout the source half-plane. -/

open Complex Real Set MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerEpsteinQuadrants MayerEpsteinHeightGrowth
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinEndpointBounds

private theorem norm_cauchyWeight (w : ℂ) (t : ℝ) :
    ‖cauchyWeight w t‖=(1+t^2)^(-(w.re+2)/2) := by
  unfold cauchyWeight
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 1+t^2)]
  congr 1
  simp
  ring

/-- The Cauchy weight has norm at most one on the source half-plane. -/
theorem norm_cauchyWeight_le_one {w : ℂ} (hw : 0 ≤ w.re) (t : ℝ) :
    ‖cauchyWeight w t‖ ≤ 1 := by
  rw [norm_cauchyWeight]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith only [sq_nonneg t])
    (by linarith only [hw])

/-- Its second bound retains exactly the spectral decay needed for reciprocity. -/
theorem norm_cauchyWeight_le_power {w : ℂ} (hw : 0 ≤ w.re) {t : ℝ} (ht : 0 < t) :
    ‖cauchyWeight w t‖ ≤ t^(-w.re-2) := by
  rw [norm_cauchyWeight]
  calc
    _ ≤ (t^2)^(-(w.re+2)/2) := Real.rpow_le_rpow_of_nonpos
      (by positivity : 0 < t^2) (by linarith) (by linarith only [hw])
    _ = t^(-w.re-2) := by
      rw [← Real.rpow_natCast t 2,← Real.rpow_mul ht.le]
      congr 1
      ring

private theorem small_power {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (η : ℝ) :
    (a/t)^(1-η)=a^(1-η)*t^(-1+η) := by
  rw [Real.rpow_def_of_pos (div_pos ha ht),Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos ht,Real.log_div ha.ne' ht.ne',← Real.exp_add]
  congr 1
  ring

private theorem reciprocal_power {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (σ η : ℝ) :
    t^(-σ-2)*(a/t)^(-σ)*(t/a)^(1-η)=a^(-σ-1+η)*t^(-1-η) := by
  rw [Real.rpow_def_of_pos ht,Real.rpow_def_of_pos (div_pos ha ht),
    Real.rpow_def_of_pos (div_pos ht ha),Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos ht,Real.log_div ha.ne' ht.ne',Real.log_div ht.ne' ha.ne']
  rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

/-- At the zero endpoint, sublinear height growth leaves the power `t^(-1+η)`. -/
theorem small_endpoint {w : ℂ} (hw2 : w ≠ 2) {η β a t : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hηw : η ≤ w.re) (hβ : 1 < β)
    (hwβ : w.re ≤ β) (ht : 0 < t) (hta : t ≤ a) :
    ‖cauchyWeight w t*epsteinField w (a/t)‖ ≤
      growthCoefficient η β w*a^(1-η)*t^(-1+η) := by
  have ha : 0 < a := ht.trans_le hta
  have hheight : 1 ≤ a/t := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using hta)
  have hE := norm_epsteinField_le_power hw2 hη0 hη1 hηw hβ hwβ hheight
  have hq := norm_cauchyWeight_le_one (hη0.le.trans hηw) t
  calc
    _ = ‖cauchyWeight w t‖*‖epsteinField w (a/t)‖ := norm_mul _ _
    _ ≤ ‖epsteinField w (a/t)‖ := mul_le_of_le_one_left (norm_nonneg _) hq
    _ ≤ _ := hE
    _ = _ := by rw [small_power ha ht]; ring

/-- At infinity, the spectral exponents cancel and leave `t^(-1-η)`. -/
theorem large_endpoint {w : ℂ} (hw2 : w ≠ 2) {η β a t : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hηw : η ≤ w.re) (hβ : 1 < β)
    (hwβ : w.re ≤ β) (ha : 0 < a) (hat : a ≤ t) :
    ‖cauchyWeight w t*epsteinField w (a/t)‖ ≤
      growthCoefficient η β w*a^(-w.re-1+η)*t^(-1-η) := by
  have ht : 0 < t := ha.trans_le hat
  have hheight : 1 ≤ t/a := (le_div_iff₀ ha).mpr (by simpa only [one_mul] using hat)
  have hE := norm_epsteinField_le_power hw2 hη0 hη1 hηw hβ hwβ hheight
  have hrec := MayerEpsteinReciprocity.reciprocity (hη0.trans_le hηw) hw2 (div_pos ha ht)
  have hinv : 1/(a/t)=t/a := by field_simp
  rw [hinv] at hrec
  have hEnorm : ‖epsteinField w (a/t)‖=(a/t)^(-w.re)*‖epsteinField w (t/a)‖ := by
    rw [hrec,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (div_pos ha ht)]
    simp only [Complex.neg_re]
  calc
    _ = ‖cauchyWeight w t‖*((a/t)^(-w.re)*‖epsteinField w (t/a)‖) := by
      rw [norm_mul,hEnorm]
    _ ≤ t^(-w.re-2)*((a/t)^(-w.re)*(growthCoefficient η β w*(t/a)^(1-η))) := by
      apply mul_le_mul (norm_cauchyWeight_le_power (hη0.le.trans hηw) ht)
      · exact mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg (div_pos ha ht).le _)
      · positivity
      · positivity
    _ = growthCoefficient η β w*(t^(-w.re-2)*(a/t)^(-w.re)*(t/a)^(1-η)) := by ring
    _ = _ := by rw [reciprocal_power ha ht]; ring


private theorem gamma_avoids_poles {s : ℂ} (hs : 0 < s.re) (n : ℕ) : s ≠ -(n : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.neg_re,Complex.natCast_re] at hr
  linarith only [hr,hs,Nat.cast_nonneg (α := ℝ) n]

/-- The Cauchy normalization remains nonzero throughout the source half-plane. -/
theorem averagingFactor_ne_zero_halfPlane {w : ℂ} (hw : 0 < w.re) : averagingFactor w ≠ 0 := by
  have hs : 0 < ((w+2)/2).re := by norm_num [Complex.div_re]; linarith only [hw]
  have ht : 0 < (((w+2)/2)-1/2).re := by norm_num [Complex.div_re]; linarith only [hw]
  unfold averagingFactor MayerScatteringNormalization.archimedeanFactor
  apply div_ne_zero _ (by norm_num)
  apply div_ne_zero _ (Complex.Gamma_ne_zero (gamma_avoids_poles hs))
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.Gamma_ne_zero (gamma_avoids_poles ht))

/-- The Gamma quotient defining the normalization is holomorphic on the source half-plane. -/
theorem differentiableAt_averagingFactor {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ averagingFactor w := by
  have hs : 0 < ((w+2)/2).re := by norm_num [Complex.div_re]; linarith only [hw]
  have ht : 0 < (((w+2)/2)-1/2).re := by norm_num [Complex.div_re]; linarith only [hw]
  have hg0 := (Complex.differentiableAt_Gamma _ (gamma_avoids_poles hs)).comp w
    ((differentiableAt_id.add_const (2 : ℂ)).div_const 2)
  have hg1 := (Complex.differentiableAt_Gamma _ (gamma_avoids_poles ht)).comp w
    (((differentiableAt_id.add_const (2 : ℂ)).div_const 2).sub_const (1/2))
  exact (((differentiableAt_const ((Real.pi : ℂ)^(1/2 : ℂ))).mul hg1).div hg0
    (Complex.Gamma_ne_zero (gamma_avoids_poles hs))).div_const 2

/-- At each real integration point the Cauchy power is entire in the spectral parameter. -/
theorem differentiable_cauchyWeight (t : ℝ) : Differentiable ℂ (fun w => cauchyWeight w t) := by
  have hn : ((1+t^2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [cauchyWeight,Complex.cpow_def_of_ne_zero hn]
  fun_prop

/-- The normalized averaging kernel is holomorphic in the source half-plane. -/
theorem differentiableAt_cauchyKernel {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    DifferentiableAt ℂ (fun v => cauchyKernel v t) w :=
  (((differentiableAt_averagingFactor hw).inv (averagingFactor_ne_zero_halfPlane hw)).mul_const
    (t : ℂ)).mul (differentiable_cauchyWeight t w)

#print axioms averagingFactor_ne_zero_halfPlane
#print axioms differentiableAt_averagingFactor
#print axioms differentiable_cauchyWeight
#print axioms differentiableAt_cauchyKernel

#print axioms norm_cauchyWeight_le_one
#print axioms norm_cauchyWeight_le_power
#print axioms small_endpoint
#print axioms large_endpoint
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinEndpointBounds
