import GaloisForLFunctions.ExactEventTheory.IntegrableDefectsHaveDecayingBoundary
import GaloisForLFunctions.HTGeometry.MellinRegularStripLinear

/-!
# Boundary energy of the functional-equation defect

The two imaginary boundary rays of the Hamburger kernel have complementary Mellin
weights. Their joint energy is exactly `π⁻¹` times the defect's energy.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.HamburgerStability
open GaloisForLFunctions.ExactEventTheory GaloisForLFunctions.HTGeometry
open scoped FourierTransform

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Reflection cancels the two powers of `π`, leaving an inverse sine multiplier. -/
theorem boundaryPairKernel_eq_cpow_div_sin (v : ℝ) {z : ℂ} (hz : z ≠ 0) :
    boundaryPairKernel v z =
      z ^ (linePt v - 1) / Complex.sin ((Real.pi : ℂ) * (linePt v / 2)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hp : (Real.pi : ℂ) ^ (-linePt v / 2) *
      (Real.pi : ℂ) ^ (-(1 - linePt v / 2)) = (Real.pi : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hπ]
    convert Complex.cpow_neg_one (Real.pi : ℂ) using 1
    congr 1
    ring
  have hzpow : z * z ^ (2 * (-(1 - linePt v / 2))) = z ^ (linePt v - 1) := by
    nth_rw 1 [← Complex.cpow_one z]
    rw [← Complex.cpow_add _ _ hz]
    congr 1
    ring
  unfold boundaryPairKernel gammaPair
  rw [Complex.Gamma_mul_Gamma_one_sub]
  calc
    _ = ((Real.pi : ℂ) ^ (-linePt v / 2) *
        (Real.pi : ℂ) ^ (-(1 - linePt v / 2))) * (Real.pi : ℂ) *
        (z * z ^ (2 * (-(1 - linePt v / 2)))) /
          Complex.sin ((Real.pi : ℂ) * (linePt v / 2)) := by ring
    _ = _ := by rw [hp, hzpow, inv_mul_cancel₀ hπ, one_mul]

/-- Positive dilation is diagonal in the critical Mellin frequency. -/
theorem boundaryPairKernel_mul_pos (v : ℝ) {y : ℝ} (hy : 0 < y)
    {z : ℂ} (hz : z ≠ 0) :
    boundaryPairKernel v ((y : ℂ) * z) =
      (y : ℂ) ^ (linePt v - 1) * boundaryPairKernel v z := by
  rw [boundaryPairKernel_eq_cpow_div_sin v (mul_ne_zero (by exact_mod_cast hy.ne') hz),
    boundaryPairKernel_eq_cpow_div_sin v hz]
  have hpow : ((y : ℂ) * z) ^ (linePt v - 1) =
      (y : ℂ) ^ (linePt v - 1) * z ^ (linePt v - 1) := by
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hyc hz),
      Complex.cpow_def_of_ne_zero hyc, Complex.cpow_def_of_ne_zero hz,
      Complex.log_ofReal_mul hy hz, Complex.ofReal_log hy.le, add_mul, Complex.exp_add]
  rw [hpow, mul_div_assoc]

private theorem norm_sin_quarter_sq (y : ℝ) :
    ‖Complex.sin (((Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 =
      (Real.exp (2 * y) + Real.exp (-(2 * y))) / 4 := by
  rw [Complex.sq_norm]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [Complex.sin_add_mul_I]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, Real.sin_pi_div_four, Real.cos_pi_div_four,
    Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
  simp only [mul_zero, sub_zero, zero_mul, zero_add, add_zero, mul_one]
  rw [Real.cosh_eq, Real.sinh_eq, show -(2 * y) = -y + -y by ring,
    show 2 * y = y + y by ring, Real.exp_add, Real.exp_add]
  ring_nf
  rw [hs]
  ring

private theorem norm_boundaryPairKernel_unit (v : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖boundaryPairKernel v z‖ = Real.exp (-(z.arg * v)) /
      ‖Complex.sin ((Real.pi : ℂ) * (linePt v / 2))‖ := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [boundaryPairKernel_eq_cpow_div_sin v hz0, norm_div,
    Complex.norm_cpow_of_ne_zero hz0, hz, Real.one_rpow]
  have hi : (linePt v - 1).im = v := by simp [linePt]
  rw [hi, one_div, ← Real.exp_neg]

/-- The two boundary multipliers partition a constant amount of Mellin energy. -/
theorem boundaryPairKernel_paired_norm_sq (t : ℝ) :
    ‖boundaryPairKernel (2 * t) I‖ ^ 2 +
      ‖boundaryPairKernel (2 * t) (-I)‖ ^ 2 = 4 := by
  have hs : (Real.pi : ℂ) * (linePt (2 * t) / 2) =
      ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * t : ℝ) : ℂ) * I := by
    simp only [linePt]; push_cast; ring
  rw [norm_boundaryPairKernel_unit (2 * t) (by simp : ‖I‖ = 1),
    norm_boundaryPairKernel_unit (2 * t) (by simp : ‖-I‖ = 1),
    Complex.arg_I, Complex.arg_neg_I, div_pow, div_pow, ← add_div, hs,
    norm_sin_quarter_sq]
  have hp : Real.exp (-(Real.pi / 2 * (2 * t))) ^ 2 =
      Real.exp (-(2 * (Real.pi * t))) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hm : Real.exp (-(-(Real.pi / 2) * (2 * t))) ^ 2 =
      Real.exp (2 * (Real.pi * t)) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  rw [hp, hm]
  have hpos : 0 < Real.exp (2 * (Real.pi * t)) + Real.exp (-(2 * (Real.pi * t))) := by positivity
  field_simp
  ring

private def halfMellinData (f : ℝ → ℂ) (s : ℂ) : ℂ := (1 / 2 : ℂ) * f (-s.im / 2)

private theorem halfMellinData_line (f : ℝ → ℂ) (σ v : ℝ) :
    halfMellinData f ((σ : ℂ) + v * I) = (1 / 2 : ℂ) * f ((-1 / 2 : ℝ) * v) := by
  have hi : ((σ : ℂ) + (v : ℂ) * I).im = v := by simp
  rw [halfMellinData, hi]
  congr 2
  ring

private theorem integrable_halfMellinData {f : ℝ → ℂ} (hf : Integrable f) {σ : ℝ} :
    Integrable fun v : ℝ => halfMellinData f ((σ : ℂ) + v * I) := by
  simp only [halfMellinData_line]
  exact (hf.comp_mul_left' (by norm_num : (-1 / 2 : ℝ) ≠ 0)).const_mul _

private theorem memLp_halfMellinData {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) {σ : ℝ} :
    MemLp (fun v : ℝ => halfMellinData f ((σ : ℂ) + v * I)) 2 := by
  rw [memLp_two_iff_integrable_sq_norm (integrable_halfMellinData hf).aestronglyMeasurable]
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf2
  have hi := (hsq.comp_mul_left' (by norm_num : (-1 / 2 : ℝ) ≠ 0)).const_mul (1 / 4 : ℝ)
  convert hi using 1
  funext v
  rw [halfMellinData_line, norm_mul, mul_pow]
  norm_num

private theorem integral_norm_sq_halfMellinData (f : ℝ → ℂ) (σ : ℝ) :
    ∫ v : ℝ, ‖halfMellinData f ((σ : ℂ) + v * I)‖ ^ 2 =
      (1 / 2 : ℝ) * ∫ t : ℝ, ‖f t‖ ^ 2 := by
  simp only [halfMellinData_line, norm_mul, mul_pow]
  rw [integral_const_mul,
    Measure.integral_comp_mul_left (fun t : ℝ => ‖f t‖ ^ 2) (-1 / 2)]
  norm_num
  ring

private theorem mellinInv_halfMellinData (f : ℝ → ℂ) (y : ℝ) :
    mellinInv (1 / 2) (halfMellinData f) y =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, f t * (y : ℂ) ^ (linePt (2 * t) - 1) := by
  unfold mellinInv
  simp only [halfMellinData_line, smul_eq_mul, Complex.real_smul]
  have heq : (fun v : ℝ => (y : ℂ) ^ (-((1 / 2 : ℝ) + v * I)) *
      ((1 / 2 : ℂ) * f ((-1 / 2 : ℝ) * v))) =
      fun v : ℝ => (1 / 2 : ℂ) *
        (fun t : ℝ => f t * (y : ℂ) ^ (linePt (2 * t) - 1)) ((-1 / 2 : ℝ) * v) := by
    funext v
    have he : -((1 / 2 : ℝ) + (v : ℂ) * I) = linePt (2 * ((-1 / 2 : ℝ) * v)) - 1 := by
      simp only [linePt]; push_cast; ring
    rw [he]
    ring
  rw [heq, integral_const_mul,
    Measure.integral_comp_mul_left (fun t : ℝ => f t * (y : ℂ) ^ (linePt (2 * t) - 1)) (-1 / 2)]
  norm_num [Complex.real_smul]
  ring


private theorem memLp_boundary_source {g : ℝ → ℂ} (hg : Integrable g) (hg2 : MemLp g 2)
    {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    MemLp (fun t : ℝ => g t * boundaryPairKernel (2 * t) z) 2 := by
  refine hg2.of_le_mul (integrable_closedDefectLaplace_integrand hg hz hz0).aestronglyMeasurable
    (c := 3 * ‖z‖ ^ (-(1 / 2 : ℝ))) ?_
  filter_upwards with t
  rw [norm_mul, mul_comm (3 * _) ‖g t‖]
  exact mul_le_mul_of_nonneg_left (norm_boundaryPairKernel_le (2 * t) hz hz0) (norm_nonneg _)

private theorem closedDefectLaplace_ray_eq (g : ℝ → ℂ) {z : ℂ} (hz0 : z ≠ 0)
    {y : ℝ} (hy : 0 < y) :
    closedDefectLaplace g ((y : ℂ) * z) =
      mellinInv (1 / 2) (halfMellinData (fun t => g t * boundaryPairKernel (2 * t) z)) y := by
  rw [mellinInv_halfMellinData, closedDefectLaplace]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [boundaryPairKernel_mul_pos (2 * t) hy hz0]
  ring

/-- Mellin–Plancherel computes the energy on every ray in the closed right half-plane. -/
theorem closedDefectLaplace_ray_energy {g : ℝ → ℂ} (hg : Integrable g) (hg2 : MemLp g 2)
    {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    IntegrableOn (fun y : ℝ => ‖closedDefectLaplace g ((y : ℂ) * z)‖ ^ 2) (Ioi 0) ∧
    (∫ y : ℝ in Ioi 0, ‖closedDefectLaplace g ((y : ℂ) * z)‖ ^ 2) =
      1 / (4 * Real.pi) * ∫ t : ℝ, ‖g t‖ ^ 2 * ‖boundaryPairKernel (2 * t) z‖ ^ 2 := by
  let f : ℝ → ℂ := fun t => g t * boundaryPairKernel (2 * t) z
  have hf : Integrable f := integrable_closedDefectLaplace_integrand hg hz hz0
  have hf2 : MemLp f 2 := memLp_boundary_source hg hg2 hz hz0
  have hdi := integrable_halfMellinData (σ := 1 / 2) hf
  have hd2 := memLp_halfMellinData (σ := 1 / 2) hf hf2
  have heq : EqOn (fun y : ℝ => ‖closedDefectLaplace g ((y : ℂ) * z)‖ ^ 2)
      (fun y => ‖mellinInv (1 / 2) (halfMellinData f) y‖ ^ 2 * y ^ (2 * (1 / 2 : ℝ) - 1))
      (Ioi 0) := by
    intro y hy
    dsimp only
    rw [closedDefectLaplace_ray_eq g hz0 hy]
    norm_num [f]
  refine ⟨(integrableOn_norm_sq_mellinInv hdi hd2).congr_fun (fun y hy => (heq hy).symm)
    measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => heq hy),
    integral_norm_sq_mellinInv hdi hd2, integral_norm_sq_halfMellinData]
  simp only [f, norm_mul, mul_pow]
  ring

/-- An integrable finite-energy defect has a square-integrable imaginary boundary. -/
theorem memLp_defectBoundary {g : ℝ → ℂ} (hg : Integrable g) (hg2 : MemLp g 2) :
    MemLp (defectBoundary g) 2 := by
  have hp := closedDefectLaplace_ray_energy hg hg2 (z := I) (by simp) I_ne_zero
  have hm := closedDefectLaplace_ray_energy hg hg2 (z := -I) (by simp) (neg_ne_zero.mpr I_ne_zero)
  have hip : IntegrableOn (fun y => ‖defectBoundary g y‖ ^ 2) (Ioi 0) := hp.1
  have him : IntegrableOn (fun y => ‖defectBoundary g y‖ ^ 2) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, neg_preimage, neg_Iic, neg_zero]
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    simpa only [defectBoundary, Complex.ofReal_neg, neg_mul, mul_neg] using hm.1
  apply (memLp_two_iff_integrable_sq_norm (measurable_defectBoundary hg).aestronglyMeasurable).mpr
  simpa only [Ioi_union_Iic, integrableOn_univ] using hip.union him

/-- Both imaginary boundary rays together preserve the complete defect energy. -/
theorem integral_norm_sq_defectBoundary {g : ℝ → ℂ} (hg : Integrable g) (hg2 : MemLp g 2) :
    (∫ y : ℝ, ‖defectBoundary g y‖ ^ 2) =
      Real.pi⁻¹ * ∫ t : ℝ, ‖g t‖ ^ 2 := by
  have hp := closedDefectLaplace_ray_energy hg hg2 (z := I) (by simp) I_ne_zero
  have hm := closedDefectLaplace_ray_energy hg hg2 (z := -I) (by simp) (neg_ne_zero.mpr I_ne_zero)
  have hi : Integrable (fun y => ‖defectBoundary g y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (measurable_defectBoundary hg).aestronglyMeasurable).mp
      (memLp_defectBoundary hg hg2)
  have hsum : (∫ y : ℝ, ‖defectBoundary g y‖ ^ 2) =
      (∫ y : ℝ in Ioi 0, ‖closedDefectLaplace g ((y : ℂ) * I)‖ ^ 2) +
      ∫ y : ℝ in Ioi 0, ‖closedDefectLaplace g ((y : ℂ) * (-I))‖ ^ 2 := by
    rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hi, compl_Ioi]
    congr 1
    have h := integral_comp_neg_Ioi 0 (fun y : ℝ => ‖defectBoundary g y‖ ^ 2)
    simpa only [neg_zero, defectBoundary, Complex.ofReal_neg, neg_mul, mul_neg] using h.symm
  have hsi := (memLp_two_iff_integrable_sq_norm
    (integrable_closedDefectLaplace_integrand hg (by simp : 0 ≤ I.re) I_ne_zero).aestronglyMeasurable
      ).mp (memLp_boundary_source hg hg2 (by simp : 0 ≤ I.re) I_ne_zero)
  have hsmi := (memLp_two_iff_integrable_sq_norm
    (integrable_closedDefectLaplace_integrand hg (by simp : 0 ≤ (-I).re)
      (neg_ne_zero.mpr I_ne_zero)).aestronglyMeasurable).mp
        (memLp_boundary_source hg hg2 (by simp : 0 ≤ (-I).re) (neg_ne_zero.mpr I_ne_zero))
  simp only [norm_mul, mul_pow] at hsi hsmi
  rw [hsum, hp.2, hm.2, ← mul_add, ← integral_add hsi hsmi]
  have hpt : (fun t : ℝ => ‖g t‖ ^ 2 * ‖boundaryPairKernel (2 * t) I‖ ^ 2 +
      ‖g t‖ ^ 2 * ‖boundaryPairKernel (2 * t) (-I)‖ ^ 2) =
      fun t : ℝ => ‖g t‖ ^ 2 * 4 := by
    funext t
    rw [← mul_add, boundaryPairKernel_paired_norm_sq]
  rw [hpt, integral_mul_const]
  ring

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.closedDefectLaplace_ray_energy
#print axioms GaloisForLFunctions.EulerFETransportTheory.memLp_defectBoundary
#print axioms GaloisForLFunctions.EulerFETransportTheory.integral_norm_sq_defectBoundary
