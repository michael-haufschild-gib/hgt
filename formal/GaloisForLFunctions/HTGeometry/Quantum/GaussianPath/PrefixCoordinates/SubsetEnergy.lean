import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Squared-mass tails on selected independent Gaussian couplings -/

open MeasureTheory ProbabilityTheory Real Finset Set
namespace GaloisForLFunctions.HTGeometry.GaussianCoordinates
noncomputable section

/-- The quarter-square exponential moment of one standard normal. -/
theorem standard_quarter_square :
    (∫ x : ℝ, exp (x^2/4) ∂gaussianReal 0 1)=sqrt 2 := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,integral_withDensity_eq_integral_toReal_smul
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have h (x : ℝ) : (gaussianPDF 0 1 x).toReal • exp (x^2/4)=
      (sqrt (2*π))⁻¹*exp (-(1/4)*x^2) := by
    simp only [toReal_gaussianPDF,smul_eq_mul,gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  simp_rw [h]
  rw [integral_const_mul,integral_gaussian,inv_mul_eq_div,←sqrt_div (by positivity)]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

/-- A deterministic set of m Gaussian couplings pays only m one-dimensional
moments in the upper tail of its squared mass. -/
theorem gaussian_seam_square_tail {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (R : ℝ) :
    let μ := Measure.pi fun _ : I => gaussianReal 0 1
    exp (R/4)*μ.real {x : I→ℝ | R≤∑ i ∈ S, (x i)^2} ≤ (sqrt 2)^S.card := by
  classical
  intro μ
  let f (i : I) (z : ℝ) := if i∈S then exp (z^2/4) else 1
  let E := {x : I→ℝ | R≤∑ i ∈ S, (x i)^2}
  have hE : MeasurableSet E := measurableSet_le measurable_const (by fun_prop)
  have hI : Integrable (fun z : ℝ => exp (z^2/4)) (gaussianReal 0 1) := by
    by_contra hn
    exact (sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne' (standard_quarter_square.symm.trans (integral_undef hn))
  have hi (i : I) : Integrable (f i) (gaussianReal 0 1) := by
    by_cases h : i∈S
    · simpa only [f,if_pos h] using hI
    · simpa only [f,if_neg h] using (integrable_const (μ:=gaussianReal 0 1) (1:ℝ))
  have hp (x : I→ℝ) : (∏ i, f i (x i))=exp ((∑ i ∈ S, (x i)^2)/4) := by
    dsimp only [f]
    rw [←prod_filter,←Real.exp_sum,←sum_div]
    simp
  have hx (x : I→ℝ) : E.indicator (fun _ => exp (R/4)) x≤∏ i, f i (x i) := by
    rw [hp]
    by_cases he : x∈E
    · rw [Set.indicator_of_mem he]
      exact exp_le_exp.mpr (div_le_div_of_nonneg_right he (by norm_num))
    · rw [Set.indicator_of_notMem he]
      exact (exp_pos _).le
  have hm := integral_mono ((integrable_const (μ:=μ) (exp (R/4))).indicator hE)
    (Integrable.fintype_prod hi) hx
  have hj (i : I) : (∫ z, f i z ∂gaussianReal 0 1)=if i∈S then sqrt 2 else 1 := by
    by_cases h : i∈S
    · simpa only [f,if_pos h] using standard_quarter_square
    · simp [f,h]
  rw [integral_indicator_const _ hE,integral_fintype_prod_eq_prod] at hm
  simp_rw [hj] at hm
  rw [←prod_filter] at hm
  simpa only [E,Finset.filter_mem_eq_inter,Finset.univ_inter,prod_const,Measure.real,smul_eq_mul,
    mul_comm (exp (R/4))] using hm

#print axioms gaussian_seam_square_tail
end
end GaloisForLFunctions.HTGeometry.GaussianCoordinates
