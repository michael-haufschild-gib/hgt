import GaloisForLFunctions.SelbergClass.PositiveEpsteinCoefficients
import GaloisForLFunctions.SelbergClass.PositiveEpsteinGrowth
import GaloisForLFunctions.LatticeSectionTheory.DefiniteCountsHaveOffLineZeros
import GaloisForLFunctions.RHTower.ReciprocalGammaExactOrderOne
import GaloisForLFunctions.HTGeometry.OrderOneEnvelopeRootDivision
import GaloisForLFunctions.HTGeometry.OrderOneEntireQuotient
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# A positive Epstein series and its scalar completion

The form `m² + 64n²` has determinant `64`. Scaling its completed Epstein
function by `8ˢ/2` balances the dual lattice and normalizes the first ordinary
Dirichlet coefficient to one. Clearing the two poles gives an entire numerator.
-/

noncomputable section

open Complex Filter Topology Set
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.PositiveEpstein

/-- The normalized completion of the positive rectangular Epstein series. -/
def completed (s : ℂ) : ℂ :=
  (8 : ℂ) ^ s / 2 * epsteinLambda 8 (by norm_num) s

/-- The entire numerator obtained by clearing the completion's poles at zero and one. -/
def numerator (s : ℂ) : ℂ :=
  (8 : ℂ) ^ s / 2 *
    (s * (s - 1) * (rectFEPair 8 (by norm_num)).Λ₀ s - (s - 1) + s / 8)

theorem analytic_numerator : AnalyticOnNhd ℂ numerator univ := by
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  have hpow : Differentiable ℂ (fun s : ℂ => (8 : ℂ) ^ s) :=
    differentiable_id.const_cpow (.inl (by norm_num))
  have hΛ := (rectFEPair 8 (by norm_num)).differentiable_Λ₀
  unfold numerator
  fun_prop

private theorem epstein_eight_eq (s : ℂ) :
    epsteinLambda 8 (by norm_num) s =
      (rectFEPair 8 (by norm_num)).Λ₀ s - 1 / s - (1 / 8) / (1 - s) := by
  unfold epsteinLambda WeakFEPair.Λ
  simp only [rectFEPair, smul_eq_mul, mul_one, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]

theorem numerator_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    numerator s = s * (s - 1) * completed s := by
  rw [numerator, completed, epstein_eight_eq]
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1s]
  <;> ring

@[simp] theorem numerator_zero : numerator 0 = 1 / 2 := by
  norm_num [numerator]

@[simp] theorem numerator_one : numerator 1 = 1 / 2 := by
  norm_num [numerator]

theorem orderOneEnvelope_numerator : OrderOneEnvelope numerator := by
  have hpow : OrderOneEnvelope (fun s : ℂ => (8 : ℂ) ^ s) := by
    refine ((orderOneEnvelope_natCast_cpow_neg (n := 8) (by norm_num)).comp_affine
      (-1) 0).congr fun s => ?_
    simp only [mul_neg_one, neg_mul, one_mul, add_zero, neg_neg]
  have hpoly : OrderOneEnvelope (fun s : ℂ => s * (s - 1)) := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_one] using
      orderOneEnvelope_polynomial (Polynomial.X * (Polynomial.X - 1) : Polynomial ℂ)
  have hcorrection : OrderOneEnvelope (fun s : ℂ => -(s - 1) + s / 8) := by
    simpa only [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      div_eq_mul_inv] using
      orderOneEnvelope_polynomial (-(Polynomial.X - 1) + Polynomial.X *
        Polynomial.C (8⁻¹ : ℂ))
  refine ((hpow.const_mul (1 / 2)).mul
    ((hpoly.mul (orderOneEnvelope_epsteinLambda_zero (by norm_num : (0 : ℝ) < 8))).add
      hcorrection)).congr fun s => ?_
  unfold numerator
  ring

/-- Entire regularization of the ordinary Dirichlet series at its possible pole. -/
def regularized (s : ℂ) : ℂ :=
  ((Real.pi / 8 : ℝ) : ℂ) ^ s * reciprocalGammaEntire (s + 1) * numerator s

theorem analytic_regularized : AnalyticOnNhd ℂ regularized univ := by
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  have hbase : ((Real.pi / 8 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 8)).ne'
  have hpow : Differentiable ℂ (fun s : ℂ => ((Real.pi / 8 : ℝ) : ℂ) ^ s) :=
    differentiable_id.const_cpow (.inl hbase)
  have hΓ : Differentiable ℂ reciprocalGammaEntire := Complex.differentiable_one_div_Gamma
  have hR := Complex.analyticOnNhd_univ_iff_differentiable.mp analytic_numerator
  unfold regularized
  fun_prop

theorem orderOneEnvelope_regularized : OrderOneEnvelope regularized := by
  have hbase : ((Real.pi / 8 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 8)).ne'
  have hpow : OrderOneEnvelope (fun s : ℂ => ((Real.pi / 8 : ℝ) : ℂ) ^ s) :=
    (orderOneEnvelope_exp_mul (Complex.log ((Real.pi / 8 : ℝ) : ℂ))).congr
      fun s => (Complex.cpow_def_of_ne_zero hbase _).symm
  exact (hpow.mul (RHTower.orderOneEnvelope_reciprocalGammaEntire.comp_affine 1 1 |>.congr
    fun s => by simp only [one_mul])).mul orderOneEnvelope_numerator

/-- The completion has a real zero strictly between the critical line and its pole. -/
theorem completed_has_offLine_zero :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ completed σ = 0 := by
  obtain ⟨σ, hσ, hσ1, hz⟩ := epsteinLambda_eight_has_offLine_zero
  exact ⟨σ, hσ, hσ1, by rw [completed, hz, mul_zero]⟩

end GaloisForLFunctions.SelbergClass.PositiveEpstein
