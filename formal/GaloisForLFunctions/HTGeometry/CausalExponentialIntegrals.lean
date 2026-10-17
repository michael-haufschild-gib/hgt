import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Exponential masses on the two sides of a causal boundary -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

theorem lintegral_causal_exponential {c : ℝ} (hc : 0 < c) (a : ℝ) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (Real.exp (-(c * (t - a))))) =
      ENNReal.ofReal (1 / c) := by
  have he : (fun t : ℝ => Real.exp (-(c * (t - a)))) =
      fun t => Real.exp (c * a) * Real.exp (-c * t) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(c * (t - a)))) (Ioi a) := by
    rw [he]
    exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) a).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun t => (Real.exp_pos _).le),
    he, integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hc) a]
  congr 1
  calc Real.exp (c * a) * (-Real.exp (-c * a) / -c) =
      (Real.exp (c * a) * Real.exp (-(c * a))) / c := by
        rw [neg_mul, neg_div_neg_eq, mul_div_assoc]
    _ = 1 / c := by rw [← Real.exp_add]; simp

theorem lintegral_anticausal_exponential {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (∫⁻ a in Iic t, ENNReal.ofReal (Real.exp (-(c * (t - a))))) =
      ENNReal.ofReal (1 / c) := by
  have he : (fun a : ℝ => Real.exp (-(c * (t - a)))) =
      fun a => Real.exp (-(c * t)) * Real.exp (c * a) := by
    funext a
    rw [← Real.exp_add]
    congr 1
    ring
  have hi : IntegrableOn (fun a : ℝ => Real.exp (-(c * (t - a)))) (Iic t) := by
    rw [he]
    exact (integrableOn_exp_mul_Iic hc t).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun a => (Real.exp_pos _).le),
    he, integral_const_mul, integral_exp_mul_Iic hc t]
  congr 1
  calc Real.exp (-(c * t)) * (Real.exp (c * t) / c) =
      (Real.exp (-(c * t)) * Real.exp (c * t)) / c := by ring
    _ = 1 / c := by rw [← Real.exp_add]; simp

end GaloisForLFunctions.HTGeometry
