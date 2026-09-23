import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The Gamma integrand in logarithmic coordinates

Substituting `x = e^u` turns the Gamma integral into `∫ e^{iut} e^{σu − e^u} du`.  The integrand is
dominated by `e^{σu}` on the left half line and, since `e^u ≥ (1 + u/2)²`, by a Gaussian with a linear
term on the right half line, so it is integrable for every positive `σ`.

Its derivatives are again combinations of the same shape with `σ` replaced by `σ + k`, so this one
lemma supplies the integrability needed for every order.
-/

open MeasureTheory Filter Set

namespace GaloisForLFunctions

/-- A Gaussian with a linear term is integrable. -/
theorem integrable_exp_neg_quarter_sq_add (c : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-(u ^ (2 : ℕ)) / 4 + c * u)) := by
  have hbase : Integrable (fun u : ℝ => Real.exp (-(1 / 4 : ℝ) * u ^ (2 : ℕ))) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hshift : Integrable (fun u : ℝ => Real.exp (-(1 / 4 : ℝ) * (u - 2 * c) ^ (2 : ℕ))) :=
    hbase.comp_sub_right (2 * c)
  have hconst := hshift.const_mul (Real.exp (c ^ (2 : ℕ)))
  refine hconst.congr ?_
  filter_upwards with u
  rw [← Real.exp_add]
  congr 1
  ring

/-- The exponential integrand of the Gamma integral in logarithmic coordinates is integrable. -/
theorem integrable_expSubExp {a : ℝ} (ha : 0 < a) :
    Integrable (fun u : ℝ => Real.exp (a * u - Real.exp u)) := by
  have hcont : Continuous (fun u : ℝ => Real.exp (a * u - Real.exp u)) := by
    fun_prop
  have hlow : IntegrableOn (fun u : ℝ => Real.exp (a * u - Real.exp u)) (Iic 0) := by
    refine Integrable.mono' (integrableOn_exp_mul_Iic ha 0) hcont.aestronglyMeasurable.restrict ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have := Real.exp_pos u
    linarith
  have hhigh : IntegrableOn (fun u : ℝ => Real.exp (a * u - Real.exp u)) (Ici 0) := by
    refine Integrable.mono' ((integrable_exp_neg_quarter_sq_add (a - 1)).restrict)
      hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
    have hu0 : (0 : ℝ) ≤ u := hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have hhalf : 1 + u / 2 ≤ Real.exp (u / 2) := by
      have := Real.add_one_le_exp (u / 2)
      linarith
    have hsq : (1 + u / 2) ^ (2 : ℕ) ≤ Real.exp u := by
      have hpos : (0 : ℝ) ≤ 1 + u / 2 := by linarith
      calc (1 + u / 2) ^ (2 : ℕ) ≤ Real.exp (u / 2) ^ (2 : ℕ) := by
            exact pow_le_pow_left₀ hpos hhalf 2
        _ = Real.exp u := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    nlinarith [hsq]
  have := hlow.union hhigh
  rw [Iic_union_Ici] at this
  rwa [integrableOn_univ] at this

end GaloisForLFunctions
