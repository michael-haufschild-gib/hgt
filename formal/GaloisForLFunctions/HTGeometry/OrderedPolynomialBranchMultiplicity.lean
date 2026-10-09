import GaloisForLFunctions.HTGeometry.OrderedPolynomialRootContinuation
import Mathlib.FieldTheory.Separable

open Polynomial
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap

/-- Distinct supplied critical positions make the actual derivative separable. -/
theorem separable_derivative_additivePolynomial {n : ℕ} (v : Parameter n)
    (hv : Function.Injective (position v)) : (additivePolynomial v).derivative.Separable := by
  rw [derivative_additivePolynomial]
  apply Separable.unit_mul
  · apply (isUnit_iff_ne_zero.mpr (show (n + 2 : ℂ) ≠ 0 by
      exact_mod_cast (show n + 2 ≠ 0 by omega))).map
  · exact separable_prod_X_sub_C_iff.mpr hv

/-- The polynomial over its j-th critical value has a double root at that critical position. -/
theorem rootMultiplicity_fiberPolynomial_critical {n : ℕ} (v : Parameter n)
    (hv : Function.Injective (position v)) (j : Fin (n + 1)) :
    (fiberPolynomial v (valuesWithConstant v j)).rootMultiplicity (position v j) = 2 := by
  let F := fiberPolynomial v (valuesWithConstant v j)
  change F.rootMultiplicity (position v j) = 2
  have hF : F ≠ 0 := (monic_fiberPolynomial v _).ne_zero
  have hroot : F.IsRoot (position v j) := by
    simp only [IsRoot, F, fiberPolynomial, eval_sub, eval_C, additivePolynomial,
      valuesWithConstant, eval_add, sub_self]
  have hder : F.derivative = (additivePolynomial v).derivative := by
    simp [F, fiberPolynomial]
  have hderroot : F.derivative.IsRoot (position v j) := by
    rw [hder, derivative_additivePolynomial]
    simp only [IsRoot, eval_mul, eval_C, criticalProduct, eval_prod, eval_sub, eval_X]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _), mul_zero]
  have hderne : F.derivative ≠ 0 := by
    rw [hder, derivative_additivePolynomial]
    exact mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast (show n + 2 ≠ 0 by omega)))
      (monic_criticalProduct v).ne_zero
  have hpos := (rootMultiplicity_pos hF).mpr hroot
  have hderpos := (rootMultiplicity_pos hderne).mpr hderroot
  have hsep : F.derivative.Separable := by
    rw [hder]
    exact separable_derivative_additivePolynomial v hv
  have hderle := rootMultiplicity_le_one_of_separable hsep (position v j)
  have hdrop := derivative_rootMultiplicity_of_root hroot
  omega

/-- Every other root over a distinct critical value is regular. -/
theorem derivative_fiberPolynomial_ne_zero_of_ne_critical {n : ℕ} (v : Parameter n)
    (hv : Function.Injective (valuesWithConstant v)) (j : Fin (n + 1)) {z : ℂ}
    (hz : (fiberPolynomial v (valuesWithConstant v j)).IsRoot z)
    (hza : z ≠ position v j) :
    (fiberPolynomial v (valuesWithConstant v j)).derivative.eval z ≠ 0 := by
  intro hzero
  have hcrit : (polynomial v).derivative.IsRoot z := by
    simpa only [IsRoot, fiberPolynomial, derivative_sub, derivative_C, sub_zero,
      derivative_additivePolynomial, derivative_polynomial] using hzero
  obtain ⟨k, hzk⟩ := derivative_root_position v hcrit
  have hval : (additivePolynomial v).eval z = valuesWithConstant v j := by
    simpa only [IsRoot, fiberPolynomial, eval_sub, eval_C, sub_eq_zero] using hz
  have hkj : valuesWithConstant v k = valuesWithConstant v j := by
    rw [hzk] at hval
    simpa only [additivePolynomial, valuesWithConstant, eval_add, eval_C] using hval
  exact hza (hzk.trans (congrArg (position v) (hv hkj)))

/-- A regular critical-value fiber has one double root and every remaining root simple. -/
theorem rootMultiplicity_fiberPolynomial_other {n : ℕ} (v : Parameter n)
    (hv : Function.Injective (valuesWithConstant v)) (j : Fin (n + 1)) {z : ℂ}
    (hz : (fiberPolynomial v (valuesWithConstant v j)).IsRoot z)
    (hza : z ≠ position v j) :
    (fiberPolynomial v (valuesWithConstant v j)).rootMultiplicity z = 1 := by
  have hpos := (rootMultiplicity_pos (monic_fiberPolynomial v _).ne_zero).mpr hz
  have hderzero := rootMultiplicity_eq_zero
    (derivative_fiberPolynomial_ne_zero_of_ne_critical v hv j hz hza)
  have hdrop := derivative_rootMultiplicity_of_root hz
  omega

end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
