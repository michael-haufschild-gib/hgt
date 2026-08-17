import GaloisForLFunctions.HTGeometry.JetSchwarzian
import GaloisForLFunctions.HTGeometry.QuadOneAffineTransport
import GaloisForLFunctions.HTGeometry.QuadTwoAffineTransport

/-!
# No rational projective structure for the two quadratic maps

The Schwarzian of either postcritically finite quadratic is `−3/(2·(z − crit)^2)`, a double pole
exactly at the critical point.  A rational projective structure would satisfy

`a(R)·(R')² = a − S_R` ,

an affine transport with unit coefficient whose inhomogeneous term is polar of order two at the
critical point, and the critical-order obstruction forbids it.

This is the bottom of the weight-zero tower: the Schwarzian coordinate translates by `S_R` under the
substitution, so a jet-level invariant built over it can only close if the translation can be undone
by a rational function — which is exactly a projective structure.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## `z ↦ z² + 1` -/

theorem quadOne_no_projective_structure (a : RatFunc ℂ) :
    ¬ (ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_not_isConst a
        * ratFuncDeriv (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne) ^ 2
      = a - ratFuncSchwarzian (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)) := by
  intro hα
  set R₀ : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne with hR₀def
  have hd1 : ratFuncDeriv R₀
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne) :=
    ratFuncDeriv_algebraMap quadOne
  have hd2 : ratFuncDeriv (ratFuncDeriv R₀)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) := by
    rw [hd1, ratFuncDeriv_algebraMap, derivative_quadOne, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, mul_one, zero_add]
  have hd3 : ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R₀)) = 0 := by
    rw [hd2, ratFuncDeriv_algebraMap, Polynomial.derivative_C, map_zero]
  set b : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)
    with hbdef
  have hb : b ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero
      (derivative_ne_zero_of_natDegree_ne_zero quadOne_natDegree_ne_zero)
  have hAm2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 := by
    refine algebraMap_ne_zero_of_ne_zero ?_
    intro hh
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 0) hh
    simp at hc
  have hC32 : (RatFunc.C (3 / 2 : ℂ) : RatFunc ℂ) ≠ 0 := by
    intro hh
    have h32 : (3 / 2 : ℂ) = 0 := (RatFunc.C_injective (K := ℂ)) (by simp [hh])
    norm_num at h32
  set c : RatFunc ℂ := RatFunc.C (3 / 2 : ℂ)
      * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) / b) ^ 2 with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero hC32 (pow_ne_zero 2 (div_ne_zero hAm2 hb))
  have hSval : ratFuncSchwarzian R₀ = -c := by
    rw [ratFuncSchwarzian, hd3, hd2, hd1, hcdef, zero_div, zero_sub]
  have hmultC : ∀ z : ℂ, Polynomial.rootMultiplicity z (Polynomial.C (2 : ℂ)) = 0 := by
    intro z
    refine Polynomial.rootMultiplicity_eq_zero ?_
    rw [Polynomial.IsRoot.def, Polynomial.eval_C]
    norm_num
  have hcord : ∀ p : ℂ, ratOrder c p
      = -(2 * (Polynomial.rootMultiplicity p (Polynomial.derivative quadOne) : ℤ)) := by
    intro p
    rw [hcdef, ratOrder_mul hC32 (pow_ne_zero 2 (div_ne_zero hAm2 hb)), ratOrder_C,
      ratOrder_pow (div_ne_zero hAm2 hb), div_eq_mul_inv,
      ratOrder_mul hAm2 (inv_ne_zero hb), ratOrder_inv hb, ratOrder_algebraMap,
      hbdef, ratOrder_algebraMap, hmultC p]
    push_cast
    ring
  have hIAT : IsAffineTransport quadOne quadOne_not_isConst 2 1 c a := by
    show ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_not_isConst a
        * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)) ^ (2 : ℤ)
      = 1 * a + c
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← hbdef, ← hd1]
    rw [hSval] at hα
    linear_combination hα
  have ha0 : a ≠ 0 := by
    intro hh
    have hz : ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_not_isConst a
        * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)) ^ (2 : ℤ)
      = 1 * a + c := hIAT
    rw [hh, map_zero, zero_mul, mul_zero, zero_add] at hz
    exact hc0 hz.symm
  refine quadOne_no_affineTransport_of_critical_order ha0 one_ne_zero hc0 hIAT
    (fun p _ => ratOrder_one p) (fun p hp => ?_) ?_ ?_
  · rw [hcord p, Polynomial.rootMultiplicity_eq_zero ?_]
    · norm_num
    rw [Polynomial.IsRoot.def, derivative_quadOne_eval]
    exact mul_ne_zero (by norm_num) hp
  · rw [hcord, rootMultiplicity_derivative_quadOne, ratOrder_one]
    norm_num
  · rw [hcord, rootMultiplicity_derivative_quadOne]
    norm_num

/-! ## `z ↦ (z − 1)²` -/

theorem quadTwo_no_projective_structure (a : RatFunc ℂ) :
    ¬ (ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
        quadTwo_not_isConst a
        * ratFuncDeriv (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo) ^ 2
      = a - ratFuncSchwarzian (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)) := by
  intro hα
  set R₀ : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo with hR₀def
  have hd1 : ratFuncDeriv R₀
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo) :=
    ratFuncDeriv_algebraMap quadTwo
  have hd2 : ratFuncDeriv (ratFuncDeriv R₀)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) := by
    rw [hd1, ratFuncDeriv_algebraMap, derivative_quadTwo, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, zero_mul, mul_one, zero_add]
  have hd3 : ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R₀)) = 0 := by
    rw [hd2, ratFuncDeriv_algebraMap, Polynomial.derivative_C, map_zero]
  set b : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)
    with hbdef
  have hb : b ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero
      (derivative_ne_zero_of_natDegree_ne_zero quadTwo_natDegree_ne_zero)
  have hAm2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 := by
    refine algebraMap_ne_zero_of_ne_zero ?_
    intro hh
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 0) hh
    simp at hc
  have hC32 : (RatFunc.C (3 / 2 : ℂ) : RatFunc ℂ) ≠ 0 := by
    intro hh
    have h32 : (3 / 2 : ℂ) = 0 := (RatFunc.C_injective (K := ℂ)) (by simp [hh])
    norm_num at h32
  set c : RatFunc ℂ := RatFunc.C (3 / 2 : ℂ)
      * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) / b) ^ 2 with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero hC32 (pow_ne_zero 2 (div_ne_zero hAm2 hb))
  have hSval : ratFuncSchwarzian R₀ = -c := by
    rw [ratFuncSchwarzian, hd3, hd2, hd1, hcdef, zero_div, zero_sub]
  have hmultC : ∀ z : ℂ, Polynomial.rootMultiplicity z (Polynomial.C (2 : ℂ)) = 0 := by
    intro z
    refine Polynomial.rootMultiplicity_eq_zero ?_
    rw [Polynomial.IsRoot.def, Polynomial.eval_C]
    norm_num
  have hcord : ∀ p : ℂ, ratOrder c p
      = -(2 * (Polynomial.rootMultiplicity p (Polynomial.derivative quadTwo) : ℤ)) := by
    intro p
    rw [hcdef, ratOrder_mul hC32 (pow_ne_zero 2 (div_ne_zero hAm2 hb)), ratOrder_C,
      ratOrder_pow (div_ne_zero hAm2 hb), div_eq_mul_inv,
      ratOrder_mul hAm2 (inv_ne_zero hb), ratOrder_inv hb, ratOrder_algebraMap,
      hbdef, ratOrder_algebraMap, hmultC p]
    push_cast
    ring
  have hIAT : IsAffineTransport quadTwo quadTwo_not_isConst 2 1 c a := by
    show ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
        quadTwo_not_isConst a
        * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)) ^ (2 : ℤ)
      = 1 * a + c
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← hbdef, ← hd1]
    rw [hSval] at hα
    linear_combination hα
  have ha0 : a ≠ 0 := by
    intro hh
    have hz : ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
        quadTwo_not_isConst a
        * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)) ^ (2 : ℤ)
      = 1 * a + c := hIAT
    rw [hh, map_zero, zero_mul, mul_zero, zero_add] at hz
    exact hc0 hz.symm
  refine quadTwo_no_affineTransport_of_critical_order ha0 one_ne_zero hc0 hIAT
    (fun p _ => ratOrder_one p) (fun p hp => ?_) ?_ ?_
  · rw [hcord p, Polynomial.rootMultiplicity_eq_zero ?_]
    · norm_num
    rw [Polynomial.IsRoot.def, derivative_quadTwo_eval]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hp)
  · rw [hcord, rootMultiplicity_derivative_quadTwo, ratOrder_one]
    norm_num
  · rw [hcord, rootMultiplicity_derivative_quadTwo]
    norm_num

end

end GaloisForLFunctions.HTGeometry
