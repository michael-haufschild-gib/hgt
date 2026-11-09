import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialElapsedDepthActionHasItsDerivative

/-!
# Sharp elapsed-heat credit

The isolated quadratic pair follows `X²+c ↦ X²+c−2t`. Until its collision,
every elapsed-depth power equals its initial value. A larger coefficient
than `2` already fails for `X²+1` at time `1/4`.
-/

open Polynomial Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- Backward heat subtracts exactly twice elapsed time from the constant term. -/
theorem polyHeat_quadratic (t c : ℝ) :
    polyHeat t (X ^ 2 + C c) = X ^ 2 + C (c - 2 * t) := by
  have h1 (s : ℝ) : forwardPolyHeat s 1 = 1 := by
    simpa only [C_1] using forwardPolyHeat_C s 1
  have hX (s : ℝ) : forwardPolyHeat s X = X := by
    simpa only [mul_one, h1, derivative_one, mul_zero, add_zero] using
      forwardPolyHeat_X_mul s (1 : ℝ[X])
  have hsq (s : ℝ) : forwardPolyHeat s (X ^ 2) = X ^ 2 + C (2 * s) := by
    simpa only [pow_two, hX, derivative_X, mul_one] using forwardPolyHeat_X_mul s X
  rw [← neg_neg t, ← forwardPolyHeat_eq_polyHeat, forwardPolyHeat_add,
    hsq, forwardPolyHeat_C, add_assoc, ← C_add]
  congr 2
  ring

/-- A positive quadratic has one upper root, with squared depth `c`. -/
theorem upperRoots_quadratic {c : ℝ} (hc : 0 < c) :
    RiemannGaussian.realPolynomialUpperRootMultiset (X ^ 2 + C c) =
      {(Real.sqrt c : ℂ) * I} := by
  let w : ℂ := (Real.sqrt c : ℂ) * I
  have hw : w ^ 2 = -(c : ℂ) := by
    rw [show w ^ 2 = (Real.sqrt c : ℂ) ^ 2 * I ^ 2 by dsimp [w]; ring,
      I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hc.le]
    ring
  have hfac : (X ^ 2 + C (c : ℂ) : ℂ[X]) = (X - C w) * (X - C (-w)) := by
    calc
      _ = X ^ 2 - C (w ^ 2) := by rw [hw, map_neg]; ring
      _ = _ := by rw [map_pow, map_neg]; ring
  have hr : ((X ^ 2 + C c : ℝ[X]).map ofRealHom).roots = {w} + {-w} := by
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      show ofRealHom c = (c : ℂ) from rfl, hfac,
      roots_mul (mul_ne_zero (monic_X_sub_C w).ne_zero (monic_X_sub_C (-w)).ne_zero),
      roots_X_sub_C, roots_X_sub_C]
  have hi : 0 < w.im := by
    simpa only [w, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero] using Real.sqrt_pos.mpr hc
  unfold RiemannGaussian.realPolynomialUpperRootMultiset
  rw [hr]
  simp only [Multiset.filter_add, Multiset.filter_singleton, hi, if_true,
    Complex.neg_im, not_lt.mpr (neg_nonpos.mpr hi.le), if_false, w]
  simp

/-- Every elapsed-depth power is conserved by an isolated pair until collision. -/
theorem quadratic_upper_elapsed_moment_eq {c t : ℝ} (ht : 0 < c - 2 * t) (q : ℝ) :
    ((RiemannGaussian.realPolynomialUpperRootMultiset
      (polyHeat t (X ^ 2 + C c))).map (fun z => (z.im ^ 2 + 2 * t) ^ q)).sum = c ^ q := by
  rw [polyHeat_quadratic, upperRoots_quadratic ht]
  simp only [Multiset.map_singleton, Multiset.sum_singleton,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
    Real.sq_sqrt ht.le, sub_add_cancel]

/-- Every proposed elapsed coefficient above `2` violates the first-moment budget. -/
theorem elapsed_heat_coefficient_is_sharp {k : ℝ} (hk : 2 < k) :
    ∃ p : ℝ[X], p ≠ 0 ∧ ∃ t : ℝ, 0 < t ∧
      ((RiemannGaussian.realPolynomialUpperRootMultiset p).map
        (fun z => z.im ^ 2)).sum <
      ((RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map
        (fun z => z.im ^ 2 + k * t)).sum := by
  refine ⟨X ^ 2 + C 1, ?_, 1 / 4, by norm_num, ?_⟩
  · intro hp
    have h := congrArg (Polynomial.eval 0) hp
    norm_num at h
  · rw [upperRoots_quadratic (show (0 : ℝ) < 1 by norm_num), polyHeat_quadratic,
      upperRoots_quadratic (show (0 : ℝ) < 1 - 2 * (1 / 4) by norm_num)]
    simp only [Multiset.map_singleton, Multiset.sum_singleton,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 2 * (1 / 4) by norm_num)]
    linarith only [hk]

#print axioms quadratic_upper_elapsed_moment_eq
#print axioms elapsed_heat_coefficient_is_sharp

end
end GaloisForLFunctions.ArithmeticElectrostatics
