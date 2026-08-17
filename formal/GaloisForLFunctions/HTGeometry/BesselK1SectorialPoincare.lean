import GaloisForLFunctions.HTGeometry.BesselK1RayCoefficients

/-!
# The sectorial remainder in the corpus's Poincaré normalization

The ray expansion carries the factor `(2z)^{-1/2}` and powers of `(2z)^{-1}`; the corpus's Poincaré
form carries `(π/z)^{1/2}` and powers of `z^{-1}`.  On the right half plane a positive real factor
splits out of a principal power, so the two normalizations differ exactly by the rescaling of the
coefficients already computed.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section CpowSplit

theorem ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) (s : ℂ) :
    (((r : ℝ) : ℂ) * x) ^ s = ((r : ℝ) : ℂ) ^ s * x ^ s := by
  have hrne : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hmul : (((r : ℝ) : ℂ) * x) ≠ 0 := mul_ne_zero hrne hx
  rw [Complex.cpow_def_of_ne_zero hmul, Complex.cpow_def_of_ne_zero hrne,
    Complex.cpow_def_of_ne_zero hx, Complex.log_ofReal_mul hr hx, ← Complex.exp_add,
    Complex.ofReal_log hr.le]
  congr 1
  ring

theorem arg_ne_pi_of_re_pos {w : ℂ} (hw : 0 < w.re) : w.arg ≠ Real.pi := by
  intro h
  rw [Complex.arg_eq_pi_iff] at h
  linarith [h.1]

theorem two_mul_cpow_half {w : ℂ} (hw : 0 < w.re) :
    ((2 : ℂ) * w) ^ (((1 : ℝ) / 2 : ℝ) : ℂ)
      = ((Real.sqrt 2 : ℝ) : ℂ) * w ^ (((1 : ℝ) / 2 : ℝ) : ℂ) := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have h2 : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by norm_num
  rw [h2, ofReal_mul_cpow (by norm_num) hwne]
  congr 1
  rw [← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow]

theorem pi_div_cpow_half {w : ℂ} (hw : 0 < w.re) :
    ((Real.pi : ℂ) / w) ^ ((1 : ℂ) / 2)
      = ((Real.sqrt Real.pi : ℝ) : ℂ) * (w ^ (((1 : ℝ) / 2 : ℝ) : ℂ))⁻¹ := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hinvne : w⁻¹ ≠ 0 := inv_ne_zero hwne
  have hcast : ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hdiv : ((Real.pi : ℂ) / w) = ((Real.pi : ℝ) : ℂ) * w⁻¹ := by
    rw [div_eq_mul_inv]
  rw [hdiv, hcast, ofReal_mul_cpow Real.pi_pos hinvne,
    Complex.inv_cpow w _ (arg_ne_pi_of_re_pos hw)]
  congr 1
  rw [← Complex.ofReal_cpow Real.pi_pos.le, Real.sqrt_eq_rpow]

end CpowSplit

section Bridge

theorem raySum_eq_poincare {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    ((((2 : ℂ) * w) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))⁻¹
        * ∑ k ∈ Finset.range n, ((rayCoeff k : ℝ) : ℂ) * (((2 : ℂ) * w)⁻¹) ^ k)
      = ((Real.pi : ℂ) / w) ^ ((1 : ℂ) / 2)
        * ∑ k ∈ Finset.range n, ((besselK1Coeff k : ℝ) : ℂ) * (w⁻¹) ^ k := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast ne_of_gt this
  have hterms : ∀ k ∈ Finset.range n,
      ((rayCoeff k : ℝ) : ℂ) * (((2 : ℂ) * w)⁻¹) ^ k
      = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ))
        * (((besselK1Coeff k : ℝ) : ℂ) * (w⁻¹) ^ k) := by
    intro k _
    rw [rayCoeff_eq k, mul_inv, mul_pow]
    push_cast
    have h2k : ((2 : ℂ) ^ k) * ((2 : ℂ)⁻¹ ^ k) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (two_ne_zero), one_pow]
    calc ((Real.sqrt 2 : ℝ) : ℂ) * (2 : ℂ) ^ k * ((Real.sqrt Real.pi : ℝ) : ℂ)
          * ((besselK1Coeff k : ℝ) : ℂ) * ((2 : ℂ)⁻¹ ^ k * (w⁻¹) ^ k)
        = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ))
          * (((besselK1Coeff k : ℝ) : ℂ) * (w⁻¹) ^ k)
          * (((2 : ℂ) ^ k) * ((2 : ℂ)⁻¹ ^ k)) := by ring
      _ = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ))
          * (((besselK1Coeff k : ℝ) : ℂ) * (w⁻¹) ^ k) := by rw [h2k, mul_one]
  rw [Finset.sum_congr rfl hterms, ← Finset.mul_sum, two_mul_cpow_half hw, pi_div_cpow_half hw,
    mul_inv]
  have hcp : w ^ (((1 : ℝ) / 2 : ℝ) : ℂ) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr ?_
    exact Or.inl hwne
  field_simp

/-- **The all-orders Schläfli asymptotic with a modulus remainder, in Poincaré normalization.** -/
theorem norm_besselK1C_sub_poincare_le_norm (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ‖_root_.HTGeometry.besselK1C w
        - Complex.exp (-w) * (((Real.pi : ℂ) / w) ^ ((1 : ℂ) / 2)
          * ∑ k ∈ Finset.range (m + 1), ((besselK1Coeff k : ℝ) : ℂ) * (w⁻¹) ^ k)‖
      ≤ Real.exp (-w.re) * ((2 * ‖w‖) ^ ((1 : ℝ) / 2))⁻¹
        * (rayRemConst (m + 1) / (2 * ‖w‖) ^ (m + 1)) := by
  rw [← raySum_eq_poincare hw (m + 1)]
  exact norm_besselK1C_sub_raySum_le m hw

end Bridge

end

end GaloisForLFunctions.HTGeometry
