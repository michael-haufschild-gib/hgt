import GaloisForLFunctions.HTGeometry.PoincareSeriesCosetDecomposition
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Expanding the coset terms of the Poincaré series in the exponential

For a fixed row `(c, u)` with matrix `M = M_{c,u}`, top-left entry `a` and `d₀ = u.val`, the Möbius
image is `M w = a/c - 1/(c(cw + d₀))`, so with `U_l = c(z + l) + d₀`

  `Σ_l U_l^{-k} e(m M(z+l)) = e(ma/c) Σ_{j ≥ 0} (-2πi m/c)^j/j! · Σ_l U_l^{-(k+j)}`,

the double series being absolutely convergent because `|U_l| ≥ c·Im z`.  The inner sums are then
Lipschitz sums `Σ_l (c(w + l))^{-s}` with `w = z + d₀/c`.
-/

open UpperHalfPlane hiding I
open EisensteinSeries ModularGroup Complex
open scoped MatrixGroups Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (c : ℕ+) (u : (ZMod c)ˣ)

/-! ## The row `(c, u)` and its matrix -/

/-- `d₀ = u.val` as a complex number. -/
def unitVal : ℂ := ((u : ZMod c).val : ℂ)

/-- The top-left entry `a` of `M_{c,u}`; it satisfies `a d₀ - b c = 1`. -/
def unitTop : ℤ := (unitRowMatrix c u) 0 0

theorem unitRowMatrix_apply_one_zero : (unitRowMatrix c u) 1 0 = c := by
  rw [unitRowMatrix, gammaSetMatrix_apply_one_zero, shiftedRow_val_zero]

theorem unitRowMatrix_apply_one_one : (unitRowMatrix c u) 1 1 = ((u : ZMod c).val : ℤ) := by
  rw [unitRowMatrix, gammaSetMatrix_apply_one_one, shiftedRow_val_one]
  simp

theorem unitRowMatrix_det :
    unitTop c u * ((u : ZMod c).val : ℤ) - (unitRowMatrix c u) 0 1 * c = 1 := by
  have := (unitRowMatrix c u).det_coe
  rw [Matrix.det_fin_two, unitRowMatrix_apply_one_zero, unitRowMatrix_apply_one_one] at this
  exact this

theorem c_pos_real : (0 : ℝ) < c := by exact_mod_cast c.pos

theorem c_ne_zero_complex : (c : ℂ) ≠ 0 := by exact_mod_cast c.ne_zero

/-- The imaginary part of `c w + d₀` is `c · Im w`. -/
theorem im_linear (w : ℂ) : ((c : ℂ) * w + unitVal c u).im = c * w.im := by
  simp only [unitVal, Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, add_zero]

theorem linear_ne_zero' (w : ℍ) : (c : ℂ) * (w : ℂ) + unitVal c u ≠ 0 := by
  intro h
  have h1 := im_linear c u (w : ℂ)
  rw [h, Complex.zero_im, UpperHalfPlane.coe_im] at h1
  have : (0 : ℝ) < c * w.im := mul_pos (c_pos_real c) w.im_pos
  linarith

/-- `|c w + d₀| ≥ c · Im w`. -/
theorem le_norm_linear (w : ℍ) : (c : ℝ) * w.im ≤ ‖(c : ℂ) * (w : ℂ) + unitVal c u‖ := by
  have h := Complex.abs_im_le_norm ((c : ℂ) * (w : ℂ) + unitVal c u)
  rw [im_linear, UpperHalfPlane.coe_im, abs_of_pos (mul_pos (c_pos_real c) w.im_pos)] at h
  exact h

/-- **The Möbius image**: `M_{c,u} w = a/c - 1/(c(cw + d₀))`. -/
theorem coe_unitRowMatrix_smul (w : ℍ) :
    ((unitRowMatrix c u • w : ℍ) : ℂ)
      = (unitTop c u : ℂ) / c - 1 / ((c : ℂ) * ((c : ℂ) * w + unitVal c u)) := by
  rw [coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast, unitRowMatrix_apply_one_zero,
    unitRowMatrix_apply_one_one, Int.cast_natCast]
  have hdet : (unitTop c u : ℂ) * unitVal c u - ((unitRowMatrix c u) 0 1 : ℂ) * c = 1 := by
    have := unitRowMatrix_det c u
    have h' : ((unitTop c u * ((u : ZMod c).val : ℤ) - (unitRowMatrix c u) 0 1 * c : ℤ) : ℂ) = 1 := by
      rw [this]; simp
    push_cast at h'
    simpa [unitVal] using h'
  have hc := c_ne_zero_complex c
  have hU := linear_ne_zero' c u w
  rw [unitTop] at hdet ⊢
  simp only [unitVal] at hdet hU ⊢
  push_cast at hdet hU ⊢
  rw [div_sub_div _ _ hc (mul_ne_zero hc hU), div_eq_div_iff hU (mul_ne_zero hc (mul_ne_zero hc hU))]
  linear_combination (-((c : ℂ) * ((c : ℂ) * (w : ℂ) + (((u : ZMod c).val : ℕ) : ℂ)))) * hdet

/-- The exponential factor splits: `e(m M w) = e(ma/c) · exp(-2πi m/(c(cw + d₀)))`. -/
theorem expSeed_unitRowMatrix_smul (m : ℕ) (w : ℍ) :
    expSeed m (unitRowMatrix c u • w)
      = Complex.exp (2 * π * I * m * (unitTop c u : ℂ) / c) *
          Complex.exp ((-2 * π * I * m / c) / ((c : ℂ) * w + unitVal c u)) := by
  rw [expSeed, coe_unitRowMatrix_smul, ← Complex.exp_add]
  congr 1
  have hc := c_ne_zero_complex c
  have hU := linear_ne_zero' c u w
  field_simp
  ring

/-! ## The exponential series -/

theorem hasSum_exp_div (x U : ℂ) :
    HasSum (fun j : ℕ => x ^ j / (j.factorial : ℂ) * U ^ (-(j : ℤ))) (Complex.exp (x / U)) := by
  have := NormedSpace.expSeries_div_hasSum_exp (x / U)
  rw [← Complex.exp_eq_exp_ℂ] at this
  refine this.congr_fun fun j => ?_
  rw [div_pow, zpow_neg, zpow_natCast]
  ring

/-! ## Absolute convergence of the double series -/

/-- `U_l = c(z + l) + d₀`. -/
def linearShift (z : ℍ) (l : ℤ) : ℂ := (c : ℂ) * ((z : ℂ) + l) + unitVal c u

theorem linearShift_eq (z : ℍ) (l : ℤ) :
    linearShift c u z l = (c : ℂ) * ((ModularGroup.T ^ l • z : ℍ) : ℂ) + unitVal c u := by
  rw [linearShift, coe_T_zpow_smul_eq]

theorem le_norm_linearShift (z : ℍ) (l : ℤ) : (c : ℝ) * z.im ≤ ‖linearShift c u z l‖ := by
  rw [linearShift_eq]
  have := le_norm_linear c u (ModularGroup.T ^ l • z)
  rwa [im_T_zpow_smul] at this

theorem linearShift_ne_zero (z : ℍ) (l : ℤ) : linearShift c u z l ≠ 0 := by
  rw [linearShift_eq]
  exact linear_ne_zero' c u _

theorem summable_norm_linearShift_zpow {k : ℤ} (hk : 3 ≤ k) (z : ℍ) :
    Summable fun l : ℤ => ‖linearShift c u z l‖ ^ (-k) := by
  have h := (summable_norm_eisSummand hk z).comp_injective (i := fun l : ℤ => (shiftedRow c u l).1)
    (fun l l' (h : (shiftedRow c u l).1 = (shiftedRow c u l').1) => by
      have := congrArg (fun v : Fin 2 → ℤ => v 1) h
      simp only [shiftedRow_val_one] at this
      have hc : ((c : ℕ) : ℤ) ≠ 0 := by exact_mod_cast c.ne_zero
      exact mul_right_cancel₀ hc (by linarith))
  refine h.congr fun l => ?_
  simp only [Function.comp_def, eisSummand_shiftedRow, norm_zpow]
  rfl

/-- The double family `(l, j) ↦ x^j/j! · U_l^{-(k+j)}` is absolutely summable. -/
theorem summable_uncurry_expansion {k : ℕ} (hk : 3 ≤ k) (x : ℂ) (z : ℍ) :
    Summable (Function.uncurry fun (l : ℤ) (j : ℕ) =>
      x ^ j / (j.factorial : ℂ) * linearShift c u z l ^ (-((k + j : ℕ) : ℤ))) := by
  have hcy : (0 : ℝ) < c * z.im := mul_pos (c_pos_real c) z.im_pos
  have hg : Summable fun j : ℕ => (‖x‖ / (c * z.im)) ^ j / (j.factorial : ℝ) :=
    Real.summable_pow_div_factorial _
  have hh : Summable fun l : ℤ => ‖linearShift c u z l‖ ^ (-(k : ℤ)) :=
    summable_norm_linearShift_zpow c u (by exact_mod_cast hk) z
  have hprod := Summable.mul_of_nonneg hh hg (fun l => by positivity) (fun j => by positivity)
  refine Summable.of_norm_bounded hprod fun p => ?_
  obtain ⟨l, j⟩ := p
  have hU : (0 : ℝ) < ‖linearShift c u z l‖ := lt_of_lt_of_le hcy (le_norm_linearShift c u z l)
  have hle := le_norm_linearShift c u z l
  simp only [Function.uncurry_apply_pair, norm_mul, norm_div, norm_pow, norm_zpow,
    Complex.norm_natCast]
  rw [div_pow, div_div, zpow_neg, zpow_natCast, pow_add, mul_inv, zpow_neg, zpow_natCast]
  calc ‖x‖ ^ j / (j.factorial : ℝ) * ((‖linearShift c u z l‖ ^ k)⁻¹ * (‖linearShift c u z l‖ ^ j)⁻¹)
      ≤ ‖x‖ ^ j / (j.factorial : ℝ) * ((‖linearShift c u z l‖ ^ k)⁻¹ * ((c * z.im) ^ j)⁻¹) := by
        gcongr
    _ = (‖linearShift c u z l‖ ^ k)⁻¹ * (‖x‖ ^ j / ((c * z.im) ^ j * (j.factorial : ℝ))) := by
        ring

/-! ## The expansion -/

theorem cosetTerm_eq_tsum {k : ℕ} (m : ℕ) (z : ℍ) (l : ℤ) :
    cosetTerm (k : ℤ) m c u l z
      = Complex.exp (2 * π * I * m * (unitTop c u : ℂ) / c) *
        ∑' j : ℕ, (-2 * π * I * m / c) ^ j / (j.factorial : ℂ) *
          linearShift c u z l ^ (-((k + j : ℕ) : ℤ)) := by
  rw [cosetTerm, expSeed_unitRowMatrix_smul, ← linearShift_eq,
    show (c : ℂ) * ((z : ℂ) + l) + (((u : ZMod c).val : ℕ) : ℂ) = linearShift c u z l from rfl,
    ← (hasSum_exp_div (-2 * π * I * m / c) (linearShift c u z l)).tsum_eq, mul_left_comm]
  conv_lhs => rw [← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  have hU := linearShift_ne_zero c u z l
  rw [show (-((k + j : ℕ) : ℤ)) = -(k : ℤ) + -(j : ℤ) by push_cast; ring, zpow_add₀ hU]
  ring

/-- **The exponential expansion of the coset sum.** -/
theorem tsum_cosetTerm_eq {k : ℕ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) :
    ∑' l : ℤ, cosetTerm (k : ℤ) m c u l z
      = Complex.exp (2 * π * I * m * (unitTop c u : ℂ) / c) *
        ∑' j : ℕ, (-2 * π * I * m / c) ^ j / (j.factorial : ℂ) *
          ∑' l : ℤ, linearShift c u z l ^ (-((k + j : ℕ) : ℤ)) := by
  simp_rw [cosetTerm_eq_tsum]
  rw [tsum_mul_left]
  congr 1
  rw [← (summable_uncurry_expansion c u hk (-2 * π * I * m / c) z).tsum_comm]
  refine tsum_congr fun j => ?_
  rw [tsum_mul_left]

/-! ## The inner Lipschitz sums -/

/-- The shifted point `w = z + d₀/c`. -/
def shiftedPoint (z : ℍ) : ℍ :=
  ⟨(z : ℂ) + unitVal c u / c, by
    simp only [Complex.add_im, unitVal]
    rw [show ((((u : ZMod c).val : ℕ) : ℂ) / (c : ℂ)).im = 0 by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_im]]
    simpa using z.im_pos⟩

theorem coe_shiftedPoint (z : ℍ) : ((shiftedPoint c u z : ℍ) : ℂ) = (z : ℂ) + unitVal c u / c := rfl

theorem linearShift_eq_mul (z : ℍ) (l : ℤ) :
    linearShift c u z l = (c : ℂ) * (((shiftedPoint c u z : ℍ) : ℂ) + l) := by
  rw [linearShift, coe_shiftedPoint]
  have hc := c_ne_zero_complex c
  field_simp
  ring

/-- **The Lipschitz sum**: for `s ≥ 2`,
`Σ_l (c(z+l) + d₀)^{-s} = c^{-s} (-2πi)^s/(s-1)! Σ_{n ≥ 0} n^{s-1} e(n w)`, `w = z + d₀/c`. -/
theorem tsum_linearShift_zpow {s : ℕ} (hs : 2 ≤ s) (z : ℍ) :
    ∑' l : ℤ, linearShift c u z l ^ (-(s : ℤ))
      = ((c : ℂ) ^ s)⁻¹ * ((-2 * π * I) ^ s / ((s - 1).factorial : ℂ) *
          ∑' n : ℕ, (n : ℂ) ^ (s - 1) * Complex.exp (2 * π * I * (shiftedPoint c u z : ℂ)) ^ n) := by
  have hs' : 1 ≤ s - 1 := by omega
  have key := EisensteinSeries.qExpansion_identity hs' (shiftedPoint c u z)
  rw [show s - 1 + 1 = s by omega] at key
  rw [← key, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  rw [linearShift_eq_mul, zpow_neg, zpow_natCast, mul_pow, one_div, mul_inv]

end

end GaloisForLFunctions.HTGeometry
