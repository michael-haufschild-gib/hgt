import GaloisForLFunctions.RHTower.ThetaGroupHauptmodulForms
import GaloisForLFunctions.RHTower.ModularAxisSourceTransform
import GaloisForLFunctions.RHTower.JacobiThetaBoundaryLimits

/-!
# Cusp data of the theta-group basis forms `θ₃·h^j`

The basis forms satisfy the theta inversion law on the imaginary axis,
`F(ie^{-2x}) = e^{x}F(ie^{2x})`, and decay at the cusp `∞`:
`‖θ₃h^j - δ_{j0}‖ ≤ M_j e^{-π im τ}` for `im τ ≥ 1`.  Hence each has an even theta source with an
entire transform (`ModularAxisSourceTransform`).
-/

open Complex
open scoped Real

namespace RHTower

noncomputable section

open Bottcher

/-- The basis forms `θ₃·h^j`. -/
def thetaGroupBasis (j : ℕ) (τ : ℂ) : ℂ := thetaThree τ * thetaGroupHauptmodul τ ^ j

theorem thetaGroupBasis_eq_form (j : ℕ) :
    thetaGroupBasis j = thetaGroupForm (Polynomial.X ^ j) := by
  funext τ; simp [thetaGroupBasis, thetaGroupForm]

theorem differentiableOn_thetaGroupBasis (j : ℕ) :
    DifferentiableOn ℂ (thetaGroupBasis j) modUpperSet := by
  rw [thetaGroupBasis_eq_form]
  intro τ hτ
  exact (differentiableAt_thetaGroupForm _ hτ).differentiableWithinAt

theorem neg_one_div_modAxisPoint (x : ℝ) : -1 / modAxisPoint x = modAxisPoint (-x) := by
  unfold modAxisPoint
  have he : (Real.exp (2 * -x) : ℂ) = ((Real.exp (2 * x) : ℂ))⁻¹ := by
    rw [show 2 * -x = -(2 * x) by ring, Real.exp_neg]; push_cast; ring
  rw [he]
  have hne : (Real.exp (2 * x) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  field_simp
  rw [I_sq]

theorem cpow_half_neg_I_mul_modAxisPoint (x : ℝ) :
    (-I * modAxisPoint x) ^ (1 / 2 : ℂ) = (Real.exp x : ℂ) := by
  have h1 : -I * modAxisPoint x = ((Real.exp (2 * x) : ℝ) : ℂ) := by
    unfold modAxisPoint
    rw [← mul_assoc, show -I * I = 1 by rw [neg_mul, I_mul_I]; ring, one_mul]
  rw [h1, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2; ring

/-- The theta inversion law read on the imaginary axis. -/
theorem thetaGroupForm_axis (P : Polynomial ℂ) (x : ℝ) :
    thetaGroupForm P (modAxisPoint (-x)) = (Real.exp x : ℂ) * thetaGroupForm P (modAxisPoint x) := by
  have h := thetaGroupForm_S P (modAxisPoint_mem x)
  rw [neg_one_div_modAxisPoint, cpow_half_neg_I_mul_modAxisPoint] at h
  exact h

theorem thetaGroupBasis_axis (j : ℕ) (x : ℝ) :
    thetaGroupBasis j (modAxisPoint (-x)) = (Real.exp x : ℂ) * thetaGroupBasis j (modAxisPoint x) := by
  rw [thetaGroupBasis_eq_form]; exact thetaGroupForm_axis _ x

/-! ## Cusp bounds -/

theorem thetaThree_eq_jacobiTheta (τ : ℂ) : thetaThree τ = jacobiTheta τ := by
  rw [thetaThree, jacobiTheta_eq_jacobiTheta₂]

theorem norm_thetaThree_sub_one_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖thetaThree τ - 1‖ ≤ jacobiThetaTailConstant * Real.exp (-π * τ.im) := by
  rw [thetaThree_eq_jacobiTheta]; exact norm_jacobiTheta_sub_one_le' hτ

theorem norm_thetaFour_sub_one_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖thetaFour τ - 1‖ ≤ jacobiThetaTailConstant * Real.exp (-π * τ.im) := by
  rw [thetaFour_eq]
  have h := norm_jacobiTheta_sub_one_le' (τ := τ + 1) (by simpa using hτ)
  simpa using h

theorem jacobiThetaTailConstant_mul_exp_neg_pi_lt :
    jacobiThetaTailConstant * Real.exp (-π) < 1 / 2 := by
  have hπ : 3 < π := Real.pi_gt_three
  have he3 : Real.exp (-π) < 1 / 20 := by
    have h1 : Real.exp (-π) < Real.exp (-3) := Real.exp_lt_exp.mpr (by linarith)
    have h2 : (20 : ℝ) < Real.exp 3 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : (2.718 : ℝ) < Real.exp 1 := by
        have := Real.exp_one_gt_d9; linarith
      have h5 : (2.718 : ℝ) ^ 3 < Real.exp 1 ^ 3 := pow_lt_pow_left₀ h4 (by norm_num) (by norm_num)
      rw [h3]; norm_num at h5 ⊢; linarith
    have h5 : Real.exp (-3) = (Real.exp 3)⁻¹ := Real.exp_neg 3
    have h6 : (Real.exp 3)⁻¹ < 1 / 20 := by
      rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]; norm_num; linarith
    linarith
  rw [jacobiThetaTailConstant]
  have hpos : 0 < 1 - Real.exp (-π) := by linarith [Real.exp_pos (-π)]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
  nlinarith [Real.exp_pos (-π)]

theorem exp_neg_pi_mul_le_exp_neg_pi {v : ℝ} (hv : 1 ≤ v) :
    Real.exp (-π * v) ≤ Real.exp (-π) := by
  apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]

theorem half_le_norm_thetaThree {τ : ℂ} (hτ : 1 ≤ τ.im) : 1 / 2 ≤ ‖thetaThree τ‖ := by
  have h := norm_thetaThree_sub_one_le hτ
  have hsmall : ‖thetaThree τ - 1‖ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left (exp_neg_pi_mul_le_exp_neg_pi hτ)
      jacobiThetaTailConstant_pos.le
    linarith [jacobiThetaTailConstant_mul_exp_neg_pi_lt]
  have htri := norm_sub_norm_le (1 : ℂ) (1 - thetaThree τ)
  rw [sub_sub_cancel, norm_one, norm_sub_rev] at htri
  linarith

theorem norm_thetaThree_le_two {τ : ℂ} (hτ : 1 ≤ τ.im) : ‖thetaThree τ‖ ≤ 2 := by
  have h := norm_thetaThree_sub_one_le hτ
  have hsmall : ‖thetaThree τ - 1‖ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left (exp_neg_pi_mul_le_exp_neg_pi hτ)
      jacobiThetaTailConstant_pos.le
    linarith [jacobiThetaTailConstant_mul_exp_neg_pi_lt]
  have := norm_le_insert' (thetaThree τ) 1
  calc ‖thetaThree τ‖ = ‖(thetaThree τ - 1) + 1‖ := by ring_nf
    _ ≤ ‖thetaThree τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

theorem norm_thetaFour_le_two {τ : ℂ} (hτ : 1 ≤ τ.im) : ‖thetaFour τ‖ ≤ 2 := by
  have h := norm_thetaFour_sub_one_le hτ
  have hsmall : ‖thetaFour τ - 1‖ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left (exp_neg_pi_mul_le_exp_neg_pi hτ)
      jacobiThetaTailConstant_pos.le
    linarith [jacobiThetaTailConstant_mul_exp_neg_pi_lt]
  calc ‖thetaFour τ‖ = ‖(thetaFour τ - 1) + 1‖ := by ring_nf
    _ ≤ ‖thetaFour τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

/-- Constant for the `θ₂` cusp bound. -/
def thetaTwoCuspConstant : ℝ := ∑' n : ℤ, Real.exp (-π * ((n : ℝ) ^ (2 : ℕ) + n))

theorem summable_thetaTwoCusp : Summable (fun n : ℤ => Real.exp (-π * ((n : ℝ) ^ (2 : ℕ) + n))) := by
  refine (summable_pow_mul_jacobiTheta₂_term_bound (1 / 2) one_pos 0).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le) (fun n => ?_)
  rw [pow_zero, one_mul]
  apply Real.exp_le_exp.mpr
  have h : -(n : ℝ) ≤ ((|n| : ℤ) : ℝ) := by rw [Int.cast_abs]; exact neg_le_abs _
  nlinarith [mul_nonneg Real.pi_pos.le (by linarith : 0 ≤ (n : ℝ) + ((|n| : ℤ) : ℝ))]

theorem int_sq_add_self_nonneg (n : ℤ) : 0 ≤ (n : ℝ) ^ (2 : ℕ) + n := by
  have : 0 ≤ n ^ 2 + n := by nlinarith
  exact_mod_cast this

theorem norm_thetaTwo_le_cusp {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖thetaTwo τ‖ ≤ thetaTwoCuspConstant * Real.exp (-π * τ.im / 4) := by
  have hτ0 : 0 < τ.im := by linarith
  unfold thetaTwo
  rw [norm_mul, Complex.norm_exp]
  have hre : ((π : ℂ) * I * τ / 4).re = -π * τ.im / 4 := by
    simp [Complex.mul_re]
  rw [hre, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hsum : Summable (fun n : ℤ => ‖jacobiTheta₂_term n (τ / 2) τ‖) := by
    refine summable_thetaTwoCusp.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    rw [norm_jacobiTheta₂_half_term]
    apply Real.exp_le_exp.mpr
    have := int_sq_add_self_nonneg n
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le this) (by linarith : (0 : ℝ) ≤ τ.im - 1)]
  rw [jacobiTheta₂]
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  refine hsum.tsum_le_tsum (fun n => ?_) summable_thetaTwoCusp
  rw [norm_jacobiTheta₂_half_term]
  apply Real.exp_le_exp.mpr
  have := int_sq_add_self_nonneg n
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le this) (by linarith : (0 : ℝ) ≤ τ.im - 1)]

theorem thetaTwoCuspConstant_nonneg : 0 ≤ thetaTwoCuspConstant :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-- Cusp bound for the Hauptmodul. -/
theorem norm_thetaGroupHauptmodul_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖thetaGroupHauptmodul τ‖ ≤ 4096 * thetaTwoCuspConstant ^ 4 * Real.exp (-π * τ.im) := by
  unfold thetaGroupHauptmodul
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow]
  have h2 := norm_thetaTwo_le_cusp hτ
  have h4 := norm_thetaFour_le_two hτ
  have h3 := half_le_norm_thetaThree hτ
  have hK := thetaTwoCuspConstant_nonneg
  have h3pos : 0 < ‖thetaThree τ‖ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have hA : ‖thetaTwo τ‖ ^ 4 ≤ thetaTwoCuspConstant ^ 4 * Real.exp (-π * τ.im) := by
    calc ‖thetaTwo τ‖ ^ 4 ≤ (thetaTwoCuspConstant * Real.exp (-π * τ.im / 4)) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 4
      _ = thetaTwoCuspConstant ^ 4 * Real.exp (-π * τ.im) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hB : ‖thetaFour τ‖ ^ 4 ≤ 16 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h4 4; norm_num at this; linarith
  have hC : (1 / 2 : ℝ) ^ 8 ≤ ‖thetaThree τ‖ ^ 8 := pow_le_pow_left₀ (by norm_num) h3 8
  have hE := Real.exp_pos (-π * τ.im)
  calc ‖thetaTwo τ‖ ^ 4 * ‖thetaFour τ‖ ^ 4
      ≤ (thetaTwoCuspConstant ^ 4 * Real.exp (-π * τ.im)) * 16 :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = 4096 * thetaTwoCuspConstant ^ 4 * Real.exp (-π * τ.im) * (1 / 2) ^ 8 := by ring
    _ ≤ 4096 * thetaTwoCuspConstant ^ 4 * Real.exp (-π * τ.im) * ‖thetaThree τ‖ ^ 8 :=
        mul_le_mul_of_nonneg_left hC (by positivity)

/-- The value of the basis form at the cusp `∞`. -/
def thetaGroupBasisCusp (j : ℕ) : ℂ := if j = 0 then 1 else 0

theorem thetaGroupBasis_cuspDecay (j : ℕ) :
    ∃ M : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖thetaGroupBasis j τ - thetaGroupBasisCusp j‖ ≤ M * Real.exp (-π * τ.im) := by
  set Ch : ℝ := 4096 * thetaTwoCuspConstant ^ 4 with hCh
  have hCh0 : 0 ≤ Ch := by have := thetaTwoCuspConstant_nonneg; positivity
  rcases Nat.eq_zero_or_pos j with hj | hj
  · refine ⟨jacobiThetaTailConstant, fun τ hτ => ?_⟩
    subst hj
    simp only [thetaGroupBasis, thetaGroupBasisCusp, pow_zero, mul_one, if_true]
    exact norm_thetaThree_sub_one_le hτ
  · refine ⟨2 * Ch ^ j, fun τ hτ => ?_⟩
    have hj0 : j ≠ 0 := hj.ne'
    simp only [thetaGroupBasis, thetaGroupBasisCusp, hj0, if_false, sub_zero]
    have hh := norm_thetaGroupHauptmodul_le hτ
    have h3 := norm_thetaThree_le_two hτ
    have hE1 : Real.exp (-π * τ.im) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; nlinarith [Real.pi_pos]
    rw [norm_mul, norm_pow]
    have hpow : ‖thetaGroupHauptmodul τ‖ ^ j ≤ Ch ^ j * Real.exp (-π * τ.im) := by
      calc ‖thetaGroupHauptmodul τ‖ ^ j ≤ (Ch * Real.exp (-π * τ.im)) ^ j :=
            pow_le_pow_left₀ (norm_nonneg _) hh j
        _ = Ch ^ j * Real.exp (-π * τ.im) ^ j := mul_pow _ _ _
        _ ≤ Ch ^ j * Real.exp (-π * τ.im) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc Real.exp (-π * τ.im) ^ j ≤ Real.exp (-π * τ.im) ^ 1 :=
                  pow_le_pow_of_le_one (Real.exp_pos _).le hE1 hj
              _ = _ := pow_one _
    calc ‖thetaThree τ‖ * ‖thetaGroupHauptmodul τ‖ ^ j
        ≤ 2 * (Ch ^ j * Real.exp (-π * τ.im)) :=
          mul_le_mul h3 hpow (by positivity) (by norm_num)
      _ = 2 * Ch ^ j * Real.exp (-π * τ.im) := by ring

end

end RHTower
