import GaloisForLFunctions.Bottcher.ModularLambda

/-!
# The theta-group Hauptmodul and the weakly holomorphic weight-`½` forms `θ₃·P(h)`

`h = θ₂⁴θ₄⁴/θ₃⁸ = λ(1-λ)` is invariant under `τ ↦ τ+2` and `τ ↦ -1/τ`, holomorphic on the upper
half-plane, vanishes at the cusp `∞` and has a pole at the cusp `1`.  For every polynomial `P` the
function `θ₃·P(h)` is two-periodic and has exactly the theta inversion law
`F(-1/τ) = (-iτ)^{1/2} F(τ)`.  Its theta source is therefore even with integer spectrum.  These
forms are the level-one deformation class of the theta source used in the route-2 audit.
-/

open Complex
open scoped Real

namespace RHTower

noncomputable section

open Bottcher

/-- The `Γ_θ` Hauptmodul `h = θ₂⁴θ₄⁴/θ₃⁸ = λ(1-λ)`. -/
def thetaGroupHauptmodul (τ : ℂ) : ℂ :=
  thetaTwo τ ^ (4 : ℕ) * thetaFour τ ^ (4 : ℕ) / thetaThree τ ^ (8 : ℕ)

theorem thetaTwo_add_two (τ : ℂ) :
    thetaTwo (τ + 2) = Complex.exp ((π : ℂ) * I / 4) ^ (2 : ℕ) * thetaTwo τ := by
  rw [show τ + 2 = (τ + 1) + 1 by ring, thetaTwo_add_one, thetaTwo_add_one]; ring

theorem thetaFour_add_two (τ : ℂ) : thetaFour (τ + 2) = thetaFour τ := by
  rw [show τ + 2 = (τ + 1) + 1 by ring, thetaFour_add_one, thetaThree_add_one]

theorem exp_pi_I_div_four_pow_eight : Complex.exp ((π : ℂ) * I / 4) ^ (8 : ℕ) = 1 := by
  rw [← Complex.exp_nat_mul, show ((8 : ℕ) : ℂ) * ((π : ℂ) * I / 4) = 2 * π * I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

theorem thetaGroupHauptmodul_add_two (τ : ℂ) :
    thetaGroupHauptmodul (τ + 2) = thetaGroupHauptmodul τ := by
  unfold thetaGroupHauptmodul
  rw [thetaTwo_add_two, thetaFour_add_two, thetaThree_add_two, mul_pow, ← pow_mul,
    show 2 * 4 = 8 by norm_num, exp_pi_I_div_four_pow_eight, one_mul]

theorem thetaGroupHauptmodul_S {τ : ℂ} (hτ : 0 < τ.im) :
    thetaGroupHauptmodul (-1 / τ) = thetaGroupHauptmodul τ := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have hIτ : I / τ ≠ 0 := div_ne_zero I_ne_zero hτ0
  have hmIτ : -I * τ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0
  unfold thetaGroupHauptmodul
  rw [thetaTwo_S τ hτ0, thetaFour_S τ hτ0, thetaThree_S τ hτ0]
  set P := (I / τ) ^ (1 / 2 : ℂ) with hP
  set Q := (-I * τ) ^ (1 / 2 : ℂ) with hQ
  have hPne : P ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hIτ
  have hQne : Q ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hmIτ
  have hP2 : P ^ (2 : ℕ) = I / τ := by
    rw [hP, pow_two, ← Complex.cpow_add _ _ hIτ, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
      Complex.cpow_one]
  have hQ2 : Q ^ (2 : ℕ) = -I * τ := by
    rw [hQ, pow_two, ← Complex.cpow_add _ _ hmIτ, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
      Complex.cpow_one]
  have hPQ2 : (P * Q) ^ (2 : ℕ) = 1 := by
    rw [mul_pow, hP2, hQ2]
    have he : (I / τ) * (-I * τ) = -(I ^ (2 : ℕ)) * (τ / τ) := by ring
    rw [he, I_sq, div_self hτ0]; norm_num
  have hPQ8 : P ^ (8 : ℕ) * Q ^ (8 : ℕ) = 1 := by
    rw [← mul_pow, show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, hPQ2, one_pow]
  have hθ3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  field_simp
  linear_combination (-(thetaFour τ ^ 4 * thetaTwo τ ^ 4)) * hPQ8

/-- The weakly holomorphic weight-`½` forms `θ₃·P(h)` with the theta multiplier on `Γ_θ`. -/
def thetaGroupForm (P : Polynomial ℂ) (τ : ℂ) : ℂ :=
  thetaThree τ * P.eval (thetaGroupHauptmodul τ)

theorem thetaGroupForm_add_two (P : Polynomial ℂ) (τ : ℂ) :
    thetaGroupForm P (τ + 2) = thetaGroupForm P τ := by
  unfold thetaGroupForm
  rw [thetaThree_add_two, thetaGroupHauptmodul_add_two]

theorem thetaGroupForm_S (P : Polynomial ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaGroupForm P (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaGroupForm P τ := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  unfold thetaGroupForm
  rw [thetaThree_S τ hτ0, thetaGroupHauptmodul_S hτ]; ring

theorem differentiableAt_thetaGroupHauptmodul {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaGroupHauptmodul τ := by
  unfold thetaGroupHauptmodul
  have h4 : DifferentiableAt ℂ thetaFour τ := differentiableAt_thetaFour hτ
  exact (((differentiableAt_thetaTwo hτ).pow 4).mul (h4.pow 4)).div
    ((differentiableAt_thetaThree hτ).pow 8) (pow_ne_zero 8 (thetaThree_ne_zero_of_im_pos hτ))

theorem differentiableAt_thetaGroupForm (P : Polynomial ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (thetaGroupForm P) τ := by
  unfold thetaGroupForm
  exact (differentiableAt_thetaThree hτ).mul
    ((P.differentiable.differentiableAt).comp τ (differentiableAt_thetaGroupHauptmodul hτ))

end

end RHTower
