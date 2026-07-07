/-
The local argument principle: the winding number counts enclosed order.

A zero of order `m` at the centre of a circle contributes exactly `m` to the winding number of the
loop around it (`windingNumber_center_zero`): the boundary loop `θ ↦ (r·e^{iθ})^m` lifts through the
logarithm `θ ↦ m·(log r + iθ)`, whose increment over `[0,2π]` is `m·2πi`.  Specialised to `m = r = 1`
this is the fundamental computation `windingNumber(e^{iθ}) = 1` (`windingNumber_circle`) — the winding
number is not identically zero.

Consequently the loop deck charge around an order-`m` zero is `m mod 2^k`
(`loopCharge_center_zero`): the *topological* winding realisation of the deck charge and the
*algebraic* `wCharge` of the enclosed order are the same observable.  This is the local case of the
argument principle, welding `WindingNumber` to the `DeckChargeCalculus`.
-/
import GaloisForLFunctions.RHTower.WindingNumber

open Complex Set

namespace RHTower

/-- **The local argument principle.**  The winding number of the boundary loop `θ ↦ (r·e^{iθ})^m`
(`r > 0`) around the centre is the order `m`: a zero of order `m` winds the loop `m` times. -/
theorem windingNumber_center_zero (m : ℕ) (r : ℝ) (hr : 0 < r) :
    windingNumber (fun θ => (↑r * exp (I * ↑θ)) ^ m) 0 (2 * Real.pi) = (m : ℤ) := by
  have hexp_r : exp ((Real.log r : ℂ)) = (r : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hr]
  have hcont : Continuous (fun θ : ℝ => (↑r * exp (I * ↑θ)) ^ m) := by fun_prop
  have hnz : ∀ θ : ℝ, (↑r * exp (I * ↑θ)) ^ m ≠ 0 := fun θ =>
    pow_ne_zero _ (mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _))
  have hclosed : (fun θ : ℝ => (↑r * exp (I * ↑θ)) ^ m) 0
      = (fun θ : ℝ => (↑r * exp (I * ↑θ)) ^ m) (2 * Real.pi) := by
    simp only
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    congr 2
    rw [show (I * ((2 : ℝ) * Real.pi : ℝ)) = ((2 : ℂ) * Real.pi * I) by push_cast; ring,
      Complex.exp_two_pi_mul_I]
  have hL : IsLoop (fun θ : ℝ => (↑r * exp (I * ↑θ)) ^ m) 0 (2 * Real.pi) := ⟨hcont, hnz, hclosed⟩
  set L : ℝ → ℂ := fun θ => (m : ℂ) * ((Real.log r : ℂ) + I * ↑θ) with hLdef
  have hLcont : Continuous L := by fun_prop
  have hLexp : ∀ θ, exp (L θ) = (↑r * exp (I * ↑θ)) ^ m := by
    intro θ; rw [hLdef]; simp only; rw [Complex.exp_nat_mul, Complex.exp_add, hexp_r]
  have key := contLog_increment hL hLcont hLexp
  rw [hLdef] at key; simp only [Complex.ofReal_zero, mul_zero, add_zero] at key
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hcast : (m : ℂ)
      = ((windingNumber (fun θ : ℝ => (↑r * exp (I * ↑θ)) ^ m) 0 (2 * Real.pi) : ℤ) : ℂ) := by
    apply mul_right_cancel₀ h2pi; rw [← key]; push_cast; ring
  exact_mod_cast hcast.symm

/-- **The fundamental winding.**  The unit circle `θ ↦ e^{iθ}` winds once about the origin — the
winding number is not identically zero. -/
theorem windingNumber_circle : windingNumber (fun θ : ℝ => exp (I * ↑θ)) 0 (2 * Real.pi) = 1 := by
  have h := windingNumber_center_zero 1 1 one_pos
  simp only [Complex.ofReal_one, one_mul, pow_one, Nat.cast_one] at h
  exact h

/-- **The winding realisation of the deck charge is the algebraic one.**  The loop deck charge around
an order-`m` zero is `m mod 2^k` — precisely `wCharge (2^k) m`, the abstract deck charge of the
enclosed order.  The topological winding and the algebraic `wCharge` coincide on the local model. -/
theorem loopCharge_center_zero (k m : ℕ) (r : ℝ) (hr : 0 < r) :
    loopCharge k (fun θ => (↑r * exp (I * ↑θ)) ^ m) 0 (2 * Real.pi) = wCharge (2 ^ k) (m : ℤ) := by
  rw [loopCharge, windingNumber_center_zero m r hr]

/-- The order-`m` zero is invisible to the rung-`k` charge exactly when `2^k ∣ m` — the local
instance of `loopCharge_eq_zero_iff` and of the `RH_{2^k}` divisibility condition. -/
theorem loopCharge_center_zero_eq_zero_iff (k m : ℕ) (r : ℝ) (hr : 0 < r) :
    loopCharge k (fun θ => (↑r * exp (I * ↑θ)) ^ m) 0 (2 * Real.pi) = 0 ↔ 2 ^ k ∣ m := by
  rw [loopCharge_center_zero k m r hr]
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [wCharge_eq_zero_iff]
  norm_cast

end RHTower
