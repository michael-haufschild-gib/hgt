import GaloisForLFunctions.HTGeometry.RittCyclicPoleTransport
import GaloisForLFunctions.HTGeometry.RittTowerDescentStep

/-!
# Regularity of the Faà di Bruno coefficients

Regularity at a point is closed under addition, under differentiation, and under division by a unit.
The coefficients of the shift relation on the jet tower are generated from `q/ρ^n` by exactly those
three operations, so at a point where the chain-rule factor is a unit and the multiplier is a nonzero
constant, every coefficient is regular.

For the cyclic normal form the chain-rule factor is a unit away from the origin and the poles of the
map — precisely the points that a fibre over a non-critical value already avoids — so the pole count
for the affine transport equation has the regular inhomogeneity it needs.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable section

omit [CharZero K] in
/-- Regularity is closed under addition. -/
theorem ratOrder_add_nonneg {x y : RatFunc K} {z : K} (hx : 0 ≤ ratOrder x z)
    (hy : 0 ≤ ratOrder y z) : 0 ≤ ratOrder (x + y) z := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rwa [zero_add]
  rcases eq_or_ne y 0 with rfl | hy0
  · rwa [add_zero]
  rcases eq_or_ne (x + y) 0 with h | hxy0
  · rw [h, ratOrder_zero]
  · have := min_le_ratOrder_add hx0 hy0 hxy0 z
    omega

omit [CharZero K] in
/-- Regularity is closed under division by a unit. -/
theorem ratOrder_div_nonneg {x r : RatFunc K} {z : K} (hr0 : r ≠ 0)
    (hx : 0 ≤ ratOrder x z) (hr : ratOrder r z = 0) : 0 ≤ ratOrder (x / r) z := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_div, ratOrder_zero]
  · rw [div_eq_mul_inv, ratOrder_mul hx0 (inv_ne_zero hr0), ratOrder_inv hr0, hr]
    omega

/-- Regularity is closed under differentiation. -/
theorem ratOrder_deriv_nonneg {x : RatFunc K} {z : K} (hx : 0 ≤ ratOrder x z) :
    0 ≤ ratOrder (ratFuncDeriv x) z := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hz : ratFuncDeriv (0 : RatFunc K) = 0 := by
      rw [← ratFuncDerivation_apply, map_zero]
    rw [hz, ratOrder_zero]
  · exact ratOrder_ratFuncDeriv_nonneg hx0 hx

omit [CharZero K] in
/-- A constant divided by a power of a unit is regular. -/
theorem ratOrder_const_div_pow (c : K) {r : RatFunc K} (hr0 : r ≠ 0) {z : K}
    (hr : ratOrder r z = 0) (m : ℕ) : 0 ≤ ratOrder (RatFunc.C c / r ^ m) z := by
  refine ratOrder_div_nonneg (pow_ne_zero m hr0) ?_ ?_
  · rw [ratOrder_C]
  · rw [ratOrder_pow hr0, hr, mul_zero]

/-- **The Faà di Bruno coefficients are regular where the chain-rule factor is a unit.** -/
theorem exists_shift_jet_coeffs_regular {L : Type*} [Field L] [Algebra (RatFunc K) L]
    (Fr : RittFrame (RatFunc K) L) (hdK : Fr.dK = ratFuncDeriv) {τ : L} (c : K)
    (hshift : Fr.σ τ = algebraMap (RatFunc K) L (RatFunc.C c) * τ)
    {z : K} (hρ : ratOrder Fr.ρ z = 0) :
    ∀ n : ℕ, ∃ A : ℕ → RatFunc K, (∀ j, n ≤ j → A j = 0) ∧
      (∀ j, 0 ≤ ratOrder (A j) z) ∧ Fr.σ (Fr.d^[n] τ)
      = algebraMap (RatFunc K) L (RatFunc.C c / Fr.ρ ^ n) * Fr.d^[n] τ
        + ∑ j ∈ Finset.range n, algebraMap (RatFunc K) L (A j) * Fr.d^[j] τ := by
  refine exists_shift_jet_coeffs_pred Fr hshift (fun x => 0 ≤ ratOrder x z) ?_ ?_ ?_ ?_ ?_
  · rw [ratOrder_zero]
  · exact fun x y hx hy => ratOrder_add_nonneg hx hy
  · intro x hx
    rw [hdK]
    exact ratOrder_deriv_nonneg hx
  · exact fun x hx => ratOrder_div_nonneg Fr.ρ_ne hx hρ
  · exact fun m => ratOrder_const_div_pow c Fr.ρ_ne hρ m

end

end GaloisForLFunctions.HTGeometry
