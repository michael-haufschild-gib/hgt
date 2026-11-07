import Mathlib

/-!
# The depth aspect and the archimedean place

What replaces `q`-factorization at the archimedean place, where a height has no prime factors?

**Depth aspect: exact.** Let `q = q₁ q₂` with `q₂ ∣ q₁`. Then `q₁² ≡ 0 mod q`, so
`(1 + q₁u)(1 + q₁v) ≡ 1 + q₁(u + v) mod q` (`one_add_mul_mul_one_add_mul`): `u ↦ 1 + q₁u` is a homomorphism from the
additive group into the units. For every multiplicative character `χ` mod `q`:

* `ψ(u) = χ(1 + q₁u)` is an additive character (`mulChar_one_add_mul_add`);
* **`q`-differencing is exact** (`mulChar_add_mul`): `χ(n + q₁h) = χ(n) ψ(h n⁻¹)` for a unit `n`. Summing `χ` over a
  progression of step `q₁` is summing an additive character.

**Archimedean place: approximate.** The multiplicative interval `1 + [0, H/x]` is the analogue of `1 + q₁ℤ`.
`h ↦ t log(1 + h/x)` is additive up to the defect `t h h'/x²` (`log_one_add_defect_le`), and it is the additive
character `t h/x` up to `|t| h²/x²` (`abs_log_one_add_sub_le`). So it is an additive character exactly while
`|t| H² ≪ x²`, that is on `H ≪ x/√|t|`.

Both places factor at the square root of the conductor: `q₁ ≥ √q` in depth (`q₂ ∣ q₁`), `H ≍ x/√t` at the height. What
the archimedean place lacks is exactness: the quadratic Taylor term is the defect that vanishes `p`-adically. A height
has every real scale as a factor, at the price `t h²/x²` per step; this is the van der Corput `B`-process, and it is why
the height aspect has the Weyl–Vinogradov losses that smooth moduli avoid.
-/

open Real

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- `q₁² = 0` modulo `q₁ q₂` when `q₂ ∣ q₁`. -/
theorem natCast_sq_eq_zero {q₁ q₂ : ℕ} (h : q₂ ∣ q₁) : ((q₁ : ZMod (q₁ * q₂)) ^ 2) = 0 := by
  obtain ⟨k, rfl⟩ := h
  have e : ((q₂ * k : ℕ) : ZMod (q₂ * k * q₂)) ^ 2 = (((q₂ * k * q₂) * k : ℕ) : ZMod (q₂ * k * q₂)) := by
    push_cast
    ring
  rw [e, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- **The exact homomorphism of the depth aspect.** -/
theorem one_add_mul_mul_one_add_mul {q₁ q₂ : ℕ} (h : q₂ ∣ q₁) (u v : ZMod (q₁ * q₂)) :
    (1 + (q₁ : ZMod (q₁ * q₂)) * u) * (1 + q₁ * v) = 1 + q₁ * (u + v) := by
  have h0 := natCast_sq_eq_zero h
  linear_combination u * v * h0

/-- `χ(1 + q₁ ·)` is an additive character. -/
theorem mulChar_one_add_mul_add {q₁ q₂ : ℕ} (h : q₂ ∣ q₁) (χ : MulChar (ZMod (q₁ * q₂)) ℂ)
    (u v : ZMod (q₁ * q₂)) :
    χ (1 + q₁ * (u + v)) = χ (1 + q₁ * u) * χ (1 + q₁ * v) := by
  rw [← map_mul, one_add_mul_mul_one_add_mul h]

/-- **`q`-differencing is exact.** -/
theorem mulChar_add_mul {q₁ q₂ : ℕ} (χ : MulChar (ZMod (q₁ * q₂)) ℂ) (n : (ZMod (q₁ * q₂))ˣ)
    (hh : ZMod (q₁ * q₂)) :
    χ (n + q₁ * hh) = χ n * χ (1 + q₁ * (hh * (n⁻¹ : (ZMod (q₁ * q₂))ˣ))) := by
  rw [← map_mul]
  congr 1
  have : (n : ZMod (q₁ * q₂)) * (n⁻¹ : (ZMod (q₁ * q₂))ˣ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination (-(q₁ : ZMod (q₁ * q₂)) * hh) * this

/-! ## The archimedean place -/

/-- `0 ≤ log(1+a) + log(1+b) − log(1+a+b) ≤ ab` for `a, b ≥ 0`. -/
theorem log_one_add_add_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ Real.log (1 + a) + Real.log (1 + b) - Real.log (1 + (a + b)) ∧
      Real.log (1 + a) + Real.log (1 + b) - Real.log (1 + (a + b)) ≤ a * b := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + (a + b) := by linarith
  have e : Real.log (1 + a) + Real.log (1 + b) - Real.log (1 + (a + b)) =
      Real.log (1 + a * b / (1 + (a + b))) := by
    rw [← Real.log_mul h1.ne' h2.ne', ← Real.log_div (by positivity) h3.ne']
    congr 1
    field_simp
    ring
  rw [e]
  have hq : 0 ≤ a * b / (1 + (a + b)) := by positivity
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  calc Real.log (1 + a * b / (1 + (a + b))) ≤ a * b / (1 + (a + b)) := by
        have := Real.log_le_sub_one_of_pos (x := 1 + a * b / (1 + (a + b))) (by positivity)
        linarith
    _ ≤ a * b := div_le_self (by positivity) (by linarith)

/-- **The archimedean homomorphism is approximate.** `h ↦ t log(1 + h/x)` is additive up to `|t| h h'/x²`. -/
theorem log_one_add_defect_le (t : ℝ) {x h h' : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hh' : 0 ≤ h') :
    |t * Real.log (1 + h / x) + t * Real.log (1 + h' / x) - t * Real.log (1 + (h + h') / x)| ≤
      |t| * (h * h') / x ^ 2 := by
  obtain ⟨h1, h2⟩ := log_one_add_add_sub_le (div_nonneg hh hx.le) (div_nonneg hh' hx.le)
  have e : t * Real.log (1 + h / x) + t * Real.log (1 + h' / x) - t * Real.log (1 + (h + h') / x) =
      t * (Real.log (1 + h / x) + Real.log (1 + h' / x) - Real.log (1 + (h / x + h' / x))) := by
    rw [add_div]
    ring
  rw [e, abs_mul, abs_of_nonneg h1]
  have e2 : h / x * (h' / x) = h * h' / x ^ 2 := by field_simp
  rw [mul_div_assoc, ← e2]
  exact mul_le_mul_of_nonneg_left h2 (abs_nonneg t)

/-- `|log(1+u) − u| ≤ u²` for `u ≥ 0`. -/
theorem abs_log_one_add_sub_le_sq {u : ℝ} (hu : 0 ≤ u) : |Real.log (1 + u) - u| ≤ u ^ 2 := by
  have h1 : 0 < 1 + u := by linarith
  have hup : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hlo : u / (1 + u) ≤ Real.log (1 + u) := by
    have := Real.log_le_sub_one_of_pos (x := (1 + u)⁻¹) (by positivity)
    rw [Real.log_inv] at this
    have e : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by field_simp; ring
    linarith
  have hgap : u - u / (1 + u) ≤ u ^ 2 := by
    have e : u - u / (1 + u) = u ^ 2 / (1 + u) := by field_simp; ring
    rw [e]
    exact div_le_self (sq_nonneg u) (by linarith)
  rw [abs_le]
  constructor <;> linarith

/-- **The archimedean additive character.** `t log(1 + h/x) = t h/x` up to `|t| h²/x²`. -/
theorem abs_log_one_add_sub_le (t : ℝ) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    |t * Real.log (1 + h / x) - t * (h / x)| ≤ |t| * h ^ 2 / x ^ 2 := by
  rw [← mul_sub, abs_mul]
  have := abs_log_one_add_sub_le_sq (div_nonneg hh hx.le)
  rw [div_pow] at this
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left this (abs_nonneg t)

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
