import GaloisForLFunctions.ArithmeticDiscreteness.EulerColumnsCollideOrRepelAtPolynomialScale

/-!
# Integral pure Euler factors repel at polynomial scale

Where integrality of the local data does help. A degree-two Euler factor
`1 − a p^{−s} + p^{−2s}` with `a ∈ ℤ` is pure (its zeros lie on `Re s = 0`) iff `|a| ≤ 2`; for such
`a` the Satake parameters, the roots of `w² − a w + 1`, are roots of unity
(`pow_twelve_eq_one_of_satake`): `a = ±2` gives `w = ±1`, `a = 0` gives `w² = −1`, `a = ±1` gives
`w³ = ∓1`. So every zero satisfies `p^{−12s} = 1` and lies on the refined Euler column
`2πik/(12 log p)` (`degTwoCarrier_zero_mem_column`).

* **Collide or repel at polynomial scale** (`degTwoCarrier_collide_or_repel`). For distinct primes
  and integers `|a_p| ≤ 2`, distinct zeros of `∏_p (1 − a_p p^{−s} + p^{−2s})` of height `≤ T`
  are at distance `≥ c T^{−C}`: they are zeros of `s ↦ ∏_p (1 − p^{−12s})`, and
  `eulerCarrier_collide_or_repel` applies at height `12T`.

Integrality (Kronecker's theorem in degree two) makes the Satake angles rational multiples of `π`,
which turns every near-coincidence into an integer linear form in prime logarithms.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- **Integral pure Satake parameters are roots of unity.** If `a ∈ ℤ`, `|a| ≤ 2`, and
`w² − a w + 1 = 0`, then `w¹² = 1`. -/
theorem pow_twelve_eq_one_of_satake {a : ℤ} (ha : |a| ≤ 2) {w : ℂ}
    (hw : w ^ 2 - (a : ℂ) * w + 1 = 0) : w ^ 12 = 1 := by
  have ha' : -2 ≤ a ∧ a ≤ 2 := abs_le.mp ha
  obtain ⟨h1, h2⟩ := ha'
  interval_cases a
  · -- `a = −2`: `w = −1`
    have : (w + 1) ^ 2 = 0 := by push_cast at hw; linear_combination hw
    have hw1 : w = -1 := by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this; linear_combination this
    rw [hw1]; norm_num
  · -- `a = −1`: `w³ = 1`
    have h3 : w ^ 3 = 1 := by push_cast at hw; linear_combination (w - 1) * hw
    calc w ^ 12 = (w ^ 3) ^ 4 := by ring
      _ = 1 := by rw [h3]; norm_num
  · -- `a = 0`: `w² = −1`
    have h2' : w ^ 2 = -1 := by push_cast at hw; linear_combination hw
    calc w ^ 12 = (w ^ 2) ^ 6 := by ring
      _ = 1 := by rw [h2']; norm_num
  · -- `a = 1`: `w³ = −1`
    have h3 : w ^ 3 = -1 := by push_cast at hw; linear_combination (w + 1) * hw
    calc w ^ 12 = (w ^ 3) ^ 4 := by ring
      _ = 1 := by rw [h3]; norm_num
  · -- `a = 2`: `w = 1`
    have : (w - 1) ^ 2 = 0 := by push_cast at hw; linear_combination hw
    have hw1 : w = 1 := by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this; linear_combination this
    rw [hw1]; norm_num

/-- The degree-two carrier `∏_i (1 − a_i p_i^{−s} + p_i^{−2s})`. -/
def degTwoCarrier {d : ℕ} (p : Fin d → ℕ) (a : Fin d → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (1 - (a i : ℂ) * (p i : ℂ) ^ (-s) + ((p i : ℂ) ^ (-s)) ^ 2)

/-- **Zeros lie on refined Euler columns.** Every zero `s` of an integral pure degree-two carrier
has `12 s` a zero of the Euler carrier `∏_i (1 − p_i^{−s})`. -/
theorem degTwoCarrier_zero_mem_column {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, 1 < p i)
    (a : Fin d → ℤ) (ha : ∀ i, |a i| ≤ 2) {s : ℂ} (hs : degTwoCarrier p a s = 0) :
    eulerCarrier p (12 * s) = 0 := by
  unfold degTwoCarrier at hs
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hs
  have hw := pow_twelve_eq_one_of_satake (ha i) (w := (p i : ℂ) ^ (-s)) (by linear_combination hi)
  unfold eulerCarrier
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have hp0 : (p i : ℂ) ≠ 0 := by exact_mod_cast (by have := hp i; omega : p i ≠ 0)
  rw [show -(12 * s) = (12 : ℕ) * -s by push_cast; ring, Complex.cpow_nat_mul, hw, sub_self]

/-- **Integral pure Euler factors collide or repel at polynomial scale.** For distinct primes
`p_i` and integers `|a_i| ≤ 2` there are `c, C > 0` such that distinct zeros of
`∏_i (1 − a_i p_i^{−s} + p_i^{−2s})` of height at most `T ≥ 1` are at distance `≥ c T^{−C}`. -/
theorem degTwoCarrier_collide_or_repel {d : ℕ} (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (a : Fin d → ℤ) (ha : ∀ i, |a i| ≤ 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ ρ ρ' : ℂ,
      degTwoCarrier p a ρ = 0 → degTwoCarrier p a ρ' = 0 → |ρ.im| ≤ T → |ρ'.im| ≤ T → ρ ≠ ρ' →
        c * T ^ (-C) ≤ ‖ρ - ρ'‖ := by
  obtain ⟨c, C, hc, hC, hrep⟩ := eulerCarrier_collide_or_repel p hp hprime
  refine ⟨c * (12 : ℝ) ^ (-C) / 12, C, by positivity, hC, fun T hT ρ ρ' hρ hρ' hT1 hT2 hne => ?_⟩
  have hp1 : ∀ i, 1 < p i := fun i => (hprime i).one_lt
  have h12 : (12 : ℂ) * ρ ≠ 12 * ρ' := fun h => hne (mul_left_cancel₀ (by norm_num) h)
  have him : ∀ z : ℂ, |((12 : ℂ) * z).im| = 12 * |z.im| := fun z => by
    rw [show ((12 : ℂ) * z).im = 12 * z.im by simp, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  have h := hrep (12 * T) (by linarith) (12 * ρ) (12 * ρ')
    (degTwoCarrier_zero_mem_column p hp1 a ha hρ) (degTwoCarrier_zero_mem_column p hp1 a ha hρ')
    (by rw [him]; linarith) (by rw [him]; linarith) h12
  rw [← mul_sub, norm_mul, show ‖(12 : ℂ)‖ = 12 by norm_num,
    Real.mul_rpow (by norm_num) (by linarith)] at h
  have : c * (12 : ℝ) ^ (-C) * T ^ (-C) ≤ 12 * ‖ρ - ρ'‖ := by linarith
  have h12' : c * (12 : ℝ) ^ (-C) / 12 * T ^ (-C) = (c * (12 : ℝ) ^ (-C) * T ^ (-C)) / 12 := by ring
  rw [h12']
  linarith

end GaloisForLFunctions.ArithmeticDiscreteness
