import GaloisForLFunctions.FiniteFreeProbability.AdditiveConvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# The degree-three test of the finite free route

On centered cubics `X³ − 3sX − 2t` the finite free convolution `⊞₃` simply adds the parameters:
`(s₁, t₁) ⊞₃ (s₂, t₂) = (s₁ + s₂, t₁ + t₂)`. The cubic with a double root,
`(X + a)²(X − 2a) = X³ − 3a²X − 2a³`, has parameters `(a², a³)`.

**Theorem.** Every centered cubic with `s ≥ 0` and `|t| ≤ s^{3/2}` (the real-rooted range) is the
`⊞₃`-convolution of two double-root cubics: take `a = √s cos θ`, `b = √s sin θ` with
`cos³θ + sin³θ = t/s^{3/2}` (intermediate values on `[−π/2, 0]`).

Double-root cubics carry no Gaussian component (any backward heat splits the double root off the
line), so semicircle-free factorizations exist for every real-rooted cubic: the degree-three test
of the finite free route is satisfied by every real-rooted Jensen cubic and cannot discriminate.
The source-faithful structure is multiplicative (Gamma ⊠ theta), not additive.
-/

open Polynomial

namespace FiniteFreeProbability

noncomputable section

/-- The centered cubic `X³ − 3sX − 2t`. -/
def centeredCubic (s t : ℝ) : ℝ[X] := X ^ 3 - C (3 * s) * X - C (2 * t)

theorem coeff_centeredCubic (s t : ℝ) (k : ℕ) :
    (centeredCubic s t).coeff k =
      if k = 3 then 1 else if k = 1 then -(3 * s) else if k = 0 then -(2 * t) else 0 := by
  simp only [centeredCubic, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  rcases k with _ | _ | _ | _ | k <;> simp

/-- **`⊞₃` adds centered parameters.** -/
theorem ffConv_centeredCubic (s₁ t₁ s₂ t₂ : ℝ) :
    ffConv 3 (centeredCubic s₁ t₁) (centeredCubic s₂ t₂) = centeredCubic (s₁ + s₂) (t₁ + t₂) := by
  ext k
  rw [ffConv, finsetSum_coeff]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, coeff_C_mul,
    coeff_iterate_derivative, coeff_centeredCubic, nsmul_eq_mul]
  rcases k with _ | _ | _ | _ | k
  · norm_num [Nat.factorial, Nat.descFactorial]; ring
  · norm_num [Nat.factorial, Nat.descFactorial]; ring
  · norm_num [Nat.factorial, Nat.descFactorial]
  · norm_num [Nat.factorial, Nat.descFactorial]
  · simp [show k + 4 ≠ 3 by omega, show k + 1 + 4 ≠ 3 by omega, show k + 2 + 4 ≠ 3 by omega]

/-- The double-root cubic `(X + a)²(X − 2a)` is centered with parameters `(a², a³)`. -/
theorem doubleRootCubic_eq (a : ℝ) :
    (X + C a) ^ 2 * (X - C (2 * a)) = centeredCubic (a ^ 2) (a ^ 3) := by
  simp only [centeredCubic, map_mul, map_pow, map_ofNat]
  ring

/-- **Semicircle-free factorization of every real-rooted centered cubic.** -/
theorem exists_doubleRoot_factorization {s t : ℝ} (hs : 0 ≤ s)
    (ht : |t| ≤ Real.sqrt s ^ 3) :
    ∃ a b : ℝ, centeredCubic s t =
      ffConv 3 ((X + C a) ^ 2 * (X - C (2 * a))) ((X + C b) ^ 2 * (X - C (2 * b))) := by
  set r := Real.sqrt s
  have hr : 0 ≤ r := Real.sqrt_nonneg s
  have hr2 : r ^ 2 = s := Real.sq_sqrt hs
  set f : ℝ → ℝ := fun θ => r ^ 3 * (Real.cos θ ^ 3 + Real.sin θ ^ 3)
  have hcont : ContinuousOn f (Set.Icc (-(Real.pi / 2)) 0) :=
    (continuous_const.mul ((Real.continuous_cos.pow 3).add (Real.continuous_sin.pow 3))).continuousOn
  have hlo : f (-(Real.pi / 2)) = -r ^ 3 := by
    simp only [f, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hhi : f 0 = r ^ 3 := by simp [f]
  obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc (by linarith [Real.pi_pos]) hcont
    (show t ∈ Set.Icc (f (-(Real.pi / 2))) (f 0) by
      rw [hlo, hhi]; exact ⟨by linarith [neg_abs_le t], le_trans (le_abs_self t) ht⟩)
  refine ⟨r * Real.cos θ, r * Real.sin θ, ?_⟩
  rw [doubleRootCubic_eq, doubleRootCubic_eq, ffConv_centeredCubic]
  congr 1
  · rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one, hr2]
  · rw [← hθ]; simp only [f]; ring

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.exists_doubleRoot_factorization
