import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Purchase ratio and width cap of the trigonometric pole-purchase method

A nonnegative cosine polynomial `P(θ) = Σ_{k ≤ K} a_k cos kθ` has first coefficient at most twice
its constant term: integrating `(1 − cos θ)·P(θ) ≥ 0` over a period gives `2π a₀ − π a₁ ≥ 0`.  In de
la Vallée Poussin's coupled positivity the constant term multiplies the pole `1/(σ−1)` and the first
coefficient multiplies the share `1/(σ−β)` of a zero aligned with the evaluation point, so the method
purchases at most two units of zero share per unit of pole.

The second theorem is the resulting cap.  With height scale `L` (a constant multiple of `log t`),
`a₁ ≤ 2a₀`, and `S ≥ a₁` the total weight of the growth terms, the inequality
`a₁/(δ+η) ≤ a₀/δ + L·S` holds for every `δ > 0` as soon as `η ≥ (3 − 2√2)/(2L)`.  No choice of
nonnegative cosine polynomial can therefore certify a zero-free width beyond `(3 − 2√2)/(2L)`: the
inequality never fails, so it never excludes a zero at distance `η` from the line `Re s = 1`.  The
constant is the maximum of `u(1−u)/(1+u)`, attained at `u = √2 − 1`.
-/

open Real intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite cosine polynomial `Σ_{k ≤ K} a_k cos(kθ)`. -/
def cosinePolynomial (a : ℕ → ℝ) (K : ℕ) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), a k * Real.cos (k * θ)

theorem continuous_cosinePolynomial (a : ℕ → ℝ) (K : ℕ) : Continuous (cosinePolynomial a K) := by
  unfold cosinePolynomial
  refine continuous_finsetSum _ (fun k _ => continuous_const.mul ?_)
  exact Real.continuous_cos.comp (continuous_const.mul continuous_id)

/-- Interval integrability of one cosine mode with a constant coefficient. -/
theorem intervalIntegrable_const_mul_cos_nat_mul (c : ℝ) (k : ℕ) (x y : ℝ) :
    IntervalIntegrable (fun θ : ℝ => c * Real.cos ((k : ℝ) * θ)) MeasureTheory.volume x y :=
  ((continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)) :
    Continuous (fun θ : ℝ => c * Real.cos ((k : ℝ) * θ)))).intervalIntegrable x y

/-- Interval integrability of `cos θ` times one cosine mode with a constant coefficient. -/
theorem intervalIntegrable_const_mul_cos_mul_cos_nat_mul (c : ℝ) (k : ℕ) (x y : ℝ) :
    IntervalIntegrable (fun θ : ℝ => c * (Real.cos θ * Real.cos ((k : ℝ) * θ)))
      MeasureTheory.volume x y :=
  ((continuous_const.mul (Real.continuous_cos.mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))) :
    Continuous (fun θ : ℝ => c * (Real.cos θ * Real.cos ((k : ℝ) * θ))))).intervalIntegrable x y

/-- `∫₀^{2π} cos(kθ) dθ = 0` for `k ≥ 1`. -/
theorem integral_cos_nat_mul_eq_zero {k : ℕ} (hk : k ≠ 0) :
    ∫ θ in (0:ℝ)..(2 * π), Real.cos (k * θ) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hk', integral_cos]
  have h1 : Real.sin ((k : ℝ) * (2 * π)) = 0 := by
    have : (k : ℝ) * (2 * π) = ((2 * k : ℕ) : ℝ) * π := by push_cast; ring
    rw [this]
    exact Real.sin_nat_mul_pi _
  simp [h1]

/-- `∫₀^{2π} cos θ · cos(kθ) dθ` is `π` for `k = 1` and `0` otherwise. -/
theorem integral_cos_mul_cos_nat_mul (k : ℕ) :
    ∫ θ in (0:ℝ)..(2 * π), Real.cos θ * Real.cos (k * θ) = if k = 1 then π else 0 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [integral_cos]
    · rw [if_pos rfl]
      have hsq : ∫ θ in (0:ℝ)..(2 * π), Real.cos θ * Real.cos ((1 : ℕ) * θ)
          = ∫ θ in (0:ℝ)..(2 * π), Real.cos θ ^ 2 := by
        congr 1
        funext θ
        simp [pow_two]
      rw [hsq, integral_cos_sq]
      simp [Real.sin_two_pi]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hne : m + 2 ≠ 1 := by omega
    rw [if_neg hne]
    have hprod : ∀ θ : ℝ, Real.cos θ * Real.cos (((m + 2 : ℕ) : ℝ) * θ)
        = (Real.cos (((m + 1 : ℕ) : ℝ) * θ) + Real.cos (((m + 3 : ℕ) : ℝ) * θ)) / 2 := by
      intro θ
      have h1 : ((m + 1 : ℕ) : ℝ) * θ = ((m + 2 : ℕ) : ℝ) * θ - θ := by push_cast; ring
      have h3 : ((m + 3 : ℕ) : ℝ) * θ = ((m + 2 : ℕ) : ℝ) * θ + θ := by push_cast; ring
      rw [h1, h3, Real.cos_sub, Real.cos_add]
      ring
    have hint : ∀ n : ℕ, IntervalIntegrable (fun θ : ℝ => Real.cos ((n : ℝ) * θ)) MeasureTheory.volume
        (0:ℝ) (2 * π) := fun n =>
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    simp_rw [hprod]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint (m + 1)) (hint (m + 3)),
      integral_cos_nat_mul_eq_zero (by omega : m + 1 ≠ 0),
      integral_cos_nat_mul_eq_zero (by omega : m + 3 ≠ 0)]
    norm_num

/-- The mean of a cosine polynomial over a period is its constant term. -/
theorem integral_cosinePolynomial (a : ℕ → ℝ) (K : ℕ) :
    ∫ θ in (0:ℝ)..(2 * π), cosinePolynomial a K θ = 2 * π * a 0 := by
  unfold cosinePolynomial
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    intervalIntegrable_const_mul_cos_nat_mul (a k) k 0 (2 * π))]
  rw [Finset.sum_range_succ']
  have hzero : ∀ k ∈ Finset.range K,
      ∫ θ in (0:ℝ)..(2 * π), a (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ) = 0 := by
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_cos_nat_mul_eq_zero (by omega), mul_zero]
  rw [Finset.sum_eq_zero hzero, zero_add, intervalIntegral.integral_const_mul]
  simp
  ring

/-- The first Fourier coefficient of a cosine polynomial, read off against `cos θ`. -/
theorem integral_cos_mul_cosinePolynomial (a : ℕ → ℝ) {K : ℕ} (hK : 1 ≤ K) :
    ∫ θ in (0:ℝ)..(2 * π), Real.cos θ * cosinePolynomial a K θ = π * a 1 := by
  unfold cosinePolynomial
  have hrw : (fun θ : ℝ => Real.cos θ * ∑ k ∈ Finset.range (K + 1), a k * Real.cos (k * θ))
      = fun θ => ∑ k ∈ Finset.range (K + 1), a k * (Real.cos θ * Real.cos (k * θ)) := by
    funext θ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [hrw, intervalIntegral.integral_finsetSum (fun k _ =>
    intervalIntegrable_const_mul_cos_mul_cos_nat_mul (a k) k 0 (2 * π))]
  have hterm : ∀ k ∈ Finset.range (K + 1),
      ∫ θ in (0:ℝ)..(2 * π), a k * (Real.cos θ * Real.cos (k * θ))
        = a k * (if k = 1 then π else 0) := by
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_cos_mul_cos_nat_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single 1]
  · simp [mul_comm]
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Purchase ratio.**  A nonnegative cosine polynomial has `a₁ ≤ 2a₀`. -/
theorem cosinePolynomial_purchase_ratio_le_two {a : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hP : ∀ θ, 0 ≤ cosinePolynomial a K θ) : a 1 ≤ 2 * a 0 := by
  have hnonneg : 0 ≤ ∫ θ in (0:ℝ)..(2 * π), (1 - Real.cos θ) * cosinePolynomial a K θ := by
    refine intervalIntegral.integral_nonneg (by positivity) (fun θ _ => ?_)
    exact mul_nonneg (by linarith [Real.cos_le_one θ]) (hP θ)
  have hsplit : ∫ θ in (0:ℝ)..(2 * π), (1 - Real.cos θ) * cosinePolynomial a K θ
      = (∫ θ in (0:ℝ)..(2 * π), cosinePolynomial a K θ)
        - ∫ θ in (0:ℝ)..(2 * π), Real.cos θ * cosinePolynomial a K θ := by
    have hi1 : IntervalIntegrable (fun θ : ℝ => cosinePolynomial a K θ) MeasureTheory.volume 0 (2 * π) :=
      (continuous_cosinePolynomial a K).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun θ : ℝ => Real.cos θ * cosinePolynomial a K θ)
        MeasureTheory.volume 0 (2 * π) :=
      ((Real.continuous_cos.mul (continuous_cosinePolynomial a K) :
        Continuous (fun θ : ℝ => Real.cos θ * cosinePolynomial a K θ))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hi1 hi2]
    congr 1
    funext θ
    ring
  rw [hsplit, integral_cosinePolynomial, integral_cos_mul_cosinePolynomial a hK] at hnonneg
  nlinarith [Real.pi_pos]

/-- The scalar inequality behind the cap: `u − u² ≤ (3 − 2√2)(1 + u)` for every real `u`, with
equality at `u = √2 − 1`. -/
theorem purchase_key_inequality (u : ℝ) : u - u ^ 2 ≤ (3 - 2 * Real.sqrt 2) * (1 + u) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [sq_nonneg (u - (Real.sqrt 2 - 1)), h2]

theorem three_sub_two_sqrt_two_nonneg : 0 ≤ 3 - 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2, h2, sq_nonneg (Real.sqrt 2 - 3 / 2)]

/-- **Width cap of the pole-purchase method.**  With pole coefficient `a₀ > 0`, aligned share
coefficient `a₁ ≤ 2a₀`, total growth weight `S ≥ a₁`, height scale `L > 0`, and
`η ≥ (3 − 2√2)/(2L)`, the purchase inequality `a₁/(δ+η) ≤ a₀/δ + L·S` holds for every `δ > 0`.
The method therefore cannot exclude a zero at distance `η` from `Re s = 1`. -/
theorem purchase_width_cap {L a0 a1 S η δ : ℝ} (hL : 0 < L) (ha0 : 0 < a0)
    (ha1 : a1 ≤ 2 * a0) (hS0 : 0 ≤ S) (hS : a1 ≤ S)
    (hη : (3 - 2 * Real.sqrt 2) / (2 * L) ≤ η) (hδ : 0 < δ) :
    a1 / (δ + η) ≤ a0 / δ + L * S := by
  have hη0 : 0 ≤ η :=
    le_trans (div_nonneg three_sub_two_sqrt_two_nonneg (by positivity)) hη
  have hpos : 0 < δ + η := by linarith
  have h2L : 3 - 2 * Real.sqrt 2 ≤ 2 * L * η := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * L)).mp hη
    linarith
  have hkey := purchase_key_inequality (2 * L * δ)
  have hstep : 2 * L * δ - (2 * L * δ) ^ 2 ≤ 2 * L * η * (1 + 2 * L * δ) := by
    nlinarith [hkey, mul_le_mul_of_nonneg_right h2L (by positivity : (0:ℝ) ≤ 1 + 2 * L * δ)]
  have hmain : 2 * δ ≤ (δ + η) * (1 + 2 * L * δ) := by
    have h' : 2 * L * (δ - 2 * L * δ ^ 2) ≤ 2 * L * (η * (1 + 2 * L * δ)) := by
      nlinarith [hstep]
    have h'' := le_of_mul_le_mul_left h' (by positivity : (0:ℝ) < 2 * L)
    nlinarith [h'']
  rcases le_or_gt a1 0 with ha1n | ha1p
  · have hle : a1 / (δ + η) ≤ 0 := by
      rw [div_le_iff₀ hpos]
      linarith
    have : 0 ≤ a0 / δ + L * S := by positivity
    linarith
  · set x : ℝ := a1 / (2 * δ) with hx
    have hx0 : 0 < x := by positivity
    have hxa : x * (2 * δ) = a1 := div_mul_cancel₀ a1 (by positivity)
    have h1 : a1 / (δ + η) ≤ x + L * a1 := by
      rw [div_le_iff₀ hpos]
      nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hmain), hxa]
    have h2 : x ≤ a0 / δ := by
      rw [hx, ← div_div]
      exact div_le_div_of_nonneg_right (by linarith) hδ.le
    have h3 : L * a1 ≤ L * S := mul_le_mul_of_nonneg_left hS hL.le
    linarith

end

end GaloisForLFunctions.HTGeometry
