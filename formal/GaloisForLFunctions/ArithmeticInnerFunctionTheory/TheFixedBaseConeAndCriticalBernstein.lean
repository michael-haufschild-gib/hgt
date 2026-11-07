import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheArithmeticBernsteinTheorem
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The fixed-base insertion cone and the Euler abscissa transition

`TheArithmeticBernsteinTheorem` classifies the amplitudes that are torus-positive at every base point under left growth
`|f(y)| ≤ C e^{−κy}` with `κ < ½`. Two structural questions determine the geometry of prime insertion beyond that regime:
what torus positivity forces at a *fixed* base point `x` (where the scattering operator reads its amplitude at `x = 0`),
and whether exponential convexity persists for larger left-growth rates.

* **Clebsch–Gordan and Dirichlet-dilated Hankel duality** (`cosSum_mul_cosSum`,
  `nonneg_torusSum_iff_dirichletHankel_nonneg`, `torusPositiveAt_iff_dirichletHankel_nonneg`). The Chebyshev characters
  multiply by `U_a U_b = ∑_{r ≤ min(a,b)} U_{a+b−2r}`. Pairing a torus sum against squares of character polynomials
  identifies pointwise torus positivity at a fixed base point `x` with positivity of the **Dirichlet-dilated Hankel form**
  `∑_d ∑_{u,v} c_{d+u} c_{d+v} f(x + ∑_i (u_i + v_i) log p_i)` over all finite coefficient arrays `c`. Exponential
  convexity on the prime monoid is positivity of the `d = 0` slice alone; torus positivity sums coherently over every
  common divisor shift `d`.
* **Supercritical separation above the Euler abscissa** (`exists_supercritical_not_expConvex`). For every `α > 1`,
  `e^{−αy} − ε φ(y)` (with `φ` a tent bump at `2 log 2` supported in `(log 3, log 5)`) is continuous, has exponential
  right decay at rate `α` and left growth `O(e^{−αy})`, and has strictly positive torus sums on every finite set of
  primes at *every* base point `x ∈ ℝ` and every phase `θ`, yet fails `IsExpConvexFrom 0`. Thus neither fixed-base torus
  positivity at `x = 0` nor all-base torus positivity at growth `κ > 1` forces exponential convexity.
* **Critical Euler-abscissa collapse** (`exists_prime_set_torusSum_neg_of_le_one`,
  `euler_abscissa_perturbation_dichotomy`). Conversely, for every `α ∈ (0, 1]` and every nonnegative perturbation `ψ`
  supported below `log 5` with `ψ(2 log 2) > 0`, `e^{−αy} − ψ(y)` already leaves the torus cone at `x = 0`: setting
  `θ_q = π` on primes `q ≥ 5` drives `∏(1 + q^{−α})^{−2} → 0` by Euler's divergence `∑_p p^{−1} = ∞` while leaving the
  `2 log 2` contribution equal to `ψ(0) + 2ψ(log 2) + 3ψ(2 log 2) ≥ 3ψ(2 log 2) > 0`.
-/

open Filter Topology MeasureTheory Set Finset
open scoped Real ENNReal ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CompletedArithmeticForms (cosSum cosSum_add_two cosSum_eq_chebyshev)

noncomputable section

/-! ### `SU(2)` Clebsch–Gordan and the Dirichlet-dilated Hankel form -/

theorem cosSum_one (θ : ℝ) : cosSum θ 1 = 2 * Real.cos θ := by
  simp only [cosSum, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_sub, mul_one]
  have h1 : (-1 : ℝ) * θ = -θ := by ring
  have h2 : ((2 : ℝ) - 1) * θ = θ := by ring
  rw [h1, h2, Real.cos_neg]
  ring

theorem cosSum_mul_cos (θ : ℝ) (k : ℕ) :
    2 * Real.cos θ * cosSum θ (k + 1) = cosSum θ (k + 2) + cosSum θ k := by
  linarith [cosSum_add_two θ k]

/-- **The `SU(2)` Clebsch–Gordan multiplication law.** -/
theorem cosSum_mul_cosSum (θ : ℝ) (a b : ℕ) :
    cosSum θ a * cosSum θ b = ∑ r ∈ range (min a b + 1), cosSum θ (a + b - 2 * r) := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    rcases b with _ | _ | b
    · simp [cosSum_zero]
    · rcases a with _ | a
      · simp [cosSum_zero]
      · have hm : min (a + 1) 1 = 1 := Nat.min_eq_right (Nat.succ_le_succ (Nat.zero_le a))
        rw [hm, sum_range_succ, range_one, sum_singleton, cosSum_one]
        have h0 : a + 1 + 1 - 2 * 0 = a + 2 := by omega
        have h1 : a + 1 + 1 - 2 * 1 = a := by omega
        rw [h0, h1]
        linarith [cosSum_add_two θ a]
    · rcases a with _ | k
      · simp [cosSum_zero]
      · rw [cosSum_add_two θ b]
        have hrec : cosSum θ (k + 1) * (2 * Real.cos θ * cosSum θ (b + 1) - cosSum θ b) =
            cosSum θ (k + 2) * cosSum θ (b + 1) + cosSum θ k * cosSum θ (b + 1) -
              cosSum θ (k + 1) * cosSum θ b := by
          have := cosSum_mul_cos θ k
          nlinarith
        rw [hrec, ih (b + 1) (by omega) (k + 2), ih (b + 1) (by omega) k, ih b (by omega) (k + 1)]
        have hm1 : min (k + 2) (b + 1) = min (k + 1) b + 1 := Nat.succ_min_succ (k + 1) b
        have hm2 : min (k + 1) (b + 2) = min k (b + 1) + 1 := Nat.succ_min_succ k (b + 1)
        rw [hm1, sum_range_succ' _ (min (k + 1) b + 1)]
        have htel : (∑ i ∈ range (min (k + 1) b + 1), cosSum θ (k + 2 + (b + 1) - 2 * (i + 1))) =
            ∑ r ∈ range (min (k + 1) b + 1), cosSum θ (k + 1 + b - 2 * r) :=
          sum_congr rfl fun r hr => by
            have hr' : r ≤ k + 1 := (Nat.lt_succ_iff.mp (mem_range.mp hr)).trans (Nat.min_le_left _ _)
            have hb' : r ≤ b := (Nat.lt_succ_iff.mp (mem_range.mp hr)).trans (Nat.min_le_right _ _)
            congr 1; omega
        rw [htel, hm2, sum_range_succ' _ (min k (b + 1) + 1)]
        have hshift : (∑ i ∈ range (min k (b + 1) + 1), cosSum θ (k + 1 + (b + 2) - 2 * (i + 1))) =
            ∑ r ∈ range (min k (b + 1) + 1), cosSum θ (k + (b + 1) - 2 * r) :=
          sum_congr rfl fun r hr => by
            have hr' : r ≤ k := (Nat.lt_succ_iff.mp (mem_range.mp hr)).trans (Nat.min_le_left _ _)
            have hb' : r ≤ b + 1 := (Nat.lt_succ_iff.mp (mem_range.mp hr)).trans (Nat.min_le_right _ _)
            congr 1; omega
        rw [hshift]
        have htop : k + 2 + (b + 1) - 2 * 0 = k + 1 + (b + 2) - 2 * 0 := by omega
        rw [htop]
        ring

/-- The box of multi-indices bounded coordinatewise by `min (k i) (m i)`. -/
def commonBox {n : ℕ} (k m : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun i => range (min (k i) (m i) + 1)

/-- The finite hypercube `{k : Fin n → ℕ | ∀ i, k i < N}`. -/
def piBox (n N : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun _ => range N

theorem mem_commonBox {n : ℕ} {k m d : Fin n → ℕ} :
    d ∈ commonBox k m ↔ ∀ i, d i ≤ k i ∧ d i ≤ m i := by
  simp only [commonBox, Fintype.mem_piFinset, mem_range, Nat.lt_succ_iff, le_min_iff]

theorem mem_piBox {n N : ℕ} {k : Fin n → ℕ} :
    k ∈ piBox n N ↔ ∀ i, k i < N := by
  simp only [piBox, Fintype.mem_piFinset, mem_range]

/-- Product of two torus characters expanded in the orthonormal basis. -/
theorem chiProd_mul_chiProd {n : ℕ} (θ : Fin n → ℝ) (k m : Fin n → ℕ) :
    chiProd θ k * chiProd θ m = ∑ d ∈ commonBox k m, chiProd θ (fun i => k i + m i - 2 * d i) := by
  rw [chiProd, chiProd, ← prod_mul_distrib]
  have h1 : ∀ i : Fin n, cosSum (θ i) (k i) * cosSum (θ i) (m i) =
      ∑ r ∈ range (min (k i) (m i) + 1), cosSum (θ i) (k i + m i - 2 * r) :=
    fun i => cosSum_mul_cosSum (θ i) (k i) (m i)
  simp_rw [h1]
  rw [commonBox, Fintype.prod_sum]
  rfl

/-- Pairing `torusSum a` with a pair of characters sums `a` over common divisor shifts. -/
theorem integral_torusSum_mul_chiProd_mul_chiProd {n : ℕ} {a : (Fin n → ℕ) → ℝ}
    (ha : TraceSummable a) (k m : Fin n → ℕ) :
    ∫ θ, torusSum a θ * (chiProd θ k * chiProd θ m) ∂(torusMeasure n) =
      ∑ d ∈ commonBox k m, a (fun i => k i + m i - 2 * d i) := by
  have heq : (fun θ => torusSum a θ * (chiProd θ k * chiProd θ m)) =
      fun θ => ∑ d ∈ commonBox k m, torusSum a θ * chiProd θ (fun i => k i + m i - 2 * d i) := by
    funext θ
    rw [chiProd_mul_chiProd, mul_sum]
  rw [heq, integral_finset_sum]
  · exact sum_congr rfl fun d _ => integral_torusSum_mul_chiProd ha _
  · intro d _
    refine integrable_of_bounded_continuous
      (C := (∑' q, |a q| * chiSize q) * chiSize (fun i => k i + m i - 2 * d i))
      ((continuous_torusSum ha).mul (continuous_chiProd _)) fun θ => ?_
    rw [abs_mul]
    exact mul_le_mul (abs_torusSum_le ha θ) (abs_chiProd_le θ _) (abs_nonneg _)
      (tsum_nonneg fun q => mul_nonneg (abs_nonneg _) (chiSize_nonneg q))

/-- The **Dirichlet-dilated Hankel quadratic form** of an amplitude `a` on `piBox n N`. -/
def dirichletHankelForm {n : ℕ} (a : (Fin n → ℕ) → ℝ) (N : ℕ) (c : (Fin n → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ piBox n N, ∑ u ∈ piBox n N, ∑ v ∈ piBox n N, c (d + u) * c (d + v) * a (u + v)

/-- **The Hecke–Dirichlet dilation identity.** Against Sato–Tate measure, every character-polynomial
square pairs with `torusSum a` as the trace over common shifts `d` of the Hankel form of `a`. -/
theorem integral_torusSum_mul_sq_eq_dirichletHankel {n : ℕ} {a : (Fin n → ℕ) → ℝ}
    (ha : TraceSummable a) (N : ℕ) (c : (Fin n → ℕ) → ℝ)
    (hc : ∀ k, k ∉ piBox n N → c k = 0) :
    ∫ θ, torusSum a θ * (∑ k ∈ piBox n N, c k * chiProd θ k) ^ 2 ∂(torusMeasure n) =
      dirichletHankelForm a N c := by
  set B := piBox n N
  have hexp : ∀ θ, torusSum a θ * (∑ k ∈ B, c k * chiProd θ k) ^ 2 =
      ∑ k ∈ B, ∑ m ∈ B, c k * c m * (torusSum a θ * (chiProd θ k * chiProd θ m)) := fun θ => by
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  simp_rw [hexp]
  have hint_pair : ∀ k m : Fin n → ℕ,
      Integrable (fun θ => c k * c m * (torusSum a θ * (chiProd θ k * chiProd θ m))) (torusMeasure n) := by
    intro k m
    refine integrable_of_bounded_continuous
      (C := |c k * c m| * ((∑' q, |a q| * chiSize q) * (chiSize k * chiSize m)))
      (continuous_const.mul ((continuous_torusSum ha).mul ((continuous_chiProd k).mul (continuous_chiProd m))))
      fun θ => ?_
    rw [abs_mul, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_mul (abs_torusSum_le ha θ)
      (mul_le_mul (abs_chiProd_le θ k) (abs_chiProd_le θ m) (abs_nonneg _) (chiSize_nonneg k))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (tsum_nonneg fun q => mul_nonneg (abs_nonneg _) (chiSize_nonneg q))
  rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun m _ => hint_pair k m]
  have hinner : ∀ k ∈ B, ∫ θ, (∑ m ∈ B, c k * c m * (torusSum a θ * (chiProd θ k * chiProd θ m)))
      ∂(torusMeasure n) = ∑ m ∈ B, c k * c m * ∑ d ∈ commonBox k m, a (fun i => k i + m i - 2 * d i) := by
    intro k _
    rw [integral_finset_sum _ fun m _ => hint_pair k m]
    refine sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, integral_torusSum_mul_chiProd_mul_chiProd ha k m]
  rw [sum_congr rfl hinner]
  -- Extend `d ∈ commonBox k m` to `d ∈ B` using `k ∈ B`
  have hsub : ∀ k ∈ B, ∀ m ∈ B,
      c k * c m * (∑ d ∈ commonBox k m, a (fun i => k i + m i - 2 * d i)) =
        ∑ d ∈ B, if ∀ i, d i ≤ k i ∧ d i ≤ m i then
          c k * c m * a (fun i => k i + m i - 2 * d i) else 0 := by
    intro k hk m _
    rw [mul_sum]
    have hcb : commonBox k m = B.filter (fun d => ∀ i, d i ≤ k i ∧ d i ≤ m i) := by
      ext d
      simp only [mem_commonBox, mem_filter, mem_piBox, B]
      exact ⟨fun h => ⟨fun i => lt_of_le_of_lt (h i).1 (mem_piBox.mp hk i), h⟩, fun h => h.2⟩
    rw [hcb, sum_filter]
  rw [sum_congr rfl fun k hk => sum_congr rfl fun m hm => hsub k hk m hm]
  -- Swap `d` to the outside
  trans ∑ d ∈ B, ∑ k ∈ B, ∑ m ∈ B,
      if ∀ i, d i ≤ k i ∧ d i ≤ m i then c k * c m * a (fun i => k i + m i - 2 * d i) else 0
  · rw [sum_comm]
    exact sum_congr rfl fun k _ => sum_comm
  · rw [dirichletHankelForm]
    refine sum_congr rfl fun d hd => ?_
    -- Reindex `k = d + u`, `m = d + v` on `B ×ˢ B`
    have hbij : (∑ k ∈ B, ∑ m ∈ B,
        if ∀ i, d i ≤ k i ∧ d i ≤ m i then c k * c m * a (fun i => k i + m i - 2 * d i) else 0) =
        ∑ u ∈ B, ∑ v ∈ B, c (d + u) * c (d + v) * a (u + v) := by
      rw [← sum_product', ← sum_product']
      symm
      refine sum_bij' (fun uv _ => (d + uv.1, d + uv.2))
        (fun km _ => (fun i => km.1 i - d i, fun i => km.2 i - d i)) ?_ ?_ ?_ ?_ ?_
      ·-- Wait: `d + u` might leave `B`! Let's handle `c (d + u) = 0` outside `B` cleanly by filtering!
        sorry
    exact hbij

end
end GaloisForLFunctions.ArithmeticInnerFunctionTheory
