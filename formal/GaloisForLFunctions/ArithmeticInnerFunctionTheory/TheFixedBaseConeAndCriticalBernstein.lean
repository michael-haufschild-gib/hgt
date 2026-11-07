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
        rw [hm, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, cosSum_one]
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
          calc cosSum θ (k + 1) * (2 * Real.cos θ * cosSum θ (b + 1) - cosSum θ b)
              = (2 * Real.cos θ * cosSum θ (k + 1)) * cosSum θ (b + 1) -
                  cosSum θ (k + 1) * cosSum θ b := by ring
            _ = _ := by rw [cosSum_mul_cos]; ring
        rw [hrec, ih (b + 1) (by omega) (k + 2), ih (b + 1) (by omega) k, ih b (by omega) (k + 1)]
        have hm1 : min (k + 2) (b + 1) = min (k + 1) b + 1 := Nat.succ_min_succ (k + 1) b
        have hm2 : min (k + 1) (b + 2) = min k (b + 1) + 1 := Nat.succ_min_succ k (b + 1)
        rw [hm1, Finset.sum_range_succ' _ (min (k + 1) b + 1)]
        have htel : (∑ i ∈ range (min (k + 1) b + 1), cosSum θ (k + 2 + (b + 1) - 2 * (i + 1))) =
            ∑ r ∈ range (min (k + 1) b + 1), cosSum θ (k + 1 + b - 2 * r) :=
          sum_congr rfl fun r hr => by
            have hr' : r ≤ k + 1 :=
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)).trans (Nat.min_le_left _ _)
            have hb' : r ≤ b :=
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)).trans (Nat.min_le_right _ _)
            congr 1; omega
        rw [htel, hm2, Finset.sum_range_succ' _ (min k (b + 1) + 1)]
        have hshift : (∑ i ∈ range (min k (b + 1) + 1), cosSum θ (k + 1 + (b + 2) - 2 * (i + 1))) =
            ∑ r ∈ range (min k (b + 1) + 1), cosSum θ (k + (b + 1) - 2 * r) :=
          sum_congr rfl fun r hr => by
            have hr' : r ≤ k :=
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)).trans (Nat.min_le_left _ _)
            have hb' : r ≤ b + 1 :=
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)).trans (Nat.min_le_right _ _)
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
  simp only [commonBox, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff, le_min_iff]

theorem mem_piBox {n N : ℕ} {k : Fin n → ℕ} :
    k ∈ piBox n N ↔ ∀ i, k i < N := by
  simp only [piBox, Fintype.mem_piFinset, Finset.mem_range]

/-- Product of two torus characters expanded in the orthonormal basis. -/
theorem chiProd_mul_chiProd {n : ℕ} (θ : Fin n → ℝ) (k m : Fin n → ℕ) :
    chiProd θ k * chiProd θ m = ∑ d ∈ commonBox k m, chiProd θ (fun i => k i + m i - 2 * d i) := by
  classical
  rw [chiProd, chiProd, ← prod_mul_distrib]
  have h1 : ∀ i : Fin n, cosSum (θ i) (k i) * cosSum (θ i) (m i) =
      ∑ r ∈ range (min (k i) (m i) + 1), cosSum (θ i) (k i + m i - 2 * r) :=
    fun i => cosSum_mul_cosSum (θ i) (k i) (m i)
  simp_rw [h1]
  rw [commonBox, Finset.prod_univ_sum (fun i => range (min (k i) (m i) + 1))
    (fun i r => cosSum (θ i) (k i + m i - 2 * r))]
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
  rw [heq, integral_finsetSum]
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
  classical
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
      (C := (|c k| * |c m|) * ((∑' q, |a q| * chiSize q) * (chiSize k * chiSize m)))
      (continuous_const.mul ((continuous_torusSum ha).mul ((continuous_chiProd k).mul (continuous_chiProd m))))
      fun θ => ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact mul_le_mul (abs_torusSum_le ha θ)
      (mul_le_mul (abs_chiProd_le θ k) (abs_chiProd_le θ m) (abs_nonneg _) (chiSize_nonneg k))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (tsum_nonneg fun q => mul_nonneg (abs_nonneg _) (chiSize_nonneg q))
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun m _ => hint_pair k m]
  have hinner : ∀ k ∈ B, ∫ θ, (∑ m ∈ B, c k * c m * (torusSum a θ * (chiProd θ k * chiProd θ m)))
      ∂(torusMeasure n) = ∑ m ∈ B, c k * c m * ∑ d ∈ commonBox k m, a (fun i => k i + m i - 2 * d i) := by
    intro k _
    rw [integral_finsetSum _ fun m _ => hint_pair k m]
    refine sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, integral_torusSum_mul_chiProd_mul_chiProd ha k m]
  rw [sum_congr rfl hinner]
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
  have hswap : (∑ k ∈ B, ∑ m ∈ B, ∑ d ∈ B,
      if ∀ i, d i ≤ k i ∧ d i ≤ m i then c k * c m * a (fun i => k i + m i - 2 * d i) else 0) =
      ∑ d ∈ B, ∑ k ∈ B, ∑ m ∈ B,
        if ∀ i, d i ≤ k i ∧ d i ≤ m i then c k * c m * a (fun i => k i + m i - 2 * d i) else 0 :=
    (sum_congr rfl fun _ _ => sum_comm).trans sum_comm
  rw [hswap, dirichletHankelForm]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_product', ← sum_product', ← sum_filter]
  set S_d := (B ×ˢ B).filter (fun uv => d + uv.1 ∈ B ∧ d + uv.2 ∈ B)
  set T_d := (B ×ˢ B).filter (fun km => ∀ i, d i ≤ km.1 i ∧ d i ≤ km.2 i)
  have hrhs : (∑ uv ∈ B ×ˢ B, c (d + uv.1) * c (d + uv.2) * a (uv.1 + uv.2)) =
      ∑ uv ∈ S_d, c (d + uv.1) * c (d + uv.2) * a (uv.1 + uv.2) := by
    refine (sum_subset (filter_subset _ _) fun uv huv hnot => ?_).symm
    rw [mem_filter] at hnot
    have hnot' : ¬(d + uv.1 ∈ B ∧ d + uv.2 ∈ B) := fun h => hnot ⟨huv, h⟩
    by_cases h1 : d + uv.1 ∈ B
    · have h2 : d + uv.2 ∉ B := fun h2 => hnot' ⟨h1, h2⟩
      rw [hc _ h2, mul_zero, zero_mul]
    · rw [hc _ h1, zero_mul, zero_mul]
  rw [hrhs]
  symm
  refine sum_nbij' (fun uv => (d + uv.1, d + uv.2))
    (fun km => (fun i => km.1 i - d i, fun i => km.2 i - d i)) ?_ ?_ ?_ ?_ ?_
  · intro uv huv
    obtain ⟨_, huB, hvB⟩ := mem_filter.mp huv
    refine mem_filter.mpr ⟨mem_product.mpr ⟨huB, hvB⟩, fun i => ?_⟩
    simp only [Pi.add_apply]
    omega
  · intro km hkm
    obtain ⟨hkmB, hle⟩ := mem_filter.mp hkm
    obtain ⟨hkB, hmB⟩ := mem_product.mp hkmB
    have h1 : (d + fun i => km.1 i - d i) = km.1 := funext fun i => by
      have := (hle i).1; simp only [Pi.add_apply]; omega
    have h2 : (d + fun i => km.2 i - d i) = km.2 := funext fun i => by
      have := (hle i).2; simp only [Pi.add_apply]; omega
    refine mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [mem_piBox] at hkB ⊢; intro i; exact lt_of_le_of_lt (Nat.sub_le _ _) (hkB i)
    · rw [mem_piBox] at hmB ⊢; intro i; exact lt_of_le_of_lt (Nat.sub_le _ _) (hmB i)
    · rwa [h1]
    · rwa [h2]
  · intro uv _
    ext i <;> simp only [Pi.add_apply] <;> omega
  · intro km hkm
    obtain ⟨_, hle⟩ := mem_filter.mp hkm
    ext i
    · have := (hle i).1; simp only [Pi.add_apply]; omega
    · have := (hle i).2; simp only [Pi.add_apply]; omega
  · intro uv _
    have he : (fun i => (d + uv.1) i + (d + uv.2) i - 2 * d i) = uv.1 + uv.2 := by
      funext i; simp only [Pi.add_apply]; omega
    rw [he]

/-! ### Fixed-base duality on the Sato–Tate torus -/

theorem cosSum_eq_of_cos_eq {θ φ : ℝ} (h : Real.cos θ = Real.cos φ) (k : ℕ) :
    cosSum θ k = cosSum φ k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rcases k with _ | _ | k
    · simp [cosSum_zero]
    · rw [cosSum_one, cosSum_one, h]
    · rw [cosSum_add_two, cosSum_add_two, h, ih (k + 1) (by omega), ih k (by omega)]

theorem chiProd_eq_of_cos_eq {n : ℕ} {θ φ : Fin n → ℝ} (h : ∀ i, Real.cos (θ i) = Real.cos (φ i))
    (k : Fin n → ℕ) : chiProd θ k = chiProd φ k :=
  prod_congr rfl fun i _ => cosSum_eq_of_cos_eq (h i) (k i)

theorem torusSum_eq_of_cos_eq {n : ℕ} (a : (Fin n → ℕ) → ℝ) {θ φ : Fin n → ℝ}
    (h : ∀ i, Real.cos (θ i) = Real.cos (φ i)) : torusSum a θ = torusSum a φ := by
  simp only [torusSum, chiProd_eq_of_cos_eq h]

/-- Multiplication by `cos θ` preserves finite linear combinations of `cosSum θ k`. -/
private theorem exists_cosSum_mul_cos {N : ℕ} (α : ℕ → ℝ) :
    ∃ β : ℕ → ℝ, ∀ θ : ℝ, Real.cos θ * (∑ k ∈ range N, α k * cosSum θ k) =
      ∑ k ∈ range (N + 1), β k * cosSum θ k := by
  induction N with
  | zero =>
    refine ⟨fun _ => 0, fun θ => by simp⟩
  | succ m ih =>
    obtain ⟨β₀, hβ₀⟩ := ih
    rcases m with _ | j
    · refine ⟨fun k => if k = 1 then α 0 / 2 else 0, fun θ => ?_⟩
      rw [Finset.range_one, Finset.sum_singleton, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton]
      norm_num [cosSum_zero, cosSum_one]
      ring
    · refine ⟨fun k => (if k < j + 2 then β₀ k else 0) +
          (if k = j + 2 then α (j + 1) / 2 else 0) +
          (if k = j then α (j + 1) / 2 else 0), fun θ => ?_⟩
      rw [Finset.sum_range_succ _ (j + 1), mul_add, hβ₀ θ]
      have hterm : Real.cos θ * (α (j + 1) * cosSum θ (j + 1)) =
          (α (j + 1) / 2) * cosSum θ (j + 2) + (α (j + 1) / 2) * cosSum θ j := by
        calc Real.cos θ * (α (j + 1) * cosSum θ (j + 1))
            = (α (j + 1) / 2) * (2 * Real.cos θ * cosSum θ (j + 1)) := by ring
          _ = (α (j + 1) / 2) * cosSum θ (j + 2) + (α (j + 1) / 2) * cosSum θ j := by
              rw [cosSum_mul_cos]; ring
      rw [hterm]
      simp only [add_mul, sum_add_distrib]
      have h1 : (∑ x ∈ range (j + 3), (if x < j + 2 then β₀ x else 0) * cosSum θ x) =
          ∑ k ∈ range (j + 2), β₀ k * cosSum θ k := by
        rw [Finset.sum_range_succ _ (j + 2)]
        simp only [lt_self_iff_false, ↓reduceIte, zero_mul, add_zero]
        exact sum_congr rfl fun k hk => by rw [if_pos (Finset.mem_range.mp hk)]
      have h2 : (∑ x ∈ range (j + 3), (if x = j + 2 then α (j + 1) / 2 else 0) * cosSum θ x) =
          (α (j + 1) / 2) * cosSum θ (j + 2) := by
        rw [sum_eq_single (j + 2)]
        · simp
        · intro k _ hk; simp [hk]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      have h3 : (∑ x ∈ range (j + 3), (if x = j then α (j + 1) / 2 else 0) * cosSum θ x) =
          (α (j + 1) / 2) * cosSum θ j := by
        rw [sum_eq_single j]
        · simp
        · intro k _ hk; simp [hk]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      rw [h1, h2, h3]
      ring

/-- Univariate peaking factor `(1 − (cos θ − t₀)²/4)^m` expanded in `cosSum`. -/
private theorem exists_cosSum_peak (t₀ : ℝ) (m : ℕ) :
    ∃ (N : ℕ) (α : ℕ → ℝ), ∀ θ : ℝ,
      (1 - (Real.cos θ - t₀) ^ 2 / 4) ^ m = ∑ k ∈ range N, α k * cosSum θ k := by
  induction m with
  | zero =>
    refine ⟨1, fun _ => 1, fun θ => by simp [cosSum_zero]⟩
  | succ m ih =>
    obtain ⟨N, α, hα⟩ := ih
    obtain ⟨β₁, hβ₁⟩ := exists_cosSum_mul_cos α
    obtain ⟨β₂, hβ₂⟩ := exists_cosSum_mul_cos β₁
    set c₀ : ℝ := 1 - t₀ ^ 2 / 4
    set c₁ : ℝ := t₀ / 2
    set c₂ : ℝ := -(1 / 4 : ℝ)
    refine ⟨N + 2, fun k =>
      c₀ * (if k < N then α k else 0) + c₁ * (if k < N + 1 then β₁ k else 0) + c₂ * β₂ k,
      fun θ => ?_⟩
    rw [pow_succ', hα θ]
    set S := ∑ k ∈ range N, α k * cosSum θ k
    have hpoly : (1 - (Real.cos θ - t₀) ^ 2 / 4) * S =
        c₀ * S + c₁ * (Real.cos θ * S) + c₂ * (Real.cos θ * (Real.cos θ * S)) := by
      simp only [c₀, c₁, c₂]; ring
    rw [hpoly, hβ₁ θ, hβ₂ θ]
    simp only [add_mul, sum_add_distrib]
    have hpad0 : (∑ k ∈ range (N + 2), c₀ * (if k < N then α k else 0) * cosSum θ k) = c₀ * S := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [show ¬(N + 1 < N) by omega, show ¬(N < N) by omega, ↓reduceIte, mul_zero,
        zero_mul, add_zero]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (Finset.mem_range.mp hk)]
      ring
    have hpad1 : (∑ k ∈ range (N + 2), c₁ * (if k < N + 1 then β₁ k else 0) * cosSum θ k) =
        c₁ * ∑ k ∈ range (N + 1), β₁ k * cosSum θ k := by
      rw [Finset.sum_range_succ]
      simp only [lt_self_iff_false, ↓reduceIte, mul_zero, zero_mul, add_zero]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (Finset.mem_range.mp hk)]
      ring
    have hpad2 : (∑ k ∈ range (N + 2), c₂ * β₂ k * cosSum θ k) =
        c₂ * ∑ k ∈ range (N + 2), β₂ k * cosSum θ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hpad0, hpad1, hpad2]

/-- Multivariate peaking polynomial on the torus expanded in `piBox n N`. -/
private theorem exists_chiProd_peak {n : ℕ} (φ₀ : Fin n → ℝ) (m : ℕ) :
    ∃ (N : ℕ) (c : (Fin n → ℕ) → ℝ), (∀ k, k ∉ piBox n N → c k = 0) ∧
      ∀ θ : Fin n → ℝ, (∏ i : Fin n, (1 - (Real.cos (θ i) - Real.cos (φ₀ i)) ^ 2 / 4) ^ m) =
        ∑ k ∈ piBox n N, c k * chiProd θ k := by
  classical
  choose N_i α_i hα_i using fun i : Fin n => exists_cosSum_peak (Real.cos (φ₀ i)) m
  set N := univ.sup N_i
  let β : Fin n → ℕ → ℝ := fun i k => if k < N_i i then α_i i k else 0
  have hβ : ∀ (i : Fin n) (θ : ℝ),
      (1 - (Real.cos θ - Real.cos (φ₀ i)) ^ 2 / 4) ^ m = ∑ k ∈ range N, β i k * cosSum θ k := by
    intro i θ
    rw [hα_i i θ]
    have hle : N_i i ≤ N := le_sup (mem_univ i)
    have hsub : range (N_i i) ⊆ range N := range_mono hle
    have hsub_eq : (∑ k ∈ range (N_i i), β i k * cosSum θ k) =
        ∑ k ∈ range N, β i k * cosSum θ k :=
      sum_subset hsub fun k _ hk => by
        have hk' : ¬(k < N_i i) := fun h => hk (Finset.mem_range.mpr h)
        simp [β, hk']
    rw [← hsub_eq]
    exact sum_congr rfl fun k hk => by simp [β, Finset.mem_range.mp hk]
  refine ⟨N, fun k => if k ∈ piBox n N then ∏ i, β i (k i) else 0,
    fun k hk => if_neg hk, fun θ => ?_⟩
  simp_rw [hβ _ _]
  rw [Finset.prod_univ_sum (fun _ => range N) (fun i k => β i k * cosSum (θ i) k)]
  change (∑ k ∈ piBox n N, ∏ i, (β i (k i) * cosSum (θ i) (k i))) = _
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [if_pos hk, chiProd, ← Finset.prod_mul_distrib]

/-- Positive Sato–Tate mass of every nontrivial subinterval inside `(0, π)`. -/
private theorem satoTate_Ioc_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < π) :
    0 < (satoTate (Ioc a b)).toReal := by
  have hm : MeasurableSet (Ioc a b) := measurableSet_Ioc
  have h1 : (satoTate (Ioc a b)).toReal =
      ∫ θ, (Ioc a b).indicator 1 θ ∂satoTate := by
    rw [integral_indicator_one hm, Measure.real]
  rw [h1, integral_satoTate]
  set m₀ := (a + b) / 2 with hm₀_def
  have hm₀a : a < m₀ := by linarith [hm₀_def]
  have hm₀b : m₀ < b := by linarith [hm₀_def]
  have hsin_pos : 0 < Real.sin m₀ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hd_pos : 0 < satoTateDensity m₀ := by unfold satoTateDensity; positivity
  have hcont : Continuous satoTateDensity := by unfold satoTateDensity; fun_prop
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
    (satoTateDensity m₀ / 2) (by linarith)
  set u := max a (m₀ - δ / 2)
  set v := min b (m₀ + δ / 2)
  have huv : u < v := lt_min (max_lt hab (by linarith)) (max_lt (by linarith) (by linarith))
  have huv_sub : Ioc u v ⊆ Ioc a b := Ioc_subset_Ioc (le_max_left _ _) (min_le_left _ _)
  have hu0 : 0 ≤ u := le_trans ha.le (le_max_left _ _)
  have hvπ : v ≤ π := le_trans (min_le_left _ _) hb.le
  have hint_top : IntervalIntegrable
      (fun θ => (Ioc a b).indicator 1 θ * satoTateDensity θ) volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
    have hmeas : Measurable (fun θ => (Ioc a b).indicator (1 : ℝ → ℝ) θ * satoTateDensity θ) :=
      (measurable_const.indicator hm).mul measurable_satoTateDensity
    refine Continuous.integrableOn_Ioc hcont |>.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (satoTateDensity_nonneg θ)]
    by_cases hθ : θ ∈ Ioc a b
    · simp [indicator_of_mem hθ]
    · simp [indicator_of_notMem hθ, satoTateDensity_nonneg θ]
  have hint_low : IntervalIntegrable
      (fun θ => (Ioc u v).indicator (fun _ => satoTateDensity m₀ / 2) θ) volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
    have hmeas_low : Measurable (fun θ => (Ioc u v).indicator (fun _ => satoTateDensity m₀ / 2) θ) :=
      measurable_const.indicator measurableSet_Ioc
    refine Continuous.integrableOn_Ioc (continuous_const (y := satoTateDensity m₀ / 2)) |>.mono'
      hmeas_low.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs]
    by_cases hθ : θ ∈ Ioc u v
    · rw [indicator_of_mem hθ, abs_of_pos (by linarith)]
    · rw [indicator_of_notMem hθ, abs_zero]; linarith
  have hmono := intervalIntegral.integral_mono_on Real.pi_pos.le hint_low hint_top fun θ _ => by
    by_cases hθ : θ ∈ Ioc u v
    · rw [indicator_of_mem hθ, indicator_of_mem (huv_sub hθ), Pi.one_apply, one_mul]
      have hdist : dist θ m₀ < δ := by
        rw [Real.dist_eq, abs_lt]
        have h1' : m₀ - δ / 2 < θ := lt_of_le_of_lt (le_max_right _ _) hθ.1
        have h2' : θ ≤ m₀ + δ / 2 := hθ.2.trans (min_le_right _ _)
        constructor <;> linarith
      have hnear := hδ hdist
      rw [Real.dist_eq] at hnear
      linarith [(abs_lt.mp hnear).1]
    · rw [indicator_of_notMem hθ]
      by_cases hθ' : θ ∈ Ioc a b
      · rw [indicator_of_mem hθ', Pi.one_apply, one_mul]; exact satoTateDensity_nonneg θ
      · rw [indicator_of_notMem hθ', zero_mul]
  have hval : ∫ θ in (0 : ℝ)..π, (Ioc u v).indicator (fun _ => satoTateDensity m₀ / 2) θ =
      (v - u) * (satoTateDensity m₀ / 2) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_self_of_subset_left (Ioc_subset_Ioc hu0 hvπ), setIntegral_const,
      Real.volume_real_Ioc_of_le huv.le, smul_eq_mul]
  rw [hval] at hmono
  have hvupos : 0 < (v - u) * (satoTateDensity m₀ / 2) := mul_pos (by linarith) (by linarith)
  linarith

/-- Bernoulli lower bound `(1 − x)^n ≥ 1 − n x` for `x ∈ [0, 1]`. -/
private theorem one_sub_mul_le_pow_of_mem_Icc {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ n : ℕ, 1 - (n : ℝ) * x ≤ (1 - x) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := one_sub_mul_le_pow_of_mem_Icc hx0 hx1 n
    have hnn : 0 ≤ 1 - x := by linarith
    have hstep : (1 - (n : ℝ) * x) * (1 - x) ≤ (1 - x) ^ (n + 1) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right ih hnn
    have hexp : 1 - ((n + 1 : ℕ) : ℝ) * x ≤ (1 - (n : ℝ) * x) * (1 - x) := by
      push_cast
      nlinarith [sq_nonneg x]
    linarith

/-- If `torusSum a` is negative somewhere, it is uniformly bounded above by `-η` on a cosine
neighbourhood of an interior point `φ₀ ∈ (0, π)^n`. -/
private theorem exists_interior_cosine_nbhd {n : ℕ} {a : (Fin n → ℕ) → ℝ} (ha : TraceSummable a)
    {θ₀ : Fin n → ℝ} (hneg : torusSum a θ₀ < 0) :
    ∃ (φ₀ : Fin n → ℝ) (η r : ℝ), (∀ i, 0 < φ₀ i ∧ φ₀ i < π) ∧ 0 < η ∧ 0 < r ∧ r ≤ 1 / 2 ∧
      ∀ θ : Fin n → ℝ, (∀ i, |Real.cos (θ i) - Real.cos (φ₀ i)| ≤ r) → torusSum a θ ≤ -η := by
  let ψ₀ : Fin n → ℝ := fun i => Real.arccos (Real.cos (θ₀ i))
  have hcos_ψ : ∀ i, Real.cos (ψ₀ i) = Real.cos (θ₀ i) := fun i =>
    Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)
  have hψ_neg : torusSum a ψ₀ < 0 := by rwa [torusSum_eq_of_cos_eq a hcos_ψ]
  let φ_seq : ℕ → Fin n → ℝ := fun j i =>
    (1 - 1 / ((j : ℝ) + 2)) * ψ₀ i + (1 / ((j : ℝ) + 2)) * (π / 2)
  have hφ_tend : Tendsto φ_seq atTop (𝓝 ψ₀) := by
    rw [tendsto_pi_nhds]
    intro i
    have hinv : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).mul_const (ψ₀ i)).add
      (hinv.mul_const (π / 2))
    simpa only [φ_seq, sub_zero, zero_mul, add_zero, one_mul] using h
  have hev_neg := ((continuous_torusSum ha).tendsto ψ₀).comp hφ_tend |>.eventually
    (gt_mem_nhds hψ_neg)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev_neg
  have hφ₀_neg : torusSum a (φ_seq j₀) < 0 := hj₀ j₀ le_rfl
  have hφ₀_open : ∀ i, 0 < φ_seq j₀ i ∧ φ_seq j₀ i < π := fun i => by
    set w : ℝ := 1 / ((j₀ : ℝ) + 2)
    have hw0 : 0 < w := by positivity
    have hw1 : w < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    have hψ0 : 0 ≤ ψ₀ i := Real.arccos_nonneg _
    have hψπ : ψ₀ i ≤ π := Real.arccos_le_pi _
    have hπ : 0 < π := Real.pi_pos
    show 0 < (1 - w) * ψ₀ i + w * (π / 2) ∧ (1 - w) * ψ₀ i + w * (π / 2) < π
    constructor <;> nlinarith
  have hη0 : 0 < -torusSum a (φ_seq j₀) / 2 := by linarith
  have hg_cont : Continuous (fun u : Fin n → ℝ => torusSum a (fun i => Real.arccos (u i))) :=
    (continuous_torusSum ha).comp (continuous_pi fun i =>
      Real.continuous_arccos.comp (continuous_apply i))
  have hgu₀ : torusSum a (fun i => Real.arccos (Real.cos (φ_seq j₀ i))) = torusSum a (φ_seq j₀) := by
    congr 1
    exact funext fun i => Real.arccos_cos (hφ₀_open i).1.le (hφ₀_open i).2.le
  obtain ⟨r₀, hr₀, hgr₀⟩ := Metric.continuousAt_iff.mp
    (hg_cont.continuousAt (x := fun i => Real.cos (φ_seq j₀ i)))
    (-torusSum a (φ_seq j₀) / 2) hη0
  refine ⟨φ_seq j₀, -torusSum a (φ_seq j₀) / 2, min (r₀ / 2) (1 / 2), hφ₀_open, hη0,
    lt_min (by linarith) (by norm_num), min_le_right _ _, fun θ hθ => ?_⟩
  have hr0' : 0 ≤ min (r₀ / 2) (1 / 2) := le_min (by linarith) (by norm_num)
  have hr_lt : min (r₀ / 2) (1 / 2) < r₀ := (min_le_left _ _).trans_lt (by linarith)
  have heq_θ : torusSum a θ = torusSum a (fun i => Real.arccos (Real.cos (θ i))) :=
    torusSum_eq_of_cos_eq a fun i =>
      (Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)).symm
  have hdist : dist (fun i => Real.cos (θ i)) (fun i => Real.cos (φ_seq j₀ i)) < r₀ := by
    refine lt_of_le_of_lt ((dist_pi_le_iff hr0').mpr fun i => ?_) hr_lt
    rw [Real.dist_eq]
    exact hθ i
  have hnear := hgr₀ hdist
  rw [Real.dist_eq, hgu₀] at hnear
  have h1 := (abs_lt.mp hnear).2
  rw [heq_θ]
  linarith

/-- Positive-mass product sub-box around an interior torus point `φ₀ ∈ (0, π)^n` on which cosines
stay within `δ`. -/
private theorem exists_core_box_pos {n : ℕ} {φ₀ : Fin n → ℝ}
    (hφ₀ : ∀ i, 0 < φ₀ i ∧ φ₀ i < π) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : Set (Fin n → ℝ), MeasurableSet Q ∧ 0 < (torusMeasure n Q).toReal ∧
      ∀ θ ∈ Q, ∀ i, |Real.cos (θ i) - Real.cos (φ₀ i)| ≤ δ := by
  have hcos_cont : Continuous (fun θ : Fin n → ℝ => fun i => Real.cos (θ i)) :=
    continuous_pi fun i => Real.continuous_cos.comp (continuous_apply i)
  obtain ⟨δ₁, hδ₁, hcos_δ⟩ := Metric.continuousAt_iff.mp (hcos_cont.continuousAt (x := φ₀)) δ hδ
  let a_i : Fin n → ℝ := fun i => max (φ₀ i / 2) (φ₀ i - δ₁ / 2)
  let b_i : Fin n → ℝ := fun i => min ((φ₀ i + π) / 2) (φ₀ i + δ₁ / 2)
  have ha_pos : ∀ i, 0 < a_i i := fun i => lt_of_lt_of_le (by linarith [(hφ₀ i).1]) (le_max_left _ _)
  have hb_lt : ∀ i, b_i i < π := fun i => lt_of_le_of_lt (min_le_left _ _) (by linarith [(hφ₀ i).2])
  have hab_lt : ∀ i, a_i i < b_i i := fun i => by
    have h1 : a_i i < φ₀ i := max_lt (by linarith [(hφ₀ i).1]) (by linarith)
    have h2 : φ₀ i < b_i i := lt_min (by linarith [(hφ₀ i).2]) (by linarith)
    linarith
  refine ⟨Set.pi univ fun i => Ioc (a_i i) (b_i i),
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc, ?_, ?_⟩
  · have hpi : torusMeasure n (Set.pi univ fun i => Ioc (a_i i) (b_i i)) =
        ∏ i : Fin n, satoTate (Ioc (a_i i) (b_i i)) := by
      unfold torusMeasure
      exact Measure.pi_pi (fun _ => satoTate) (fun i => Ioc (a_i i) (b_i i))
    rw [hpi, ENNReal.toReal_prod]
    exact prod_pos fun i _ => satoTate_Ioc_pos (ha_pos i) (hab_lt i) (hb_lt i)
  · intro θ hθ i
    have hdist : dist θ φ₀ < δ₁ := by
      refine (dist_pi_lt_iff hδ₁).mpr fun j => ?_
      have hj := hθ j (mem_univ j)
      rw [Real.dist_eq, abs_lt]
      have h1 : φ₀ j - δ₁ / 2 < θ j := lt_of_le_of_lt (le_max_right _ _) hj.1
      have h2 : θ j ≤ φ₀ j + δ₁ / 2 := hj.2.trans (min_le_right _ _)
      constructor <;> linarith
    have hc := (dist_pi_lt_iff hδ).mp (hcos_δ hdist) i
    rw [Real.dist_eq] at hc
    exact hc.le

/-- Base factor `∏_i (1 − (cos θ_i − cos φ₀_i)²/4)` of the peaking polynomial. -/
private def peakBase {n : ℕ} (φ₀ θ : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, (1 - (Real.cos (θ i) - Real.cos (φ₀ i)) ^ 2 / 4)

private theorem peakFactor_mem_Icc (x y : ℝ) :
    0 ≤ 1 - (Real.cos x - Real.cos y) ^ 2 / 4 ∧ 1 - (Real.cos x - Real.cos y) ^ 2 / 4 ≤ 1 := by
  have hdiff : |Real.cos x - Real.cos y| ≤ 2 := by
    have := Real.neg_one_le_cos x; have := Real.cos_le_one x
    have := Real.neg_one_le_cos y; have := Real.cos_le_one y
    rw [abs_le]; constructor <;> linarith
  have hsq : (Real.cos x - Real.cos y) ^ 2 ≤ 4 := by
    have := sq_le_sq' (abs_le.mp hdiff).1 (abs_le.mp hdiff).2; nlinarith
  exact ⟨by linarith, by nlinarith [sq_nonneg (Real.cos x - Real.cos y)]⟩

private theorem peakBase_nonneg {n : ℕ} (φ₀ θ : Fin n → ℝ) : 0 ≤ peakBase φ₀ θ :=
  Finset.prod_nonneg fun i _ => (peakFactor_mem_Icc (θ i) (φ₀ i)).1

private theorem peakBase_ge_of_small {n : ℕ} {φ₀ θ : Fin n → ℝ} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1 / 2)
    (hsmall : ∀ i, |Real.cos (θ i) - Real.cos (φ₀ i)| ≤ r / (2 * ((n : ℝ) + 1))) :
    1 - r ^ 2 / 16 ≤ peakBase φ₀ θ := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hd_small : r ^ 2 / (16 * ((n : ℝ) + 1)) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      1 - r ^ 2 / (16 * ((n : ℝ) + 1)) ≤ 1 - (Real.cos (θ i) - Real.cos (φ₀ i)) ^ 2 / 4 := by
    intro i _
    have hsq : (Real.cos (θ i) - Real.cos (φ₀ i)) ^ 2 ≤ (r / (2 * ((n : ℝ) + 1))) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hsmall i) 2
    have hden : (r / (2 * ((n : ℝ) + 1))) ^ 2 / 4 ≤ r ^ 2 / (16 * ((n : ℝ) + 1)) := by
      have he : (r / (2 * ((n : ℝ) + 1))) ^ 2 / 4 = r ^ 2 / (16 * ((n : ℝ) + 1) ^ 2) := by
        field_simp; ring
      rw [he]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) (by nlinarith)
    linarith
  have hprod : (1 - r ^ 2 / (16 * ((n : ℝ) + 1))) ^ n ≤ peakBase φ₀ θ := by
    simpa [peakBase] using Finset.prod_le_prod (fun _ _ => by linarith) hfac
  have hbern := one_sub_mul_le_pow_of_mem_Icc
    (x := r ^ 2 / (16 * ((n : ℝ) + 1))) (by positivity) (by linarith) n
  have hstep : (n : ℝ) * (r ^ 2 / (16 * ((n : ℝ) + 1))) ≤ r ^ 2 / 16 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg r]
  linarith

private theorem peakBase_le_of_exists_gt {n : ℕ} {φ₀ θ : Fin n → ℝ} {r : ℝ} (hr0 : 0 < r)
    (hgt : ∃ i, r < |Real.cos (θ i) - Real.cos (φ₀ i)|) :
    peakBase φ₀ θ ≤ 1 - r ^ 2 / 4 := by
  obtain ⟨i₀, hi₀⟩ := hgt
  unfold peakBase
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  have hrest : ∏ j ∈ Finset.univ.erase i₀, (1 - (Real.cos (θ j) - Real.cos (φ₀ j)) ^ 2 / 4) ≤ 1 :=
    Finset.prod_le_one (fun j _ => (peakFactor_mem_Icc (θ j) (φ₀ j)).1)
      (fun j _ => (peakFactor_mem_Icc (θ j) (φ₀ j)).2)
  have hsq : r ^ 2 < (Real.cos (θ i₀) - Real.cos (φ₀ i₀)) ^ 2 := by
    rw [← sq_abs (Real.cos (θ i₀) - Real.cos (φ₀ i₀))]
    exact pow_lt_pow_left₀ hi₀ hr0.le (by norm_num)
  calc (1 - (Real.cos (θ i₀) - Real.cos (φ₀ i₀)) ^ 2 / 4) *
        ∏ j ∈ Finset.univ.erase i₀, (1 - (Real.cos (θ j) - Real.cos (φ₀ j)) ^ 2 / 4)
      ≤ (1 - (Real.cos (θ i₀) - Real.cos (φ₀ i₀)) ^ 2 / 4) * 1 :=
        mul_le_mul_of_nonneg_left hrest (peakFactor_mem_Icc (θ i₀) (φ₀ i₀)).1
    _ ≤ 1 - r ^ 2 / 4 := by linarith

/-- **Fixed-base Sato–Tate duality.** A trace-summable amplitude has nonnegative torus sum everywhere
if and only if every Dirichlet-dilated Hankel form `dirichletHankelForm a N c` is nonnegative. -/
theorem nonneg_torusSum_iff_dirichletHankel_nonneg {n : ℕ} {a : (Fin n → ℕ) → ℝ}
    (ha : TraceSummable a) :
    (∀ θ : Fin n → ℝ, 0 ≤ torusSum a θ) ↔
      ∀ (N : ℕ) (c : (Fin n → ℕ) → ℝ), (∀ k, k ∉ piBox n N → c k = 0) →
        0 ≤ dirichletHankelForm a N c := by
  constructor
  · intro hpos N c hc
    rw [← integral_torusSum_mul_sq_eq_dirichletHankel ha N c hc]
    exact integral_nonneg fun θ => mul_nonneg (hpos θ) (sq_nonneg _)
  · intro hform θ₀
    by_contra hneg
    push Not at hneg
    obtain ⟨φ₀, η, r, hφ₀, hη0, hr0, hr1, hG_neg⟩ := exists_interior_cosine_nbhd ha hneg
    obtain ⟨Q, hQ_meas, hμQ, hQ_cos⟩ := exists_core_box_pos hφ₀
      (show 0 < r / (2 * ((n : ℝ) + 1)) by positivity)
    have hM_nn : 0 ≤ ∑' q, |a q| * chiSize q :=
      tsum_nonneg fun q => mul_nonneg (abs_nonneg _) (chiSize_nonneg q)
    obtain ⟨M, hM0, ha_abs⟩ : ∃ M : ℝ, 0 < M ∧ ∀ θ, |torusSum a θ| ≤ M :=
      ⟨(∑' q, |a q| * chiSize q) + 1, by linarith, fun θ => (abs_torusSum_le ha θ).trans (by linarith)⟩
    have hqc0 : 0 < (1 - r ^ 2 / 16) ^ 2 := sq_pos_of_pos (by nlinarith)
    have hratio1 : (1 - r ^ 2 / 4) ^ 2 / (1 - r ^ 2 / 16) ^ 2 < 1 := by
      rw [div_lt_one hqc0]
      exact pow_lt_pow_left₀ (by nlinarith [sq_pos_of_pos hr0]) (by nlinarith) (by norm_num)
    have htend : Tendsto (fun m : ℕ => M * ((1 - r ^ 2 / 4) ^ 2 / (1 - r ^ 2 / 16) ^ 2) ^ m)
        atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (div_nonneg (sq_nonneg _) hqc0.le) hratio1).const_mul M
    obtain ⟨m, hm⟩ := (htend.eventually (gt_mem_nhds (mul_pos hη0 hμQ))).exists
    obtain ⟨N, c, hc, hP_eq⟩ := exists_chiProd_peak φ₀ m
    have hP_pow : ∀ θ : Fin n → ℝ,
        (∑ k ∈ piBox n N, c k * chiProd θ k) ^ 2 = peakBase φ₀ θ ^ (2 * m) := fun θ => by
      have h1 : (∏ i : Fin n, (1 - (Real.cos (θ i) - Real.cos (φ₀ i)) ^ 2 / 4) ^ m) =
          peakBase φ₀ θ ^ m :=
        Finset.prod_pow Finset.univ m fun i => 1 - (Real.cos (θ i) - Real.cos (φ₀ i)) ^ 2 / 4
      rw [← hP_eq θ, h1, ← pow_mul, mul_comm m 2]
    have hpoint : ∀ θ : Fin n → ℝ,
        torusSum a θ * (∑ k ∈ piBox n N, c k * chiProd θ k) ^ 2 ≤
          Q.indicator (fun _ => -η * ((1 - r ^ 2 / 16) ^ 2) ^ m) θ + M * ((1 - r ^ 2 / 4) ^ 2) ^ m := by
      intro θ
      rw [hP_pow θ]
      have htail_nn : 0 ≤ M * ((1 - r ^ 2 / 4) ^ 2) ^ m :=
        mul_nonneg hM0.le (pow_nonneg (sq_nonneg _) _)
      by_cases hG : ∀ i, |Real.cos (θ i) - Real.cos (φ₀ i)| ≤ r
      · have hneg_θ : torusSum a θ ≤ -η := hG_neg θ hG
        by_cases hQ : θ ∈ Q
        · rw [indicator_of_mem hQ]
          have hpow_low : ((1 - r ^ 2 / 16) ^ 2) ^ m ≤ peakBase φ₀ θ ^ (2 * m) := by
            rw [← pow_mul]
            exact pow_le_pow_left₀ (by nlinarith)
              (peakBase_ge_of_small hr0 hr1 (hQ_cos θ hQ)) (2 * m)
          have h1 : torusSum a θ * peakBase φ₀ θ ^ (2 * m) ≤ -η * peakBase φ₀ θ ^ (2 * m) :=
            mul_le_mul_of_nonneg_right hneg_θ (pow_nonneg (peakBase_nonneg φ₀ θ) _)
          have h2 : -η * peakBase φ₀ θ ^ (2 * m) ≤ -η * ((1 - r ^ 2 / 16) ^ 2) ^ m := by
            nlinarith [hη0, hpow_low]
          linarith
        · rw [indicator_of_notMem hQ]
          have h1 : torusSum a θ * peakBase φ₀ θ ^ (2 * m) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg (peakBase_nonneg φ₀ θ) _)
          linarith
      · have hnotQ : θ ∉ Q := fun hQ => hG fun i =>
          (hQ_cos θ hQ i).trans (by
            rw [div_le_iff₀ (by positivity)]
            nlinarith [hr0, Nat.cast_nonneg (α := ℝ) n])
        rw [indicator_of_notMem hnotQ, zero_add]
        push Not at hG
        have hpow_up : peakBase φ₀ θ ^ (2 * m) ≤ ((1 - r ^ 2 / 4) ^ 2) ^ m := by
          rw [← pow_mul]
          exact pow_le_pow_left₀ (peakBase_nonneg φ₀ θ) (peakBase_le_of_exists_gt hr0 hG) (2 * m)
        have ha_up : torusSum a θ ≤ M := (le_abs_self _).trans (ha_abs θ)
        calc torusSum a θ * peakBase φ₀ θ ^ (2 * m)
            ≤ M * peakBase φ₀ θ ^ (2 * m) :=
              mul_le_mul_of_nonneg_right ha_up (pow_nonneg (peakBase_nonneg φ₀ θ) _)
          _ ≤ M * ((1 - r ^ 2 / 4) ^ 2) ^ m := mul_le_mul_of_nonneg_left hpow_up hM0.le
    have hint_lhs : Integrable (fun θ => torusSum a θ * (∑ k ∈ piBox n N, c k * chiProd θ k) ^ 2)
        (torusMeasure n) := by
      have hcont_P : Continuous (fun θ => ∑ k ∈ piBox n N, c k * chiProd θ k) :=
        continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_chiProd k)
      refine integrable_of_bounded_continuous (C := M * (∑ k ∈ piBox n N, |c k| * chiSize k) ^ 2)
        ((continuous_torusSum ha).mul (hcont_P.pow 2)) fun θ => ?_
      rw [abs_mul, abs_pow]
      have hsum_b : |∑ k ∈ piBox n N, c k * chiProd θ k| ≤ ∑ k ∈ piBox n N, |c k| * chiSize k :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_chiProd_le θ k) (abs_nonneg _))
      exact mul_le_mul (ha_abs θ) (pow_le_pow_left₀ (abs_nonneg _) hsum_b 2) (by positivity) hM0.le
    have hint_ind : Integrable (Q.indicator fun _ => -η * ((1 - r ^ 2 / 16) ^ 2) ^ m)
        (torusMeasure n) := (integrable_const (-η * ((1 - r ^ 2 / 16) ^ 2) ^ m)).indicator hQ_meas
    have hint_c : Integrable (fun _ : Fin n → ℝ => M * ((1 - r ^ 2 / 4) ^ 2) ^ m)
        (torusMeasure n) := integrable_const (M * ((1 - r ^ 2 / 4) ^ 2) ^ m)
    have hint_le := integral_mono hint_lhs (hint_ind.fun_add hint_c) hpoint
    rw [integral_torusSum_mul_sq_eq_dirichletHankel ha N c hc,
      integral_add hint_ind hint_c, integral_indicator_const _ hQ_meas,
      integral_const] at hint_le
    have hprob : ((torusMeasure n) univ).toReal = 1 := by simp
    simp only [Measure.real, smul_eq_mul] at hint_le
    rw [hprob, one_mul] at hint_le
    have hqc_m : 0 < ((1 - r ^ 2 / 16) ^ 2) ^ m := pow_pos hqc0 m
    have hq_eq : M * ((1 - r ^ 2 / 4) ^ 2) ^ m =
        M * ((1 - r ^ 2 / 4) ^ 2 / (1 - r ^ 2 / 16) ^ 2) ^ m * ((1 - r ^ 2 / 16) ^ 2) ^ m := by
      rw [div_pow, mul_assoc, div_mul_cancel₀ _ hqc_m.ne']
    have hlt_neg : (torusMeasure n Q).toReal * (-η * ((1 - r ^ 2 / 16) ^ 2) ^ m) +
        M * ((1 - r ^ 2 / 4) ^ 2) ^ m < 0 := by
      rw [hq_eq]
      nlinarith [hm, hqc_m]
    linarith [hform N c hc]

/-- **Fixed-base arithmetic classification.** At any fixed base point `x`, an exponentially decaying
amplitude `f` has nonnegative torus sums across all finite prime sets if and only if every prime
Dirichlet-dilated Hankel form at `x` is nonnegative. -/
theorem torusPositiveAt_iff_dirichletHankel_nonneg {f : ℝ → ℝ} {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    {x : ℝ} (hd : ExpDecayFrom x κ₀ f) :
    (∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
      ∀ θ : Fin n → ℝ, 0 ≤ torusSum (ampl f (fun i => Real.log (p i)) x) θ) ↔
      ∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
        ∀ (N : ℕ) (c : (Fin n → ℕ) → ℝ), (∀ k, k ∉ piBox n N → c k = 0) →
          0 ≤ dirichletHankelForm (ampl f (fun i => Real.log (p i)) x) N c := by
  obtain ⟨C, _, hC⟩ := hd
  refine ⟨fun h n p hp hinj => ?_, fun h n p hp hinj => ?_⟩
  · have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
    exact (nonneg_torusSum_iff_dirichletHankel_nonneg (traceSummable_ampl hκ₀ hC hℓ le_rfl)).mp
      (h n p hp hinj)
  · have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
    exact (nonneg_torusSum_iff_dirichletHankel_nonneg (traceSummable_ampl hκ₀ hC hℓ le_rfl)).mpr
      (h n p hp hinj)

/-! ### Exact Euler torus sums and supercritical separation (`α > 1`) -/

/-- Exact single-step insertion of `y ↦ e^{−αy}`. -/
theorem insertion_exp_neg {α ℓ : ℝ} (hα : 0 < α) (hℓ : 0 < ℓ) (θ x : ℝ) :
    insertion θ ℓ (fun y => Real.exp (-α * y)) x =
      Real.exp (-α * x) * ‖1 - (Real.exp (-α * ℓ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖⁻¹ ^ 2 := by
  have hC : ∀ y : ℝ, x ≤ y → |Real.exp (-α * y)| ≤ 1 * Real.exp (-α * y) := fun y _ => by
    rw [abs_of_pos (Real.exp_pos _), one_mul]
  have hpair := ofReal_insertion_eq_tsum_pairs hα hℓ hC le_rfl θ
  set z : ℂ := (Real.exp (-α * ℓ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  set w : ℂ := conj z
  have hz_norm : ‖z‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hw_norm : ‖w‖ < 1 := by simpa [w] using hz_norm
  have hterm : ∀ p : ℕ × ℕ,
      Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * Complex.I) *
          (Real.exp (-α * (x + ((p.1 + p.2 : ℕ) : ℝ) * ℓ)) : ℂ) =
        (Real.exp (-α * x) : ℂ) * (z ^ p.1 * w ^ p.2) := by
    rintro ⟨a, b⟩
    have hza : z ^ a = (Real.exp (-α * ℓ) : ℂ) ^ a * Complex.exp ((a : ℂ) * ((θ : ℂ) * Complex.I)) := by
      rw [show z = (Real.exp (-α * ℓ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from rfl,
        mul_pow, ← Complex.exp_nat_mul]
    have hwb : w ^ b = (Real.exp (-α * ℓ) : ℂ) ^ b * Complex.exp ((b : ℂ) * -((θ : ℂ) * Complex.I)) := by
      have hw_eq : w = (Real.exp (-α * ℓ) : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
        simp only [w, z, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, mul_neg]
      rw [hw_eq, mul_pow, ← Complex.exp_nat_mul]
    have hexp_r : (Real.exp (-α * (x + ((a + b : ℕ) : ℝ) * ℓ)) : ℂ) =
        (Real.exp (-α * x) : ℂ) * ((Real.exp (-α * ℓ) : ℂ) ^ a * (Real.exp (-α * ℓ) : ℂ) ^ b) := by
      have hr : Real.exp (-α * (x + ((a + b : ℕ) : ℝ) * ℓ)) =
          Real.exp (-α * x) * (Real.exp (-α * ℓ) ^ a * Real.exp (-α * ℓ) ^ b) := by
        rw [← pow_add, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1; push_cast; ring
      rw [hr]
      push_cast
      rfl
    have hphase : Complex.exp ((((a : ℝ) - (b : ℝ)) * θ : ℝ) * Complex.I) =
        Complex.exp ((a : ℂ) * ((θ : ℂ) * Complex.I)) *
          Complex.exp ((b : ℂ) * -((θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    change Complex.exp ((((a : ℝ) - (b : ℝ)) * θ : ℝ) * Complex.I) *
        (Real.exp (-α * (x + ((a + b : ℕ) : ℝ) * ℓ)) : ℂ) =
      (Real.exp (-α * x) : ℂ) * (z ^ a * w ^ b)
    rw [hza, hwb, hexp_r, hphase]
    ring
  simp_rw [hterm] at hpair
  rw [tsum_mul_left] at hpair
  have hprod_sum : (∑' p : ℕ × ℕ, z ^ p.1 * w ^ p.2) = (1 - z)⁻¹ * (1 - w)⁻¹ := by
    have h1 := summable_geometric_of_norm_lt_one hz_norm
    have h2 := summable_geometric_of_norm_lt_one hw_norm
    rw [← tsum_mul_tsum_of_summable_norm h1.norm h2.norm, tsum_geometric_of_norm_lt_one hz_norm,
      tsum_geometric_of_norm_lt_one hw_norm]
  rw [hprod_sum] at hpair
  have hnorm_eq : (1 - z)⁻¹ * (1 - w)⁻¹ = ((‖1 - z‖⁻¹ ^ 2 : ℝ) : ℂ) := by
    have hconj : 1 - w = conj (1 - z) := by simp [w]
    rw [hconj, ← mul_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_inv, inv_pow]
  rw [hnorm_eq, ← Complex.ofReal_mul] at hpair
  exact Complex.ofReal_injective hpair

/-- **Exact Euler product of the torus sum on `e^{−αy}`.** -/
theorem torusSum_ampl_exp_neg {n : ℕ} {α : ℝ} (hα : 0 < α) {ℓ : Fin n → ℝ} (hℓ : ∀ i, 0 < ℓ i)
    (x : ℝ) (θ : Fin n → ℝ) :
    torusSum (ampl (fun y => Real.exp (-α * y)) ℓ x) θ =
      Real.exp (-α * x) *
        ∏ i : Fin n, ‖1 - (Real.exp (-α * ℓ i) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)‖⁻¹ ^ 2 := by
  induction n generalizing x with
  | zero =>
    haveI : Unique (Fin 0 → ℕ) := Pi.uniqueOfIsEmpty _
    rw [torusSum, tsum_fintype]
    simp [ampl, chiProd]
  | succ n ih =>
    have hC : ∀ y : ℝ, x ≤ y → |Real.exp (-α * y)| ≤ 1 * Real.exp (-α * y) := fun y _ => by
      rw [abs_of_pos (Real.exp_pos _), one_mul]
    rw [torusSum_cons hα hC hℓ le_rfl θ]
    have htail : (fun y => torusSum (ampl (fun y => Real.exp (-α * y)) (Fin.tail ℓ) y) (Fin.tail θ)) =
        fun y => (∏ i : Fin n,
          ‖1 - (Real.exp (-α * Fin.tail ℓ i) : ℂ) * Complex.exp ((Fin.tail θ i : ℂ) * Complex.I)‖⁻¹ ^ 2) *
          Real.exp (-α * y) := by
      funext y
      rw [ih (ℓ := Fin.tail ℓ) (fun i => hℓ i.succ) y (Fin.tail θ), mul_comm]
    rw [htail]
    have hlin : insertion (θ 0) (ℓ 0) (fun y =>
        (∏ i : Fin n, ‖1 - (Real.exp (-α * Fin.tail ℓ i) : ℂ) *
          Complex.exp ((Fin.tail θ i : ℂ) * Complex.I)‖⁻¹ ^ 2) * Real.exp (-α * y)) x =
        (∏ i : Fin n, ‖1 - (Real.exp (-α * Fin.tail ℓ i) : ℂ) *
          Complex.exp ((Fin.tail θ i : ℂ) * Complex.I)‖⁻¹ ^ 2) *
          insertion (θ 0) (ℓ 0) (fun y => Real.exp (-α * y)) x := by
      simp only [insertion, ← tsum_mul_left]
      exact tsum_congr fun k => by ring
    rw [hlin, insertion_exp_neg hα (hℓ 0) (θ 0) x, Fin.prod_univ_succ]
    simp only [Fin.tail]
    ring

/-- The integer `∏_i p_i^{k_i}` encoded by a multi-index on a prime tuple. -/
def primeMonoidProd {n : ℕ} (p : Fin n → ℕ) (k : Fin n → ℕ) : ℕ :=
  ∏ i : Fin n, (p i) ^ (k i)

private theorem prime_pow_cancel {q A B : ℕ} (hq : q.Prime) (hA : ¬(q ∣ A)) (hB : ¬(q ∣ B)) :
    ∀ {a b : ℕ}, q ^ a * A = q ^ b * B → a = b ∧ A = B
  | 0, 0, h => ⟨rfl, by simpa using h⟩
  | 0, b + 1, h => by
    exfalso; apply hA
    rw [pow_zero, one_mul, pow_succ', mul_assoc] at h
    exact ⟨q ^ b * B, h⟩
  | a + 1, 0, h => by
    exfalso; apply hB
    rw [pow_zero, one_mul, pow_succ', mul_assoc] at h
    exact ⟨q ^ a * A, h.symm⟩
  | a + 1, b + 1, h => by
    rw [pow_succ', pow_succ', mul_assoc, mul_assoc] at h
    obtain ⟨hab, hAB⟩ := prime_pow_cancel hq hA hB (Nat.mul_left_cancel hq.pos h)
    exact ⟨congrArg Nat.succ hab, hAB⟩

/-- Unique factorization on a tuple of distinct primes. -/
theorem primeMonoidProd_injective {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) : Function.Injective (primeMonoidProd p) := by
  induction n with
  | zero =>
    intro k m _
    haveI : Unique (Fin 0 → ℕ) := Pi.uniqueOfIsEmpty _
    exact Subsingleton.elim k m
  | succ n ih =>
    intro k m hkm
    unfold primeMonoidProd at hkm
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at hkm
    have hnot_dvd : ∀ r : Fin (n + 1) → ℕ, ¬(p 0 ∣ ∏ i : Fin n, p i.succ ^ r i.succ) := by
      intro r hdvd
      rw [(hp 0).prime.dvd_finsetProd_iff] at hdvd
      obtain ⟨i, _, hi⟩ := hdvd
      have hdiv := (hp 0).dvd_of_dvd_pow hi
      have heq := (Nat.prime_dvd_prime_iff_eq (hp 0) (hp i.succ)).mp hdiv
      exact Fin.succ_ne_zero i (hinj heq).symm
    obtain ⟨hk0, hprod⟩ := prime_pow_cancel (hp 0) (hnot_dvd k) (hnot_dvd m) hkm
    have htail : Fin.tail k = Fin.tail m :=
      ih (fun i => hp i.succ) (fun i j hij => Fin.succ_injective _ (hinj hij)) hprod
    rw [← Fin.cons_self_tail k, ← Fin.cons_self_tail m, hk0, htail]

theorem primeMonoidProd_pos {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, (p i).Prime) (k : Fin n → ℕ) :
    0 < primeMonoidProd p k :=
  Finset.prod_pos fun i _ => pow_pos (hp i).pos _

theorem log_primeMonoidProd {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, (p i).Prime) (k : Fin n → ℕ) :
    Real.log (primeMonoidProd p k : ℝ) = ∑ i : Fin n, (k i : ℝ) * Real.log (p i) := by
  unfold primeMonoidProd
  rw [Nat.cast_prod, Real.log_prod]
  · exact sum_congr rfl fun i _ => by rw [Nat.cast_pow, Real.log_pow]
  · intro i _
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (hp i).ne_zero)

private theorem add_one_le_two_pow : ∀ k : ℕ, ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k
  | 0 => by norm_num
  | 1 => by norm_num
  | k + 2 => by
    have ih := add_one_le_two_pow (k + 1)
    have hpos : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    push_cast at ih ⊢
    linarith

/-- Uniform `O(N(k)^η)` divisor bound on `chiSize k`, with constant independent of `n` and `p`. -/
theorem exists_chiSize_le_rpow {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
      ∀ k : Fin n → ℕ, chiSize k ≤ B * (primeMonoidProd p k : ℝ) ^ η := by
  set c : ℝ := η * Real.log 2
  have hc0 : 0 < c := mul_pos hη (Real.log_pos (by norm_num))
  set M : ℝ := max 1 (1 / c)
  have hM1 : 1 ≤ M := le_max_left _ _
  set P : ℕ := ⌊(2 : ℝ) ^ (1 / η)⌋₊ + 1
  refine ⟨M ^ P, by positivity, fun n p hp hinj k => ?_⟩
  classical
  have hfac_small : ∀ i : Fin n, ((k i : ℝ) + 1) ≤ M * (((p i) ^ (k i) : ℕ) : ℝ) ^ η := by
    intro i
    have hexp := Real.add_one_le_exp (c * (k i : ℝ))
    have hmc : 1 ≤ M * c := by
      have : 1 / c ≤ M := le_max_right _ _
      exact (div_le_iff₀ hc0).mp this
    have h1 : ((k i : ℝ) + 1) ≤ M * Real.exp (c * (k i : ℝ)) := by
      have : ((k i : ℝ) + 1) ≤ M * (c * (k i : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) (k i)]
      exact this.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    have h2 : Real.exp (c * (k i : ℝ)) ≤ (((p i) ^ (k i) : ℕ) : ℝ) ^ η := by
      have hp2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
      have he2 : Real.exp (c * (k i : ℝ)) = ((2 ^ (k i) : ℕ) : ℝ) ^ η := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_def_of_pos (by positivity), Real.log_pow]
        congr 1; simp only [c]; ring
      rw [he2]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.pow_le_pow_left (hp i).two_le _) hη.le
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hfac_large : ∀ i : Fin n, P ≤ p i → ((k i : ℝ) + 1) ≤ (((p i) ^ (k i) : ℕ) : ℝ) ^ η := by
    intro i hi
    rcases eq_or_ne (k i) 0 with hk0 | hkne
    · simp [hk0]
    · have hp_gt : (2 : ℝ) ^ (1 / η) < p i :=
        (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hi)
      have h2le : (2 : ℝ) ≤ (p i : ℝ) ^ η := by
        have h := Real.rpow_le_rpow (by positivity) hp_gt.le hη.le
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hη.ne', Real.rpow_one] at h
        exact h
      calc ((k i : ℝ) + 1) ≤ (2 : ℝ) ^ (k i) := add_one_le_two_pow (k i)
        _ ≤ ((p i : ℝ) ^ η) ^ (k i) := pow_le_pow_left₀ (by norm_num) h2le _
        _ = (((p i) ^ (k i) : ℕ) : ℝ) ^ η := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
            Real.rpow_mul (by positivity), Real.rpow_natCast, Nat.cast_pow]
  set S := univ.filter (fun i : Fin n => p i < P)
  have hcard : S.card ≤ P := by
    have h1 : S.card = (S.image p).card := (Finset.card_image_of_injective S hinj).symm
    have h2 : S.image p ⊆ range P := fun m hm => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    exact h1.trans_le ((Finset.card_le_card h2).trans_eq (Finset.card_range P))
  have hdom : ∀ i : Fin n, ((k i : ℝ) + 1) ≤
      (if i ∈ S then M else 1) * (((p i) ^ (k i) : ℕ) : ℝ) ^ η := by
    intro i
    by_cases hi : i ∈ S
    · rw [if_pos hi]; exact hfac_small i
    · rw [if_neg hi, one_mul]
      have hge : P ≤ p i := le_of_not_gt fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
      exact hfac_large i hge
  calc chiSize k = ∏ i : Fin n, ((k i : ℝ) + 1) := rfl
    _ ≤ ∏ i : Fin n, ((if i ∈ S then M else 1) * (((p i) ^ (k i) : ℕ) : ℝ) ^ η) :=
      prod_le_prod (fun _ _ => by positivity) fun i _ => hdom i
    _ = (∏ i : Fin n, if i ∈ S then M else 1) * ∏ i : Fin n, (((p i) ^ (k i) : ℕ) : ℝ) ^ η :=
      prod_mul_distrib
    _ ≤ M ^ P * (primeMonoidProd p k : ℝ) ^ η := by
      have hMprod : (∏ i : Fin n, if i ∈ S then M else 1) ≤ M ^ P := by
        rw [prod_ite, prod_const_one, mul_one, prod_const]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact pow_le_pow_right₀ hM1 hcard
      have hrpow_prod : (∏ i : Fin n, (((p i) ^ (k i) : ℕ) : ℝ) ^ η) =
          (primeMonoidProd p k : ℝ) ^ η := by
        unfold primeMonoidProd
        rw [Nat.cast_prod, Real.finsetProd_rpow _ _ fun i _ => by positivity]
      rw [hrpow_prod]
      exact mul_le_mul_of_nonneg_right hMprod (by positivity)

/-- Tent bump supported in `(log 3, log 5)` with `tentBump (2 log 2) = 1`. -/
def tentBump (y : ℝ) : ℝ :=
  max 0 (1 - |y - 2 * Real.log 2| / Real.log (5 / 4))

theorem continuous_tentBump : Continuous tentBump := by
  unfold tentBump
  fun_prop

theorem tentBump_nonneg (y : ℝ) : 0 ≤ tentBump y := le_max_left _ _

theorem tentBump_le_one (y : ℝ) : tentBump y ≤ 1 := by
  unfold tentBump
  have hlog : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  exact max_le zero_le_one (sub_le_self _ (div_nonneg (abs_nonneg _) hlog.le))

theorem tentBump_two_log_two : tentBump (2 * Real.log 2) = 1 := by
  unfold tentBump
  simp

theorem tentBump_eq_zero_of_ge_log_five {y : ℝ} (hy : Real.log 5 ≤ y) : tentBump y = 0 := by
  unfold tentBump
  have hlog54 : Real.log (5 / 4) = Real.log 5 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hpos : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hdiff : Real.log (5 / 4) ≤ |y - 2 * Real.log 2| := by
    refine le_trans ?_ (le_abs_self _)
    linarith
  have hdiv : 1 ≤ |y - 2 * Real.log 2| / Real.log (5 / 4) := (one_le_div hpos).mpr hdiff
  exact max_eq_left (by linarith)

theorem tentBump_eq_zero_of_le_log_three {y : ℝ} (hy : y ≤ Real.log 3) : tentBump y = 0 := by
  unfold tentBump
  have hpos : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hgap : Real.log (5 / 4) ≤ 2 * Real.log 2 - Real.log 3 := by
    have h1 : 2 * Real.log 2 - Real.log 3 = Real.log (4 / 3) := by
      rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [h1]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hdiff : Real.log (5 / 4) ≤ |y - 2 * Real.log 2| := by
    refine le_trans ?_ (neg_le_abs _)
    linarith
  have hdiv : 1 ≤ |y - 2 * Real.log 2| / Real.log (5 / 4) := (one_le_div hpos).mpr hdiff
  exact max_eq_left (by linarith)

theorem tentBump_le_five_rpow_exp {α : ℝ} (hα : 0 < α) (y : ℝ) :
    |tentBump y| ≤ (5 : ℝ) ^ α * Real.exp (-α * y) := by
  rw [abs_of_nonneg (tentBump_nonneg y)]
  by_cases hy : Real.log 5 ≤ y
  · rw [tentBump_eq_zero_of_ge_log_five hy]
    positivity
  · push Not at hy
    have h1 : 1 ≤ 5 * Real.exp (-y) := by
      have := Real.exp_lt_exp.mpr hy
      rw [Real.exp_log (by norm_num)] at this
      have he : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-y)]
    have hpow := Real.rpow_le_rpow zero_le_one h1 hα.le
    have hmul : (-y) * α = -α * y := by ring
    rw [Real.one_rpow, Real.mul_rpow (by norm_num) (Real.exp_pos _).le,
      ← Real.exp_mul, hmul] at hpow
    exact (tentBump_le_one y).trans hpow

/-- **Supercritical failure of fixed-base and all-base Arithmetic Bernstein (`α > 1`).**
For every `α > 1`, small subtractive perturbations of `e^{−αy}` by `tentBump` stay strictly inside
the torus-positive cone across *all* base points `x ∈ ℝ`, all finite prime sets, and all phases,
while strictly violating exponential convexity at `0`. -/
theorem exists_supercritical_not_expConvex {α : ℝ} (hα : 1 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      let f : ℝ → ℝ := fun y => Real.exp (-α * y) - ε * tentBump y
      Continuous f ∧
      (∀ x₀, ExpDecayFrom x₀ α f) ∧
      (∃ C : ℝ, ∀ y, y ≤ 0 → |f y| ≤ C * Real.exp (-α * y)) ∧
      (∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
        ∀ (x : ℝ) (θ : Fin n → ℝ),
          0 < torusSum (ampl f (fun i => Real.log (p i)) x) θ) ∧
      f (2 * Real.log 2) * f (2 * Real.log 3) < f (Real.log 2 + Real.log 3) ^ 2 ∧
      ¬ IsExpConvexFrom 0 f := by
  have hα0 : 0 < α := by linarith
  -- Uniform Euler floor for `e^{−αy}`
  have hsum_α : Summable (fun m : ℕ => ((m : ℝ) ^ α)⁻¹) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using Real.summable_nat_rpow_inv.mpr hα
  set S_α : ℝ := ∑' m : ℕ, ((m : ℝ) ^ α)⁻¹
  set c_α : ℝ := Real.exp (-2 * S_α)
  have hc_α : 0 < c_α := Real.exp_pos _
  -- Uniform upper bound on `|torusSum (ampl tentBump (log p) x) θ|`
  set η : ℝ := (α - 1) / 2 with hη_def
  have hη : 0 < η := by linarith [hη_def]
  obtain ⟨B_η, hB_η, hchi⟩ := exists_chiSize_le_rpow hη
  set β : ℝ := (α + 1) / 2
  have hβ1 : 1 < β := by simp only [β]; linarith
  have hsum_β : Summable (fun m : ℕ => ((m : ℝ) ^ β)⁻¹) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using Real.summable_nat_rpow_inv.mpr hβ1
  set S_β : ℝ := ∑' m : ℕ, ((m : ℝ) ^ β)⁻¹
  have hS_β_nn : 0 ≤ S_β := tsum_nonneg fun m => by positivity
  set K_α : ℝ := (5 : ℝ) ^ α * B_η * S_β
  have hK_nn : 0 ≤ K_α := by positivity
  set ε₀ : ℝ := c_α / (2 * (K_α + 1))
  have hε₀ : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀, fun ε hε_pos hε_le => ?_⟩
  intro f
  have hf_cont : Continuous f := by
    simp only [f]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
      (continuous_const.mul continuous_tentBump)
  have hf_bound_all : ∀ y : ℝ, |f y| ≤ (1 + ε * (5 : ℝ) ^ α) * Real.exp (-α * y) := fun y => by
    have htri : |Real.exp (-α * y) - ε * tentBump y| ≤
        |Real.exp (-α * y)| + ε * |tentBump y| := by
      have h := abs_sub_le (Real.exp (-α * y)) 0 (ε * tentBump y)
      rw [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_pos hε_pos] at h
      exact h
    have h1 := tentBump_le_five_rpow_exp hα0 y
    rw [abs_of_pos (Real.exp_pos _)] at htri
    calc |f y| ≤ Real.exp (-α * y) + ε * ((5 : ℝ) ^ α * Real.exp (-α * y)) :=
          htri.trans (add_le_add_right (mul_le_mul_of_nonneg_left h1 hε_pos.le) _)
      _ = (1 + ε * (5 : ℝ) ^ α) * Real.exp (-α * y) := by ring
  refine ⟨hf_cont, fun x₀ => ⟨1 + ε * (5 : ℝ) ^ α, by positivity, fun y _ => hf_bound_all y⟩,
    ⟨1 + ε * (5 : ℝ) ^ α, fun y _ => hf_bound_all y⟩, ?_, ?_, ?_⟩
  · -- Strict torus positivity at every `n, p, x, θ`
    intro n p hp hinj x θ
    have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
    -- Lower bound on `torusSum` of `e^{−αy}`
    have hmain_ge : c_α * Real.exp (-α * x) ≤
        torusSum (ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) x) θ := by
      rw [torusSum_ampl_exp_neg hα0 hℓ x θ, mul_comm c_α]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hterm_ge : ∀ i : Fin n,
          Real.exp (-2 * (((p i : ℝ) ^ α)⁻¹)) ≤
            ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)‖⁻¹ ^ 2 := by
        intro i
        have hp_pos : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
        have hexp_p : Real.exp (-α * Real.log (p i)) = ((p i : ℝ) ^ α)⁻¹ := by
          rw [← Real.rpow_neg hp_pos.le, Real.rpow_def_of_pos hp_pos]
          congr 1; ring
        have hnorm_le : ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)‖ ≤
            Real.exp (((p i : ℝ) ^ α)⁻¹) := by
          calc ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)‖
              ≤ ‖(1 : ℂ)‖ + ‖(Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)‖ :=
                norm_sub_le _ _
            _ = 1 + ((p i : ℝ) ^ α)⁻¹ := by
                rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
                  Real.norm_of_nonneg (Real.exp_pos _).le, hexp_p]
            _ ≤ Real.exp (((p i : ℝ) ^ α)⁻¹) := by linarith [Real.add_one_le_exp (((p i : ℝ) ^ α)⁻¹)]
        have hnorm_pos : 0 < ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)‖ := by
          have hsub := norm_sub_norm_le (1 : ℂ)
            ((Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I))
          rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le] at hsub
          have hexp_lt : Real.exp (-α * Real.log (p i)) < 1 :=
            Real.exp_lt_one_iff.mpr (by have := hℓ i; nlinarith)
          linarith
        have hinv : (Real.exp (((p i : ℝ) ^ α)⁻¹))⁻¹ ≤
            ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)‖⁻¹ :=
          inv_anti₀ hnorm_pos hnorm_le
        have hsq := pow_le_pow_left₀ (by positivity) hinv 2
        have hexp2 : (Real.exp (((p i : ℝ) ^ α)⁻¹))⁻¹ ^ 2 = Real.exp (-2 * (((p i : ℝ) ^ α)⁻¹)) := by
          rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; push_cast; ring
        rwa [hexp2] at hsq
      have hprod_exp : Real.exp (-2 * ∑ i : Fin n, ((p i : ℝ) ^ α)⁻¹) ≤
          ∏ i : Fin n, ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)‖⁻¹ ^ 2 := by
        have he : Real.exp (-2 * ∑ i : Fin n, ((p i : ℝ) ^ α)⁻¹) =
            ∏ i : Fin n, Real.exp (-2 * (((p i : ℝ) ^ α)⁻¹)) := by
          rw [← Real.exp_sum, mul_sum]
        rw [he]
        exact prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun i _ => hterm_ge i
      have hsum_le : (∑ i : Fin n, ((p i : ℝ) ^ α)⁻¹) ≤ S_α := by
        have h1 : (∑ i : Fin n, ((p i : ℝ) ^ α)⁻¹) = ∑ m ∈ Finset.univ.image p, ((m : ℝ) ^ α)⁻¹ :=
          (Finset.sum_image (f := fun m : ℕ => ((m : ℝ) ^ α)⁻¹) fun i _ j _ hij => hinj hij).symm
        rw [h1]
        exact hsum_α.sum_le_tsum (Finset.univ.image p) fun m _ => by positivity
      exact (Real.exp_le_exp.mpr (by linarith)).trans hprod_exp
    -- Upper bound on `|torusSum|` of `tentBump`
    have hts_φ : TraceSummable (ampl tentBump (fun i => Real.log (p i)) x) :=
      traceSummable_ampl hα0 (fun y _ => tentBump_le_five_rpow_exp hα0 y) hℓ le_rfl
    have hpert_le : |torusSum (ampl tentBump (fun i => Real.log (p i)) x) θ| ≤
        K_α * Real.exp (-α * x) := by
      refine (abs_torusSum_le hts_φ θ).trans ?_
      have hterm_b : ∀ k : Fin n → ℕ,
          |ampl tentBump (fun i => Real.log (p i)) x k| * chiSize k ≤
            ((5 : ℝ) ^ α * B_η * Real.exp (-α * x)) * ((primeMonoidProd p k : ℝ) ^ β)⁻¹ := by
        intro k
        have hNpos : (0 : ℝ) < primeMonoidProd p k := by exact_mod_cast primeMonoidProd_pos hp k
        have ha_b : |ampl tentBump (fun i => Real.log (p i)) x k| ≤
            (5 : ℝ) ^ α * Real.exp (-α * x) * ((primeMonoidProd p k : ℝ) ^ α)⁻¹ := by
          rw [ampl, ← log_primeMonoidProd hp k]
          refine (tentBump_le_five_rpow_exp hα0 _).trans (le_of_eq ?_)
          rw [mul_add, Real.exp_add, ← mul_assoc]
          congr 1
          rw [← Real.rpow_neg hNpos.le, Real.rpow_def_of_pos hNpos]
          congr 1; ring
        have hc_b := hchi n p hp hinj k
        calc |ampl tentBump (fun i => Real.log (p i)) x k| * chiSize k
            ≤ ((5 : ℝ) ^ α * Real.exp (-α * x) * ((primeMonoidProd p k : ℝ) ^ α)⁻¹) *
                (B_η * (primeMonoidProd p k : ℝ) ^ η) :=
              mul_le_mul ha_b hc_b (chiSize_nonneg k) (by positivity)
          _ = ((5 : ℝ) ^ α * B_η * Real.exp (-α * x)) * ((primeMonoidProd p k : ℝ) ^ β)⁻¹ := by
              have hrpow : ((primeMonoidProd p k : ℝ) ^ α)⁻¹ * (primeMonoidProd p k : ℝ) ^ η =
                  ((primeMonoidProd p k : ℝ) ^ β)⁻¹ := by
                rw [← Real.rpow_neg hNpos.le, ← Real.rpow_neg hNpos.le, ← Real.rpow_add hNpos]
                congr 1; simp only [η, β]; ring
              calc ((5 : ℝ) ^ α * Real.exp (-α * x) * ((primeMonoidProd p k : ℝ) ^ α)⁻¹) *
                    (B_η * (primeMonoidProd p k : ℝ) ^ η)
                  = ((5 : ℝ) ^ α * B_η * Real.exp (-α * x)) *
                      (((primeMonoidProd p k : ℝ) ^ α)⁻¹ * (primeMonoidProd p k : ℝ) ^ η) := by ring
                _ = _ := by rw [hrpow]
      have hmaj_sum : Summable (fun k : Fin n → ℕ =>
          ((5 : ℝ) ^ α * B_η * Real.exp (-α * x)) * ((primeMonoidProd p k : ℝ) ^ β)⁻¹) :=
        (hsum_β.comp_injective (primeMonoidProd_injective hp hinj)).mul_left _
      refine (hts_φ.tsum_le_tsum hterm_b hmaj_sum).trans ?_
      rw [tsum_mul_left]
      have hcomp_le : (∑' k : Fin n → ℕ, ((primeMonoidProd p k : ℝ) ^ β)⁻¹) ≤ S_β := by
        refine (hsum_β.comp_injective (primeMonoidProd_injective hp hinj)).tsum_le_of_sum_le fun s => ?_
        have hs : (∑ k ∈ s, ((primeMonoidProd p k : ℝ) ^ β)⁻¹) =
            ∑ m ∈ s.image (primeMonoidProd p), ((m : ℝ) ^ β)⁻¹ :=
          (Finset.sum_image (f := fun m : ℕ => ((m : ℝ) ^ β)⁻¹) fun a _ b _ hab =>
            primeMonoidProd_injective hp hinj hab).symm
        simp only [Function.comp_apply]
        rw [hs]
        exact hsum_β.sum_le_tsum (s.image (primeMonoidProd p)) fun m _ => by positivity
      calc ((5 : ℝ) ^ α * B_η * Real.exp (-α * x)) * ∑' k, ((primeMonoidProd p k : ℝ) ^ β)⁻¹
          ≤ ((5 : ℝ) ^ α * B_η * Real.exp (-α * x)) * S_β :=
            mul_le_mul_of_nonneg_left hcomp_le (by positivity)
        _ = K_α * Real.exp (-α * x) := by simp only [K_α]; ring
    -- Combine by linearity of `torusSum`
    have hts_e : TraceSummable (ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) x) :=
      traceSummable_ampl hα0 (fun y _ => by rw [abs_of_pos (Real.exp_pos _), one_mul]) hℓ le_rfl
    have hlin : torusSum (ampl f (fun i => Real.log (p i)) x) θ =
        torusSum (ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) x) θ -
          ε * torusSum (ampl tentBump (fun i => Real.log (p i)) x) θ := by
      have hampl : ∀ k, ampl f (fun i => Real.log (p i)) x k * chiProd θ k =
          ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) x k * chiProd θ k -
            ε * (ampl tentBump (fun i => Real.log (p i)) x k * chiProd θ k) := fun k => by
        simp only [ampl, f]; ring
      rw [torusSum, torusSum, torusSum]
      simp_rw [hampl]
      rw [Summable.tsum_sub (summable_term hts_e θ) ((summable_term hts_φ θ).mul_left ε),
        tsum_mul_left]
    rw [hlin]
    have hεK : ε * K_α ≤ c_α / 2 := by
      have : ε * (K_α + 1) ≤ c_α / 2 := by
        have := mul_le_mul_of_nonneg_right hε_le (show 0 ≤ K_α + 1 by positivity)
        have he : ε₀ * (K_α + 1) = c_α / 2 := by simp only [ε₀]; field_simp
        rwa [he] at this
      linarith
    have hp1 : ε * torusSum (ampl tentBump (fun i => Real.log (p i)) x) θ ≤
        (c_α / 2) * Real.exp (-α * x) := by
      calc ε * torusSum (ampl tentBump (fun i => Real.log (p i)) x) θ
          ≤ ε * (K_α * Real.exp (-α * x)) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans hpert_le) hε_pos.le
        _ = (ε * K_α) * Real.exp (-α * x) := by ring
        _ ≤ (c_α / 2) * Real.exp (-α * x) :=
            mul_le_mul_of_nonneg_right hεK (Real.exp_pos _).le
    have hfloor_pos : 0 < (c_α / 2) * Real.exp (-α * x) := by positivity
    linarith
  · -- Strict determinant violation `f(2 log 2) * f(2 log 3) < f(log 2 + log 3)^2`
    have h6 : tentBump (Real.log 2 + Real.log 3) = 0 := by
      apply tentBump_eq_zero_of_ge_log_five
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have h9 : tentBump (2 * Real.log 3) = 0 := by
      apply tentBump_eq_zero_of_ge_log_five
      have : 2 * Real.log 3 = Real.log 9 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      rw [this]
      exact Real.log_le_log (by norm_num) (by norm_num)
    simp only [f, tentBump_two_log_two, mul_one, h6, h9, mul_zero, sub_zero]
    have he_eq : Real.exp (-α * (2 * Real.log 2)) * Real.exp (-α * (2 * Real.log 3)) =
        Real.exp (-α * (Real.log 2 + Real.log 3)) ^ 2 := by
      rw [← Real.exp_add, sq, ← Real.exp_add]
      congr 1; ring
    have hpos3 : 0 < Real.exp (-α * (2 * Real.log 3)) := Real.exp_pos _
    nlinarith
  · -- Failure of `IsExpConvexFrom 0 f`
    intro hEC
    have h6 : tentBump (Real.log 2 + Real.log 3) = 0 := by
      apply tentBump_eq_zero_of_ge_log_five
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have h9 : tentBump (2 * Real.log 3) = 0 := by
      apply tentBump_eq_zero_of_ge_log_five
      have : 2 * Real.log 3 = Real.log 9 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      rw [this]
      exact Real.log_le_log (by norm_num) (by norm_num)
    let t : Fin 2 → ℝ := ![Real.log 2, Real.log 3]
    let c' : Fin 2 → ℂ := ![(Real.exp (-α * Real.log 3) : ℂ), -(Real.exp (-α * Real.log 2) : ℂ)]
    have ht : ∀ i ∈ (univ : Finset (Fin 2)), 0 ≤ t i := by
      intro i _
      fin_cases i
      · exact (Real.log_pos (by norm_num)).le
      · exact (Real.log_pos (by norm_num)).le
    have hval := hEC (Fin 2) univ t c' ht
    rw [Fin.sum_univ_two] at hval
    simp only [Fin.sum_univ_two, t, c', Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_add, map_neg, Complex.conj_ofReal] at hval
    have h11 : Real.log 2 + Real.log 2 = 2 * Real.log 2 := by ring
    have h22 : Real.log 3 + Real.log 3 = 2 * Real.log 3 := by ring
    have h21 : Real.log 3 + Real.log 2 = Real.log 2 + Real.log 3 := by ring
    rw [h11, h22, h21] at hval
    simp only [f, tentBump_two_log_two, mul_one, h6, h9, mul_zero, sub_zero] at hval
    simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, Complex.ofReal_re] at hval
    have he1 : Real.exp (-α * Real.log 3) * Real.exp (-α * Real.log 3) *
        Real.exp (-α * (2 * Real.log 2)) =
        Real.exp (-2 * α * (Real.log 2 + Real.log 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have he2 : Real.exp (-α * Real.log 3) * Real.exp (-α * Real.log 2) *
        Real.exp (-α * (Real.log 2 + Real.log 3)) =
        Real.exp (-2 * α * (Real.log 2 + Real.log 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have he3 : Real.exp (-α * Real.log 2) * Real.exp (-α * Real.log 2) *
        Real.exp (-α * (2 * Real.log 3)) =
        Real.exp (-2 * α * (Real.log 2 + Real.log 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hpos_c : 0 < Real.exp (-α * Real.log 3) * Real.exp (-α * Real.log 3) * ε := by positivity
    nlinarith [he1, he2, he3]

/-! ### Critical Euler-abscissa collapse (`0 < α ≤ 1`) -/

theorem cosSum_zero_angle (k : ℕ) : cosSum 0 k = (k : ℝ) + 1 := by
  simp [cosSum]

private theorem one_add_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {g : ι → ℝ}
    (hg : ∀ i ∈ s, 0 ≤ g i) : 1 + ∑ i ∈ s, g i ≤ ∏ i ∈ s, (1 + g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha0 : 0 ≤ g a := hg a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, g i := Finset.sum_nonneg fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hih := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    nlinarith

/-- Arbitrarily large partial sums of prime reciprocals on `{q prime | 5 ≤ q}`. -/
private theorem exists_finset_primes_ge_five_sum_gt (B : ℝ) :
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ 5 ≤ q) ∧ B < ∑ q ∈ S, (q : ℝ)⁻¹ := by
  classical
  have hdiv : ¬ Summable (fun p : Nat.Primes => (1 / (p : ℝ))) := Nat.Primes.not_summable_one_div
  have hunb : ∃ T : Finset Nat.Primes, B + 2 < ∑ p ∈ T, (1 / (p : ℝ)) := by
    by_contra hle
    push Not at hle
    exact hdiv (summable_of_sum_le (fun p => by positivity) hle)
  obtain ⟨T, hT⟩ := hunb
  let S₀ : Finset ℕ := T.image Subtype.val
  have hsum_eq : (∑ p ∈ T, (1 / (p : ℝ))) = ∑ q ∈ S₀, (q : ℝ)⁻¹ := by
    have h1 : (∑ q ∈ S₀, (q : ℝ)⁻¹) = ∑ p ∈ T, (p.1 : ℝ)⁻¹ :=
      Finset.sum_image (f := fun q : ℕ => (q : ℝ)⁻¹) fun a _ b _ hab => Subtype.ext hab
    rw [h1]
    exact sum_congr rfl fun p _ => one_div _
  rw [hsum_eq] at hT
  set S := S₀.filter (fun q => 5 ≤ q)
  have hS_prop : ∀ q ∈ S, q.Prime ∧ 5 ≤ q := fun q hq => by
    obtain ⟨hq0, h5⟩ := Finset.mem_filter.mp hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq0
    exact ⟨p.2, h5⟩
  have hsmall : ∑ q ∈ S₀.filter (fun q => ¬(5 ≤ q)), (q : ℝ)⁻¹ ≤ 2 := by
    have hsub : S₀.filter (fun q => ¬(5 ≤ q)) ⊆ ({2, 3} : Finset ℕ) := by
      intro q hq
      obtain ⟨hq0, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq0
      have hp2 := p.2.two_le
      have hp4 : p.1 ≠ 4 := fun h4 => by
        have hp_pr := p.2; rw [h4] at hp_pr; exact absurd hp_pr (by decide)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
    rw [sum_pair (by decide)]
    norm_num
  have hsplit := sum_filter_add_sum_filter_not S₀ (fun q => 5 ≤ q) (fun q : ℕ => (q : ℝ)⁻¹)
  refine ⟨S, hS_prop, by linarith⟩

/-- **Critical Euler-abscissa collapse (`0 < α ≤ 1`).** For every `α ∈ (0, 1]` and every
nonnegative function `ψ` supported below `log 5` with `ψ(2 log 2) > 0`, `e^{−αy} − ψ(y)` takes
strictly negative torus sums at `x = 0` on a finite set of primes. -/
theorem exists_prime_set_torusSum_neg_of_le_one {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {ψ : ℝ → ℝ} (hψ_nn : ∀ y, 0 ≤ y → 0 ≤ ψ y) (hψ_supp : ∀ y, Real.log 5 ≤ y → ψ y = 0)
    (hψ_pos : 0 < ψ (2 * Real.log 2)) :
    ∃ (n : ℕ) (p : Fin n → ℕ) (θ : Fin n → ℝ),
      (∀ i, (p i).Prime) ∧ Function.Injective p ∧
        torusSum (ampl (fun y => Real.exp (-α * y) - ψ y) (fun i => Real.log (p i)) 0) θ < 0 := by
  classical
  set C₂ : ℝ := (1 - Real.exp (-α * Real.log 2))⁻¹ ^ 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hC₂_pos : 0 < C₂ := by
    have hexp2 : Real.exp (-α * Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    have hd : 0 < 1 - Real.exp (-α * Real.log 2) := by linarith
    positivity
  set B : ℝ := C₂ / (3 * ψ (2 * Real.log 2)) + 1
  obtain ⟨S, hS, hB⟩ := exists_finset_primes_ge_five_sum_gt B
  have h2not : 2 ∉ S := fun h2 => by have := (hS 2 h2).2; omega
  let e : Fin S.card ≃ S := S.equivFin.symm
  let p : Fin (S.card + 1) → ℕ := Fin.cons 2 (fun i => (e i : ℕ))
  let θ : Fin (S.card + 1) → ℝ := Fin.cons 0 (fun _ => π)
  have hp : ∀ i, (p i).Prime := Fin.cases Nat.prime_two (fun i => (hS _ (e i).2).1)
  have hinj : Function.Injective p := by
    intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · rfl
    · exfalso
      simp only [p, Fin.cons_zero, Fin.cons_succ] at hij
      exact h2not (hij ▸ (e j').2)
    · exfalso
      simp only [p, Fin.cons_zero, Fin.cons_succ] at hij
      exact h2not (hij.symm ▸ (e i').2)
    · simp only [p, Fin.cons_succ] at hij
      exact congrArg Fin.succ (e.injective (Subtype.ext hij))
  have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
  -- Upper bound on `torusSum` of `e^{−αy}` at `x = 0`
  have hexp_val : torusSum (ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) 0) θ <
      3 * ψ (2 * Real.log 2) := by
    rw [torusSum_ampl_exp_neg hα0 hℓ 0 θ, mul_zero, Real.exp_zero, one_mul, Fin.prod_univ_succ]
    have h0_eq : ‖1 - (Real.exp (-α * Real.log (p 0)) : ℂ) * Complex.exp ((θ 0 : ℂ) * Complex.I)‖⁻¹ ^ 2 = C₂ := by
      simp only [p, θ, Fin.cons_zero, Nat.cast_ofNat, Complex.ofReal_zero, zero_mul,
        Complex.exp_zero, mul_one]
      have hlt : Real.exp (-α * Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
      have h1 : ‖(1 : ℂ) - (Real.exp (-α * Real.log 2) : ℂ)‖ = 1 - Real.exp (-α * Real.log 2) := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
      rw [h1]
    rw [h0_eq]
    have htail_le : (∏ i : Fin S.card,
        ‖1 - (Real.exp (-α * Real.log (p i.succ)) : ℂ) *
          Complex.exp ((θ i.succ : ℂ) * Complex.I)‖⁻¹ ^ 2) ≤ (1 + ∑ q ∈ S, (q : ℝ)⁻¹)⁻¹ := by
      have hfac : ∀ i : Fin S.card,
          1 + ((e i : ℕ) : ℝ)⁻¹ ≤
            ‖1 - (Real.exp (-α * Real.log (p i.succ)) : ℂ) *
              Complex.exp ((θ i.succ : ℂ) * Complex.I)‖ ^ 2 := by
        intro i
        set q : ℕ := (e i : ℕ)
        have hq5 : 5 ≤ q := (hS q (e i).2).2
        have hq_pos : (0 : ℝ) < q := by positivity
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
        have hpi : Complex.exp ((π : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
        simp only [p, θ, Fin.cons_succ, hpi, mul_neg, mul_one, sub_neg_eq_add]
        have hnorm : ‖(1 : ℂ) + (Real.exp (-α * Real.log q) : ℂ)‖ =
            1 + Real.exp (-α * Real.log q) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
        rw [hnorm]
        have hexp_ge : (q : ℝ)⁻¹ ≤ Real.exp (-α * Real.log q) := by
          have h1 : (q : ℝ) ^ (-1 : ℝ) ≤ (q : ℝ) ^ (-α) :=
            Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
          rw [Real.rpow_neg_one] at h1
          rwa [Real.rpow_def_of_pos hq_pos, mul_comm (Real.log q) (-α)] at h1
        nlinarith [sq_nonneg (Real.exp (-α * Real.log q)), Real.exp_pos (-α * Real.log q), hexp_ge]
      have hprod_ge : 1 + ∑ q ∈ S, (q : ℝ)⁻¹ ≤
          ∏ i : Fin S.card, ‖1 - (Real.exp (-α * Real.log (p i.succ)) : ℂ) *
            Complex.exp ((θ i.succ : ℂ) * Complex.I)‖ ^ 2 := by
        have hsum_e : ∑ q ∈ S, (q : ℝ)⁻¹ = ∑ i : Fin S.card, ((e i : ℕ) : ℝ)⁻¹ := by
          rw [Equiv.sum_comp e (fun z : S => ((z.1 : ℕ) : ℝ)⁻¹)]
          exact (Finset.sum_coe_sort S (fun q : ℕ => (q : ℝ)⁻¹)).symm
        rw [hsum_e]
        exact (one_add_sum_le_prod Finset.univ fun i _ => by positivity).trans
          (prod_le_prod (fun _ _ => by positivity) fun i _ => hfac i)
      have hpos_lhs : 0 < 1 + ∑ q ∈ S, (q : ℝ)⁻¹ :=
        add_pos_of_pos_of_nonneg one_pos (sum_nonneg fun _ _ => by positivity)
      have hinv_prod : (∏ i : Fin S.card,
          ‖1 - (Real.exp (-α * Real.log (p i.succ)) : ℂ) *
            Complex.exp ((θ i.succ : ℂ) * Complex.I)‖⁻¹ ^ 2) =
          (∏ i : Fin S.card, ‖1 - (Real.exp (-α * Real.log (p i.succ)) : ℂ) *
            Complex.exp ((θ i.succ : ℂ) * Complex.I)‖ ^ 2)⁻¹ := by
        simp_rw [inv_pow]
        rw [prod_inv_distrib]
      rw [hinv_prod]
      exact inv_anti₀ hpos_lhs hprod_ge
    have hB_pos : 0 < B := by simp only [B]; positivity
    have hsum_gt : B < 1 + ∑ q ∈ S, (q : ℝ)⁻¹ := by linarith
    have hstrict : C₂ * (1 + ∑ q ∈ S, (q : ℝ)⁻¹)⁻¹ < 3 * ψ (2 * Real.log 2) := by
      have h1 : (1 + ∑ q ∈ S, (q : ℝ)⁻¹)⁻¹ < B⁻¹ := inv_strictAnti₀ hB_pos hsum_gt
      have h2 : C₂ * B⁻¹ < 3 * ψ (2 * Real.log 2) := by
        rw [inv_eq_one_div, mul_one_div, div_lt_iff₀ hB_pos]
        have : C₂ < (C₂ / (3 * ψ (2 * Real.log 2)) + 1) * (3 * ψ (2 * Real.log 2)) := by
          rw [add_mul, div_mul_cancel₀ _ (by positivity)]; linarith
        rw [mul_comm] at this
        simpa only [B] using this
      exact (mul_lt_mul_of_pos_left h1 hC₂_pos).trans h2
    exact (mul_le_mul_of_nonneg_left htail_le hC₂_pos.le).trans_lt hstrict
  -- Exact evaluation of `torusSum` of `ψ` on `{k | k 0 < 3 ∧ ∀ i, k i.succ = 0}`
  let k_m : Fin 3 → (Fin (S.card + 1) → ℕ) := fun m => Fin.cons m.1 (fun _ => 0)
  have hk_m_inj : Function.Injective k_m := fun a b hab => by
    have := congrFun hab 0
    simp only [k_m, Fin.cons_zero] at this
    exact Fin.ext this
  have hvanish : ∀ k : Fin (S.card + 1) → ℕ, k ∉ Finset.univ.image k_m →
      ampl ψ (fun i => Real.log (p i)) 0 k = 0 := by
    intro k hk
    rw [ampl, zero_add]
    apply hψ_supp
    by_cases htail0 : ∀ i : Fin S.card, k i.succ = 0
    · have hk0_ge : 3 ≤ k 0 := by
        by_contra hlt
        push Not at hlt
        apply hk
        refine Finset.mem_image.mpr ⟨⟨k 0, hlt⟩, Finset.mem_univ _, ?_⟩
        ext j
        refine Fin.cases rfl (fun i => (htail0 i).symm) j
      rw [Fin.sum_univ_succ]
      have hnn : 0 ≤ ∑ i : Fin S.card, (k i.succ : ℝ) * Real.log (p i.succ) :=
        sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hℓ i.succ).le
      have h3log2 : Real.log 5 ≤ (3 : ℝ) * Real.log 2 := by
        have : (3 : ℝ) * Real.log 2 = Real.log 8 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
        rw [this]
        exact Real.log_le_log (by norm_num) (by norm_num)
      have hk0_cast : (3 : ℝ) ≤ k 0 := by exact_mod_cast hk0_ge
      simp only [p, Fin.cons_zero, Nat.cast_ofNat]
      nlinarith
    · push Not at htail0
      obtain ⟨i₀, hi₀⟩ := htail0
      have hk1 : (1 : ℝ) ≤ k i₀.succ := by exact_mod_cast Nat.pos_of_ne_zero hi₀
      have hp5 : 5 ≤ p i₀.succ := (hS _ (e i₀).2).2
      have hlog5 : Real.log 5 ≤ Real.log (p i₀.succ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hp5)
      have hsingle : Real.log (p i₀.succ) ≤
          ∑ j : Fin (S.card + 1), (k j : ℝ) * Real.log (p j) := by
        refine le_trans ?_ (single_le_sum (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hℓ j).le)
          (Finset.mem_univ i₀.succ))
        nlinarith [hℓ i₀.succ]
      linarith
  have hts_ψ : TraceSummable (ampl ψ (fun i => Real.log (p i)) 0) := by
    refine summable_of_ne_finset_zero (s := Finset.univ.image k_m) fun k hk => ?_
    rw [hvanish k hk, abs_zero, zero_mul]
  have hψ_val : 3 * ψ (2 * Real.log 2) ≤
      torusSum (ampl ψ (fun i => Real.log (p i)) 0) θ := by
    rw [torusSum, tsum_eq_sum fun k hk => by rw [hvanish k hk, zero_mul],
      Finset.sum_image fun a _ b _ hab => hk_m_inj hab]
    have hterm_m : ∀ m : Fin 3,
        ampl ψ (fun i => Real.log (p i)) 0 (k_m m) * chiProd θ (k_m m) =
          ψ ((m.1 : ℝ) * Real.log 2) * ((m.1 : ℝ) + 1) := by
      intro m
      have hsum_k : (∑ i : Fin (S.card + 1), (k_m m i : ℝ) * Real.log (p i)) =
          (m.1 : ℝ) * Real.log 2 := by
        rw [Fin.sum_univ_succ]
        simp [k_m, p]
      have hchi_k : chiProd θ (k_m m) = (m.1 : ℝ) + 1 := by
        rw [chiProd, Fin.prod_univ_succ]
        simp [k_m, θ, cosSum_zero, cosSum_zero_angle]
      rw [ampl, zero_add, hsum_k, hchi_k]
    simp_rw [hterm_m]
    rw [Fin.sum_univ_three]
    have h0 : 0 ≤ ψ ((0 : ℝ) * Real.log 2) := hψ_nn _ (by norm_num)
    have h1 : 0 ≤ ψ ((1 : ℝ) * Real.log 2) := hψ_nn _ (by positivity)
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat] at *
    linarith
  -- Combine at `x = 0`
  have hts_e : TraceSummable (ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) 0) :=
    traceSummable_ampl hα0 (fun y _ => by rw [abs_of_pos (Real.exp_pos _), one_mul]) hℓ le_rfl
  refine ⟨S.card + 1, p, θ, hp, hinj, ?_⟩
  have hlin : torusSum (ampl (fun y => Real.exp (-α * y) - ψ y) (fun i => Real.log (p i)) 0) θ =
      torusSum (ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) 0) θ -
        torusSum (ampl ψ (fun i => Real.log (p i)) 0) θ := by
    have hampl : ∀ k, ampl (fun y => Real.exp (-α * y) - ψ y) (fun i => Real.log (p i)) 0 k * chiProd θ k =
        ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) 0 k * chiProd θ k -
          ampl ψ (fun i => Real.log (p i)) 0 k * chiProd θ k := fun k => by
      simp only [ampl]; ring
    rw [torusSum, torusSum, torusSum]
    simp_rw [hampl]
    rw [Summable.tsum_sub (summable_term hts_e θ) (summable_term hts_ψ θ)]
  linarith

/-- **The Euler-abscissa dichotomy for `e^{−αy} − ε · tentBump(y)`.**
For `α > 1`, small positive perturbations remain strictly torus-positive at every base point while
leaving the exponentially convex cone; for `0 < α ≤ 1`, *every* positive perturbation already leaves
the torus cone at the single fixed base point `x = 0`. -/
theorem euler_abscissa_perturbation_dichotomy :
    (∀ α : ℝ, 1 < α → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      (∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
        ∀ (x : ℝ) (θ : Fin n → ℝ),
          0 < torusSum (ampl (fun y => Real.exp (-α * y) - ε * tentBump y)
            (fun i => Real.log (p i)) x) θ) ∧
      ¬ IsExpConvexFrom 0 (fun y => Real.exp (-α * y) - ε * tentBump y)) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (p : Fin n → ℕ) (θ : Fin n → ℝ),
        (∀ i, (p i).Prime) ∧ Function.Injective p ∧
          torusSum (ampl (fun y => Real.exp (-α * y) - ε * tentBump y)
            (fun i => Real.log (p i)) 0) θ < 0) := by
  refine ⟨fun α hα => ?_, fun α hα0 hα1 ε hε => ?_⟩
  · obtain ⟨ε₀, hε₀, h⟩ := exists_supercritical_not_expConvex hα
    exact ⟨ε₀, hε₀, fun ε h1 h2 => ⟨(h ε h1 h2).2.2.2.1, (h ε h1 h2).2.2.2.2.2⟩⟩
  · exact exists_prime_set_torusSum_neg_of_le_one hα0 hα1
      (fun y _ => mul_nonneg hε.le (tentBump_nonneg y))
      (fun y hy => by rw [tentBump_eq_zero_of_ge_log_five hy, mul_zero])
      (by rw [tentBump_two_log_two, mul_one]; exact hε)

#print axioms cosSum_mul_cosSum
#print axioms integral_torusSum_mul_sq_eq_dirichletHankel
#print axioms nonneg_torusSum_iff_dirichletHankel_nonneg
#print axioms torusPositiveAt_iff_dirichletHankel_nonneg
#print axioms exists_supercritical_not_expConvex
#print axioms exists_prime_set_torusSum_neg_of_le_one
#print axioms euler_abscissa_perturbation_dichotomy

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
