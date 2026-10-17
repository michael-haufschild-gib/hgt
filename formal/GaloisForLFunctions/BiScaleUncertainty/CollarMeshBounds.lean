import GaloisForLFunctions.BiScaleUncertainty.RightNodeCollarPartition

/-!
# Cutoff-uniform logarithmic collar mesh bounds

The density at node j is at most 8/sqrt(j). Summing the square-root telescoping
bound controls every admissible physical fibre by 32 sqrt(N). Near the origin,
the reciprocal singular weight is at most twice the offset.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

theorem exp_logarithmicCollarNode_half (k : ℕ) :
    Real.exp (logarithmicCollarNode k / 2) = Real.sqrt ((k + 2 : ℕ) : ℝ) := by
  have hN : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
  have hs : Real.exp (logarithmicCollarNode k / 2) ^ 2 = ((k + 2 : ℕ) : ℝ) := by
    rw [pow_two, ← Real.exp_add, show logarithmicCollarNode k / 2 +
      logarithmicCollarNode k / 2 = logarithmicCollarNode k by ring]
    exact Real.exp_log hN
  rw [← hs, Real.sqrt_sq (Real.exp_pos _).le]

theorem exp_neg_two_collarRadius :
    Real.exp (-2 * logarithmicCollarRadius) = (1 / 2 : ℝ) := by
  rw [show -2 * logarithmicCollarRadius = -Real.log 2 by
    unfold logarithmicCollarRadius; ring, Real.exp_neg, Real.exp_log (by norm_num)]
  simp only [one_div]

theorem archWeight_at_signed_node_le (k : ℕ) (σ : Bool) {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    archLevySinhWeight (logarithmicCollarNode k + collarSignedOffset σ y) ≤
      8 / Real.sqrt ((k + 2 : ℕ) : ℝ) := by
  let x := logarithmicCollarNode k + collarSignedOffset σ y
  have hnode := logarithmicCollarNode_ge_log_two k
  have hx : logarithmicCollarRadius ≤ x := by
    cases σ <;> simp only [x, collarSignedOffset, Bool.false_eq_true, ↓reduceIte] <;>
      unfold logarithmicCollarRadius at * <;> linarith [hy.1, hy.2]
  have hlow : logarithmicCollarNode k - logarithmicCollarRadius ≤ x := by
    cases σ <;> simp only [x, collarSignedOffset, Bool.false_eq_true, ↓reduceIte] <;>
      linarith [hy.1, hy.2, logarithmicCollarRadius_pos]
  have hw := archWeight_le_cutoff_exponential logarithmicCollarRadius_pos hx
  rw [exp_neg_two_collarRadius] at hw
  norm_num at hw
  have he : Real.exp (-x / 2) ≤
      Real.exp (logarithmicCollarRadius / 2) / Real.sqrt ((k + 2 : ℕ) : ℝ) := by
    rw [← exp_logarithmicCollarNode_half, ← Real.exp_sub]
    exact Real.exp_le_exp.mpr (by linarith)
  have heδ : Real.exp (logarithmicCollarRadius / 2) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := by
        apply Real.exp_le_exp.mpr
        unfold logarithmicCollarRadius
        linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      _ = 2 := Real.exp_log (by norm_num)
  have he' := he.trans (div_le_div_of_nonneg_right heδ (Real.sqrt_nonneg _))
  change archLevySinhWeight x ≤ _
  calc
    _ ≤ 4 * Real.exp (-x / 2) := by
      simpa only [show -(1 / 2 * x : ℝ) = -x / 2 by ring] using hw
    _ ≤ 4 * (2 / Real.sqrt ((k + 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left he' (by norm_num)
    _ = _ := by ring

theorem one_le_two_mul_offset_weight {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    1 ≤ 2 * y * archLevySinhWeight y := by
  have hd : 0 < 1 - Real.exp (-2 * y) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [hy.1]))
  have he : 1 - Real.exp (-2 * y) ≤ 2 * y := by
    have h := Real.add_one_le_exp (-2 * y)
    linarith
  have hp : (1 / 2 : ℝ) ≤ Real.exp (-y / 2) := by
    have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have h := Real.exp_le_exp.mpr
      (show -Real.log 2 ≤ -y / 2 by
        unfold logarithmicCollarRadius at hy
        linarith [hy.2])
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using h
  have hw : 2 * y * archLevySinhWeight y =
      (4 * y * Real.exp (-y / 2)) / (1 - Real.exp (-2 * y)) := by
    rw [archLevySinhWeight, RHTower.ArchimedeanAnomaly.exp_half_div_sinh_eq hy.1,
      RHTower.archLevyDensity]
    ring
  rw [hw]
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_nonneg hy.1.le (sub_nonneg.mpr hp)]

theorem inverse_sqrt_step (k : ℕ) :
    1 / Real.sqrt ((k + 2 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((k + 2 : ℕ) : ℝ) - Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) by positivity)
  have ht := Real.sq_sqrt (show (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by positivity)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < ((k + 2 : ℕ) : ℝ)))).mpr
  have hd := sq_nonneg (Real.sqrt ((k + 2 : ℕ) : ℝ) - Real.sqrt ((k + 1 : ℕ) : ℝ))
  push_cast at hs ht hd ⊢
  nlinarith

theorem sum_range_inverse_sqrt_le (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / Real.sqrt ((k + 2 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := add_le_add ih (inverse_sqrt_step n)
      have h' : (∑ k ∈ Finset.range n, 1 / Real.sqrt ((k + 2 : ℕ) : ℝ)) +
          1 / Real.sqrt ((n + 2 : ℕ) : ℝ) ≤ 2 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
        linarith
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using h'

def logarithmicArrayMass (n : ℕ) (a : Bool → ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (a false k + a true k)

theorem logarithmicArrayMass_le_sqrt_cutoff (n : ℕ) (a : Bool → ℕ → ℝ)
    (ha : ∀ σ k, k ∈ Finset.range (n + 1) →
      a σ k ≤ 8 / Real.sqrt ((k + 2 : ℕ) : ℝ)) :
    logarithmicArrayMass n a ≤ 32 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
  have h : logarithmicArrayMass n a ≤
      16 * ∑ k ∈ Finset.range (n + 1), 1 / Real.sqrt ((k + 2 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have h1 := ha false k hk
    have h2 := ha true k hk
    calc
      _ ≤ 8 / Real.sqrt ((k + 2 : ℕ) : ℝ) + 8 / Real.sqrt ((k + 2 : ℕ) : ℝ) :=
        add_le_add h1 h2
      _ = _ := by ring
  have hs := mul_le_mul_of_nonneg_left (sum_range_inverse_sqrt_le (n + 1))
    (by norm_num : (0 : ℝ) ≤ 16)
  norm_num only [Nat.add_assoc] at hs
  linarith

private theorem sum_range_le_of_support (n L : ℕ) (a b : ℕ → ℝ)
    (hb : ∀ k, 0 ≤ b k) (hab : ∀ k < n, a k ≤ b k)
    (hz : ∀ k < n, L ≤ k → a k = 0) :
    (∑ k ∈ Finset.range n, a k) ≤ ∑ k ∈ Finset.range L, b k := by
  rcases le_total n L with h | h
  · refine (Finset.sum_le_sum (fun k hk => hab k (Finset.mem_range.mp hk))).trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le h)
    · exact fun k _ _ => hb k
  · have heq : (∑ k ∈ Finset.range n, a k) = ∑ k ∈ Finset.range L, a k := by
      symm
      apply Finset.sum_subset
      · intro k hk
        exact Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le h)
      · intro k hk hkL
        exact hz k (Finset.mem_range.mp hk) (by simpa only [Finset.mem_range, not_lt] using hkL)
    rw [heq]
    apply Finset.sum_le_sum
    intro k hk
    exact hab k ((Finset.mem_range.mp hk).trans_le h)

/-- The mesh removes the dependence on the largest available node. -/
theorem logarithmicArrayMass_le_inverse_sqrt_offset (n : ℕ) (a : Bool → ℕ → ℝ)
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1)
    (ha : ∀ σ k, k ∈ Finset.range (n + 1) →
      a σ k ≤ 8 / Real.sqrt ((k + 2 : ℕ) : ℝ))
    (hmesh : ∀ σ k, k ∈ Finset.range (n + 1) → a σ k ≠ 0 →
      ((k + 1 : ℕ) : ℝ) * y ≤ 1) :
    logarithmicArrayMass n a ≤ 64 / Real.sqrt y := by
  let L : ℕ := ⌈1 / y⌉₊
  have hz (k : ℕ) (hk : k < n + 1) (hL : L ≤ k) : a false k + a true k = 0 := by
    have he (σ : Bool) : a σ k = 0 := by
      by_contra hn
      have hb := hmesh σ k (Finset.mem_range.mpr hk) hn
      have hkle : ((k + 1 : ℕ) : ℝ) ≤ (L : ℝ) :=
        ((le_div_iff₀ hy).mpr hb).trans (Nat.le_ceil (1 / y))
      have hnat : k + 1 ≤ L := by exact_mod_cast hkle
      omega
    rw [he false, he true, add_zero]
  have hsum := sum_range_le_of_support (n + 1) L
    (fun k => a false k + a true k) (fun k => 16 / Real.sqrt ((k + 2 : ℕ) : ℝ))
    (fun _ => by positivity) (fun k hk => by
      have h1 := ha false k (Finset.mem_range.mpr hk)
      have h2 := ha true k (Finset.mem_range.mpr hk)
      calc
        _ ≤ 8 / Real.sqrt ((k + 2 : ℕ) : ℝ) + 8 / Real.sqrt ((k + 2 : ℕ) : ℝ) :=
          add_le_add h1 h2
        _ = _ := by ring) hz
  have hm : logarithmicArrayMass n a ≤ 32 * Real.sqrt ((L + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range L, 16 / Real.sqrt ((k + 2 : ℕ) : ℝ) := hsum
      _ = 16 * ∑ k ∈ Finset.range L, 1 / Real.sqrt ((k + 2 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ ≤ 16 * (2 * Real.sqrt ((L + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_range_inverse_sqrt_le L) (by norm_num)
      _ = _ := by ring
  have hceil : (L : ℝ) < 1 / y + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hceil.le hy.le
  have hcancel : (1 / y) * y = 1 := div_mul_cancel₀ _ hy.ne'
  have hLy : ((L + 1 : ℕ) : ℝ) * y ≤ 4 := by
    push_cast
    nlinarith
  have hroot : Real.sqrt ((L + 1 : ℕ) : ℝ) * Real.sqrt y ≤ 2 := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((L + 1 : ℕ) : ℝ))]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,
      by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hLy⟩
  have hr := (le_div_iff₀ (Real.sqrt_pos.mpr hy)).mpr hroot
  calc
    _ ≤ 32 * Real.sqrt ((L + 1 : ℕ) : ℝ) := hm
    _ ≤ 32 * (2 / Real.sqrt y) := mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by ring

namespace PhysicalCollarPartition
variable {n : ℕ}

theorem weight_le_inverse_sqrt (ρ : PhysicalCollarPartition n) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (σ : Bool) {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    ρ.weight σ k y ≤ 8 / Real.sqrt ((k + 2 : ℕ) : ℝ) := by
  have hw := archWeight_at_signed_node_le k σ hy
  by_cases hx : logarithmicCollarNode k + collarSignedOffset σ y ∈ logarithmicPhysicalCollar n k
  · exact (mul_le_of_le_one_left (archLevySinhWeight_pos hx.2.1).le
      (ρ.share_le_one k hk _)).trans hw
  · simp only [weight, density, ρ.supported k _ hx, zero_mul]
    positivity

theorem mass_le_sqrt_cutoff (ρ : PhysicalCollarPartition n) {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    ρ.mass y ≤ 32 * Real.sqrt ((n + 2 : ℕ) : ℝ) :=
  logarithmicArrayMass_le_sqrt_cutoff n (fun σ k => ρ.weight σ k y)
    (fun σ k hk => ρ.weight_le_inverse_sqrt k hk σ hy)

theorem blockNorm_le_sqrt_cutoff (ρ : PhysicalCollarPartition n) {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    ρ.blockNorm y ≤ 32 * Real.sqrt ((n + 2 : ℕ) : ℝ) :=
  (ρ.blockNorm_le_mass y).trans (ρ.mass_le_sqrt_cutoff hy)

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
