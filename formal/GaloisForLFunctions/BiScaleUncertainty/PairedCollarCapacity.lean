import GaloisForLFunctions.BiScaleUncertainty.SignedCosetProductCoupling
import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarCutoffMonotonicity

/-!
# Capacity comparisons for paired collar arrays

Nonnegative coordinate addition increases the paired allocation kernel by at most
the added mass. Zero-padding preserves both sign norms. These statements allow
physical cutoff comparisons without discarding the cross-sign product coupling.
-/

set_option autoImplicit false
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {κ : Type*}

/-- An ordered nonnegative block changes its Euclidean size by at most added mass. -/
theorem collarBlockSize_monotone_bounds (s : Finset κ) (a b : κ → ℝ)
    (ha : ∀ k ∈ s, 0 ≤ a k) (hab : ∀ k ∈ s, a k ≤ b k) :
    0 ≤ collarBlockSize s b - collarBlockSize s a ∧
      collarBlockSize s b - collarBlockSize s a ≤ ∑ k ∈ s, (b k - a k) := by
  constructor
  · apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro k hk
    nlinarith [ha k hk, hab k hk]
  · have hrem := collarBlockRemainder_nonneg s b a
    unfold collarBlockRemainder at hrem
    have hpair := collarBlockDirection_pairing s b
    have hsum : (∑ k ∈ s, (b k - a k) * collarBlockDirection s b k) ≤
        ∑ k ∈ s, (b k - a k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_of_le_one_right (sub_nonneg.mpr (hab k hk)) (collarBlockDirection_le_one s b k hk)
    simp_rw [sub_mul, Finset.sum_sub_distrib] at hsum
    rw [hpair] at hsum
    rw [Finset.sum_sub_distrib]
    linarith

/-- One sign's aggregate coset norm for a general logarithmic coefficient array. -/
def logarithmicSignNorm (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  blockWeightNorm (logarithmicOddCosets n) (logarithmicCosetNodes n) (fun _ k => a k)

theorem logarithmicSignNorm_nonneg (n : ℕ) (a : ℕ → ℝ) : 0 ≤ logarithmicSignNorm n a :=
  blockWeightNorm_nonneg _ _ _

theorem logarithmicSignNorm_monotone_bounds (n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hab : ∀ k, a k ≤ b k) :
    0 ≤ logarithmicSignNorm n b - logarithmicSignNorm n a ∧
      logarithmicSignNorm n b - logarithmicSignNorm n a ≤
        ∑ k ∈ Finset.range (n + 1), (b k - a k) := by
  have h (p : ℕ) := collarBlockSize_monotone_bounds (logarithmicCosetNodes n p) a b
    (fun k _ => ha k) (fun k _ => hab k)
  change 0 ≤ (∑ p ∈ logarithmicOddCosets n, collarBlockSize (logarithmicCosetNodes n p) b) -
    (∑ p ∈ logarithmicOddCosets n, collarBlockSize (logarithmicCosetNodes n p) a) ∧ _
  rw [← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun p _ => (h p).1)
  · change (∑ p ∈ logarithmicOddCosets n, collarBlockSize (logarithmicCosetNodes n p) b) -
      (∑ p ∈ logarithmicOddCosets n, collarBlockSize (logarithmicCosetNodes n p) a) ≤ _
    rw [← Finset.sum_sub_distrib]
    exact (Finset.sum_le_sum (fun p _ => (h p).2)).trans_eq
      (sum_logarithmicCosetNodes n (fun k => b k - a k))

/-- The three-coordinate Euclidean support is monotone and has unit l1 capacity. -/
theorem pairedRadial_monotone_bounds (W : ℝ) {A B C D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAC : A ≤ C) (hBD : B ≤ D) :
    0 ≤ Real.sqrt (W ^ 2 + C ^ 2 + D ^ 2) - Real.sqrt (W ^ 2 + A ^ 2 + B ^ 2) ∧
      Real.sqrt (W ^ 2 + C ^ 2 + D ^ 2) - Real.sqrt (W ^ 2 + A ^ 2 + B ^ 2) ≤
        (C - A) + (D - B) := by
  let S := Real.sqrt (W ^ 2 + A ^ 2 + B ^ 2)
  have hS : S ^ 2 = W ^ 2 + A ^ 2 + B ^ 2 := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hAS : A ≤ S := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg W, sq_nonneg B])
  have hBS : B ≤ S := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg W, sq_nonneg A])
  have h₁ := mul_nonneg (sub_nonneg.mpr hAS) (sub_nonneg.mpr hAC)
  have h₂ := mul_nonneg (sub_nonneg.mpr hBS) (sub_nonneg.mpr hBD)
  have h₃ := mul_nonneg (sub_nonneg.mpr hAC) (sub_nonneg.mpr hBD)
  constructor
  · apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    nlinarith
  · have hupper : Real.sqrt (W ^ 2 + C ^ 2 + D ^ 2) ≤ S + (C - A) + (D - B) := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> nlinarith
    change Real.sqrt (W ^ 2 + C ^ 2 + D ^ 2) - S ≤ _
    linarith

/-- Paired allocation kernel on an arbitrary signed logarithmic array. -/
def logarithmicPairedArrayKernel (n : ℕ) (a : Bool → ℕ → ℝ) (W : ℝ) : ℝ :=
  W + (∑ k ∈ Finset.range (n + 1), (a false k + a true k)) -
    Real.sqrt (W ^ 2 + logarithmicSignNorm n (a false) ^ 2 + logarithmicSignNorm n (a true) ^ 2)

/-- Ordered physical capacity changes the paired kernel by between zero and added mass. -/
theorem logarithmicPairedArrayKernel_monotone_bounds (n : ℕ) (a b : Bool → ℕ → ℝ) (W : ℝ)
    (ha : ∀ σ k, 0 ≤ a σ k) (hab : ∀ σ k, a σ k ≤ b σ k) :
    0 ≤ logarithmicPairedArrayKernel n b W - logarithmicPairedArrayKernel n a W ∧
      logarithmicPairedArrayKernel n b W - logarithmicPairedArrayKernel n a W ≤
        ∑ k ∈ Finset.range (n + 1), ((b false k - a false k) + (b true k - a true k)) := by
  have hf := logarithmicSignNorm_monotone_bounds n (a false) (b false) (ha false) (hab false)
  have ht := logarithmicSignNorm_monotone_bounds n (a true) (b true) (ha true) (hab true)
  have hr := pairedRadial_monotone_bounds W (logarithmicSignNorm_nonneg n (a false))
    (logarithmicSignNorm_nonneg n (a true)) (sub_nonneg.mp hf.1) (sub_nonneg.mp ht.1)
  simp only [logarithmicPairedArrayKernel, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_sub_distrib] at hf ht
  constructor <;> linarith

theorem logarithmicPairedArrayKernel_mono (n : ℕ) (a b : Bool → ℕ → ℝ) (W : ℝ)
    (ha : ∀ σ k, 0 ≤ a σ k) (hab : ∀ σ k, a σ k ≤ b σ k) :
    logarithmicPairedArrayKernel n a W ≤ logarithmicPairedArrayKernel n b W :=
  sub_nonneg.mp (logarithmicPairedArrayKernel_monotone_bounds n a b W ha hab).1

/-- One-sided errors are bounded by added capacity, even for unordered nonnegative arrays. -/
theorem logarithmicPairedArrayKernel_error_bound (n : ℕ) (a b e : Bool → ℕ → ℝ) (W : ℝ)
    (ha : ∀ σ k, 0 ≤ a σ k) (hb : ∀ σ k, 0 ≤ b σ k) (he : ∀ σ k, 0 ≤ e σ k)
    (hab : ∀ σ k, b σ k ≤ a σ k + e σ k) :
    logarithmicPairedArrayKernel n b W - logarithmicPairedArrayKernel n a W ≤
      ∑ k ∈ Finset.range (n + 1), (e false k + e true k) := by
  have hmono := logarithmicPairedArrayKernel_mono n b (fun σ k => a σ k + e σ k) W hb hab
  have hcap := (logarithmicPairedArrayKernel_monotone_bounds n a (fun σ k => a σ k + e σ k)
    W ha (fun σ k => le_add_of_nonneg_right (he σ k))).2
  simp only [add_sub_cancel_left] at hcap
  linarith

/-- Padding with zero nodes leaves each sign's coset norm unchanged. -/
theorem logarithmicSignNorm_pad {n m : ℕ} (hnm : n ≤ m) (a : ℕ → ℝ) :
    logarithmicSignNorm m (fun k => if k < n + 1 then a k else 0) = logarithmicSignNorm n a := by
  have h := blockWeightNorm_collarArrayPad hnm (fun _ k => a k)
  simp only [blockWeightNorm, logarithmicSignedCosets, Finset.sum_product, Fintype.sum_bool,
    Finset.sum_add_distrib, collarArrayPad] at h
  change logarithmicSignNorm m (fun k => if k < n + 1 then a k else 0) +
      logarithmicSignNorm m (fun k => if k < n + 1 then a k else 0) =
    logarithmicSignNorm n a + logarithmicSignNorm n a at h
  linarith

theorem logarithmicPairedArrayKernel_pad {n m : ℕ} (hnm : n ≤ m) (a : Bool → ℕ → ℝ) (W : ℝ) :
    logarithmicPairedArrayKernel m (collarArrayPad n a) W = logarithmicPairedArrayKernel n a W := by
  have hmass : (∑ k ∈ Finset.range (m + 1),
      (collarArrayPad n a false k + collarArrayPad n a true k)) =
        ∑ k ∈ Finset.range (n + 1), (a false k + a true k) := by
    have h := logarithmicArrayKernel_pad hnm a W
    unfold logarithmicArrayKernel collarAllocationKernel collarDualScale at h
    rw [blockWeightNorm_collarArrayPad hnm a,
      sum_logarithmicSignedCosets m (collarArrayPad n a), sum_logarithmicSignedCosets n a] at h
    linarith
  unfold logarithmicPairedArrayKernel
  rw [hmass]
  rw [show logarithmicSignNorm m (collarArrayPad n a false) = logarithmicSignNorm n (a false)
    from logarithmicSignNorm_pad hnm (a false),
    show logarithmicSignNorm m (collarArrayPad n a true) = logarithmicSignNorm n (a true)
    from logarithmicSignNorm_pad hnm (a true)]

theorem PhysicalCollarPartition.pairedKernel_eq_array {n : ℕ} (ρ : PhysicalCollarPartition n) (y : ℝ) :
    ρ.pairedKernel y = logarithmicPairedArrayKernel n (fun σ k => ρ.weight σ k y)
      (archLevySinhWeight y) := rfl

end
end GaloisForLFunctions.BiScaleUncertainty
