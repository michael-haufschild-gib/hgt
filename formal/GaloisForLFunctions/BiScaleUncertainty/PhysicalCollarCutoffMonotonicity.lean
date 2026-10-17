import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarSourceEnergy

/-!
# Cutoff comparison for physical collar optimization

Zero-padding preserves the signed odd-coset support function. Extending a physical
partition by assigning only the newly available physical interval preserves every
old share. The optimized coefficient is therefore monotone in the literal grid cutoff.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

/-- Zero-extension of a signed node array beyond the finite cutoff. -/
def collarArrayPad (n : ℕ) (a : Bool → ℕ → ℝ) (σ : Bool) (k : ℕ) : ℝ :=
  if k < n + 1 then a σ k else 0

/-- The shared-origin support coefficient for a general signed logarithmic array. -/
def logarithmicArrayKernel (n : ℕ) (a : Bool → ℕ → ℝ) (W : ℝ) : ℝ :=
  collarAllocationKernel (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => a j.2 k) W

theorem logarithmicCosetNodes_subset {n m : ℕ} (hnm : n ≤ m) (q : ℕ) :
    logarithmicCosetNodes n q ⊆ logarithmicCosetNodes m q := by
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hr, hq⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
    have h := Finset.mem_range.mp hr
    omega), hq⟩

theorem logarithmicSignedCosets_subset {n m : ℕ} (hnm : n ≤ m) :
    logarithmicSignedCosets n ⊆ logarithmicSignedCosets m := by
  intro j hj
  rcases Finset.mem_product.mp hj with ⟨hq, hs⟩
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hq
  exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by
    have h := Finset.mem_range.mp hk
    omega), heq⟩, hs⟩

private theorem sum_range_pad {n m : ℕ} (hnm : n ≤ m) (a : ℕ → ℝ) :
    (∑ k ∈ Finset.range (m + 1), if k < n + 1 then a k else 0) =
      ∑ k ∈ Finset.range (n + 1), a k := by
  have hs : Finset.range (n + 1) ⊆ Finset.range (m + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  calc
    _ = ∑ k ∈ Finset.range (n + 1), if k < n + 1 then a k else 0 := by
      symm
      apply Finset.sum_subset hs
      intro k _ hk
      simp only [Finset.mem_range] at hk
      simp [hk]
    _ = _ := Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))

private theorem sum_coset_pad {n m : ℕ} (hnm : n ≤ m) (q : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ logarithmicCosetNodes m q, if k < n + 1 then a k else 0) =
      ∑ k ∈ logarithmicCosetNodes n q, a k := by
  calc
    _ = ∑ k ∈ logarithmicCosetNodes n q, if k < n + 1 then a k else 0 := by
      symm
      apply Finset.sum_subset (logarithmicCosetNodes_subset hnm q)
      intro k hk hkn
      have hn : ¬k < n + 1 := by
        intro h
        exact hkn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, (Finset.mem_filter.mp hk).2⟩)
      simp [hn]
    _ = _ := Finset.sum_congr rfl (fun k hk => if_pos
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))

private theorem sum_coset_eq_zero_of_missing {n : ℕ} {j : ℕ × Bool}
    (hj : j ∉ logarithmicSignedCosets n) (a : ℕ → ℝ) :
    (∑ k ∈ logarithmicCosetNodes n j.1, a k) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  exact (hj (Finset.mem_product.mpr ⟨Finset.mem_image.mpr
    ⟨k, (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩, Finset.mem_univ _⟩)).elim

/-- New odd-coset labels with zero coefficients have zero block norm. -/
theorem blockWeightNorm_collarArrayPad {n m : ℕ} (hnm : n ≤ m) (a : Bool → ℕ → ℝ) :
    blockWeightNorm (logarithmicSignedCosets m) (fun j => logarithmicCosetNodes m j.1)
      (fun j k => collarArrayPad n a j.2 k) =
    blockWeightNorm (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
      (fun j k => a j.2 k) := by
  have hs (j : ℕ × Bool) :
      (∑ k ∈ logarithmicCosetNodes m j.1, collarArrayPad n a j.2 k ^ 2) =
        ∑ k ∈ logarithmicCosetNodes n j.1, a j.2 k ^ 2 := by
    calc
      _ = ∑ k ∈ logarithmicCosetNodes m j.1, if k < n + 1 then a j.2 k ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k < n + 1 <;> simp [collarArrayPad, hk]
      _ = _ := sum_coset_pad hnm j.1 (fun k => a j.2 k ^ 2)
  unfold blockWeightNorm
  simp_rw [hs]
  symm
  apply Finset.sum_subset (logarithmicSignedCosets_subset hnm)
  intro j _ hj
  rw [sum_coset_eq_zero_of_missing hj, Real.sqrt_zero]

/-- Both mass and shared-origin support are unchanged by padding to a larger cutoff. -/
theorem logarithmicArrayKernel_pad {n m : ℕ} (hnm : n ≤ m) (a : Bool → ℕ → ℝ) (W : ℝ) :
    logarithmicArrayKernel m (collarArrayPad n a) W = logarithmicArrayKernel n a W := by
  unfold logarithmicArrayKernel collarAllocationKernel collarDualScale
  rw [blockWeightNorm_collarArrayPad hnm a,
    sum_logarithmicSignedCosets m (collarArrayPad n a), sum_logarithmicSignedCosets n a]
  congr 2
  calc
    _ = ∑ k ∈ Finset.range (m + 1), if k < n + 1 then a false k + a true k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k < n + 1 <;> simp [collarArrayPad, hk]
    _ = _ := sum_range_pad hnm (fun k => a false k + a true k)

theorem logarithmicCollarEndpoint_monotone : Monotone logarithmicCollarEndpoint := by
  intro n m hnm
  exact Real.log_le_log (by positivity) (by exact_mod_cast (show n + 2 ≤ m + 2 by omega))

/-- Adding nonnegative array capacity cannot reduce its shared-origin coefficient. -/
theorem logarithmicArrayKernel_mono (n : ℕ) (a b : Bool → ℕ → ℝ) {W : ℝ} (hW : 0 < W)
    (ha : ∀ σ k, 0 ≤ a σ k) (hab : ∀ σ k, a σ k ≤ b σ k) :
    logarithmicArrayKernel n a W ≤ logarithmicArrayKernel n b W := by
  have h := (collarAllocationKernel_monotone_bounds (logarithmicSignedCosets n)
    (logarithmicSignedCosets_nonempty n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => a j.2 k) (fun j k => b j.2 k) hW (fun j _ k _ => ha j.2 k)
    (fun j _ k _ => hab j.2 k)).1
  have hn : 0 ≤ (1 - collarDualRadius (logarithmicSignedCosets n)
      (fun j => logarithmicCosetNodes n j.1) (fun j k => b j.2 k) W) *
      (∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1,
        (b j.2 k - a j.2 k)) :=
    mul_nonneg (sub_nonneg.mpr (collarDualRadius_lt_one _ _ _ hW).le)
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sub_nonneg.mpr (hab j.2 k))
  exact sub_nonneg.mp (hn.trans h)

/-- One-sided coefficient error is bounded by the added physical density.
The two arrays need not be coordinatewise ordered. -/
theorem logarithmicArrayKernel_error_bound (n : ℕ) (a b e : Bool → ℕ → ℝ) {W : ℝ}
    (hW : 0 < W) (ha : ∀ σ k, 0 ≤ a σ k) (he : ∀ σ k, 0 ≤ e σ k)
    (hab : ∀ σ k, b σ k ≤ a σ k + e σ k) :
    logarithmicArrayKernel n b W - logarithmicArrayKernel n a W ≤
      ∑ k ∈ Finset.range (n + 1), (e false k + e true k) := by
  have h := collarAllocationKernel_support_upper (logarithmicSignedCosets n)
    (logarithmicSignedCosets_nonempty n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => a j.2 k) (fun j k => b j.2 k) hW
  change logarithmicArrayKernel n b W - logarithmicArrayKernel n a W ≤ _ at h
  rw [← sum_logarithmicSignedCosets n e]
  refine h.trans (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k hk => ?_)
  have h0 := collarDualSlope_nonneg (logarithmicSignedCosets n)
    (fun j => logarithmicCosetNodes n j.1) (fun j k => a j.2 k) W j k (ha j.2 k)
  have h1 := (collarDualSlope_le_radius (logarithmicSignedCosets n)
    (fun j => logarithmicCosetNodes n j.1) (fun j k => a j.2 k) W j k hk).trans
      (collarDualRadius_lt_one _ _ _ hW).le
  calc
    _ ≤ e j.2 k * (1 - collarDualSlope (logarithmicSignedCosets n)
        (fun j => logarithmicCosetNodes n j.1) (fun j k => a j.2 k) W j k) :=
      mul_le_mul_of_nonneg_right (by linarith [hab j.2 k]) (sub_nonneg.mpr h1)
    _ ≤ e j.2 k := mul_le_of_le_one_right (he j.2 k) (sub_le_self 1 h0)

namespace PhysicalCollarPartition
variable {n m : ℕ}

/-- Retain all old shares on their physical interval, filling only the newly available part. -/
def extend (ρ : PhysicalCollarPartition n) (hm : n ≤ m) : PhysicalCollarPartition m where
  share k x := if x < logarithmicCollarEndpoint n then
      if k < n + 1 then ρ.share k x else 0
    else (equalMultiplicity m).share k x
  measurable_share := by
    intro k
    apply Measurable.ite measurableSet_Iio
    · by_cases hk : k < n + 1
      · simpa only [if_pos hk] using ρ.measurable_share k
      · simpa only [if_neg hk] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ)))
    · exact (equalMultiplicity m).measurable_share k
  nonneg := by
    intro k x
    split_ifs <;> first | exact ρ.nonneg k x | exact le_rfl |
      exact (equalMultiplicity m).nonneg k x
  supported := by
    intro k x hx
    by_cases hxn : x < logarithmicCollarEndpoint n
    · simp only [if_pos hxn]
      split_ifs with hk
      · apply ρ.supported k x
        intro hc
        exact hx ⟨hc.1, hc.2.1, hc.2.2.trans_le (logarithmicCollarEndpoint_monotone hm)⟩
      · rfl
    · simp only [if_neg hxn]
      exact (equalMultiplicity m).supported k x hx
  partition := by
    intro x
    by_cases hxn : x < logarithmicCollarEndpoint n
    · simp only [if_pos hxn]
      rw [sum_range_pad hm, ρ.partition]
      have he : x < logarithmicCollarEndpoint m := hxn.trans_le (logarithmicCollarEndpoint_monotone hm)
      simp only [indicator_apply, mem_Ioo, hxn, he, and_true]
    · simp only [if_neg hxn]
      exact (equalMultiplicity m).partition x

/-- Every old weighted collar is preserved or enlarged, with no duplicated physical mass. -/
theorem pad_weight_le_extend (ρ : PhysicalCollarPartition n) (hm : n ≤ m)
    (σ : Bool) (k : ℕ) (y : ℝ) :
    collarArrayPad n (fun σ k => ρ.weight σ k y) σ k ≤ (ρ.extend hm).weight σ k y := by
  by_cases hk : k < n + 1
  · rw [collarArrayPad, if_pos hk]
    by_cases hx : logarithmicCollarNode k + collarSignedOffset σ y < logarithmicCollarEndpoint n
    · simp only [weight, density, extend, if_pos hx, if_pos hk, le_refl]
    · have hz := ρ.supported k (logarithmicCollarNode k + collarSignedOffset σ y)
        (fun hc => hx hc.2.2)
      have hw : ρ.weight σ k y = 0 := by simp only [weight, density, hz, zero_mul]
      rw [hw]
      exact (ρ.extend hm).weight_nonneg σ k y
  · rw [collarArrayPad, if_neg hk]
    exact (ρ.extend hm).weight_nonneg σ k y

theorem kernel_le_extend (ρ : PhysicalCollarPartition n) (hm : n ≤ m)
    {y : ℝ} (hy : 0 < y) : ρ.kernel y ≤ (ρ.extend hm).kernel y := by
  rw [ρ.kernel_eq_allocationKernel, (ρ.extend hm).kernel_eq_allocationKernel]
  change logarithmicArrayKernel n (fun σ k => ρ.weight σ k y) (archLevySinhWeight y) ≤
    logarithmicArrayKernel m (fun σ k => (ρ.extend hm).weight σ k y) (archLevySinhWeight y)
  rw [← logarithmicArrayKernel_pad hm]
  apply logarithmicArrayKernel_mono m _ _ (archLevySinhWeight_pos hy)
  · intro σ k
    by_cases hk : k < n + 1
    · simpa only [collarArrayPad, if_pos hk] using ρ.weight_nonneg σ k y
    · simp only [collarArrayPad, if_neg hk, le_refl]
  · exact fun σ k => ρ.pad_weight_le_extend hm σ k y

/-- Extending the physical interval does not decrease the coefficient of any incumbent. -/
theorem coefficient_le_extend (ρ : PhysicalCollarPartition n) (hm : n ≤ m) :
    ρ.coefficient ≤ (ρ.extend hm).coefficient := by
  apply integral_mono_ae ρ.integrableOn_kernel (ρ.extend hm).integrableOn_kernel
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact ρ.kernel_le_extend hm hy.1

/-- The actual continuous allocation optimum is monotone in the grid cutoff. -/
theorem optimalCoefficient_monotone : Monotone optimalCoefficient := by
  intro n m hnm
  apply csSup_le
  · exact ⟨(equalMultiplicity n).coefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (ρ.coefficient_le_extend hnm).trans
      (le_csSup (coefficient_range_bddAbove m) ⟨ρ.extend hnm, rfl⟩)

end PhysicalCollarPartition

/-- The running maximum is exactly the current-cutoff optimum. -/
theorem monotoneCollarCoefficient_eq_optimalCoefficient (n : ℕ) :
    monotoneCollarCoefficient n = PhysicalCollarPartition.optimalCoefficient n := by
  apply le_antisymm ?_ (optimalCoefficient_le_monotoneCollarCoefficient n)
  apply Finset.sup'_le
  intro k hk
  apply PhysicalCollarPartition.optimalCoefficient_monotone
  have h := Finset.mem_range.mp hk
  omega

theorem optimalCoefficient_tendsto :
    Filter.Tendsto PhysicalCollarPartition.optimalCoefficient Filter.atTop
      (nhds limitingCollarCoefficient) := by
  have he : monotoneCollarCoefficient = PhysicalCollarPartition.optimalCoefficient :=
    funext monotoneCollarCoefficient_eq_optimalCoefficient
  simpa only [he] using monotoneCollarCoefficient_tendsto

theorem optimalCoefficient_le_normalized_energy (n : ℕ) (f : SmoothLogarithmicGridSource n) :
    PhysicalCollarPartition.optimalCoefficient n ≤ biScaleLevyEnergy f.1.1 /
      RHTower.ArchimedeanAnomaly.autocorr f.1.1 0 := by
  rw [← monotoneCollarCoefficient_eq_optimalCoefficient]
  exact monotoneCollarCoefficient_le_normalized_energy n f

end
end GaloisForLFunctions.BiScaleUncertainty
