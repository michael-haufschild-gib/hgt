import GaloisForLFunctions.BiScaleUncertainty.CappedCollarArrayComparison

/-!
# Physical cutoff extension for capped collars

Zero-padding preserves the exact low/high support, including new empty cosets.
The physical partition extension therefore increases the capped coefficient when
both the physical endpoint and the low constraint cutoff increase.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {ι : Type*}

/-- Adding only zero-weight blocks preserves the compact maximum. -/
theorem cappedCosetSupport_zero_extension (M N : Finset ι) (hMN : M ⊆ N)
    (L H : Bool → ι → ℝ)
    (hz : ∀ p ∈ N, p ∉ M → ∀ σ, L σ p = 0 ∧ H σ p = 0) :
    cappedCosetSupport N L H = cappedCosetSupport M L H := by
  classical
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∑ σ : Bool, ∑ p ∈ N, cappedBlockSupport (L σ p) (H σ p) (pairedCap t σ)) =
        ∑ σ : Bool, ∑ p ∈ M, cappedBlockSupport (L σ p) (H σ p) (pairedCap t σ) := by
    apply Finset.sum_congr rfl
    intro σ _
    symm
    apply Finset.sum_subset hMN
    intro p hp hpm
    rw [(hz p hp hpm σ).1, (hz p hp hpm σ).2]
    exact cappedBlockSupport_zero (pairedCap_mem ht σ)
  apply le_antisymm
  · obtain ⟨t, ht, he, _⟩ := cappedCosetSupport_attained N L H
    obtain ⟨_, _, _, hmax⟩ := cappedCosetSupport_attained M L H
    rw [he, hs t ht]
    exact hmax t ht
  · obtain ⟨t, ht, he, _⟩ := cappedCosetSupport_attained M L H
    obtain ⟨_, _, _, hmax⟩ := cappedCosetSupport_attained N L H
    rw [he, ← hs t ht]
    exact hmax t ht

theorem logarithmicOddCosets_subset {n m : ℕ} (hnm : n ≤ m) :
    logarithmicOddCosets n ⊆ logarithmicOddCosets m := by
  intro p hp
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by
    have h := Finset.mem_range.mp hj
    omega), he⟩

theorem collarBlockSize_coset_pad {n m : ℕ} (hnm : n ≤ m)
    (a : Bool → ℕ → ℝ) (σ : Bool) (p : ℕ) :
    collarBlockSize (logarithmicCosetNodes m p) (collarArrayPad n a σ) =
      collarBlockSize (logarithmicCosetNodes n p) (a σ) := by
  unfold collarBlockSize
  congr 1
  calc
    _ = ∑ j ∈ logarithmicCosetNodes n p, collarArrayPad n a σ j ^ 2 := by
      symm
      apply Finset.sum_subset (logarithmicCosetNodes_subset hnm p)
      intro j hj hjn
      have hnot : ¬j < n + 1 := by
        intro h
        exact hjn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, (Finset.mem_filter.mp hj).2⟩)
      simp [collarArrayPad, hnot]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [collarArrayPad, if_pos (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)]

theorem collarBlockSize_low_pad {n k : ℕ} (hk : k ≤ n)
    (a : Bool → ℕ → ℝ) (σ : Bool) (p : ℕ) :
    collarBlockSize (logarithmicCosetNodes k p) (collarArrayPad n a σ) =
      collarBlockSize (logarithmicCosetNodes k p) (a σ) := by
  unfold collarBlockSize
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have h : j < n + 1 := by
    have hjk := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    omega
  simp only [collarArrayPad, if_pos h]

theorem collarBlockSize_high_pad {n m k : ℕ} (hnm : n ≤ m) (hk : k ≤ n)
    (a : Bool → ℕ → ℝ) (σ : Bool) (p : ℕ) :
    collarBlockSize (logarithmicHighCosetNodes m k p) (collarArrayPad n a σ) =
      collarBlockSize (logarithmicHighCosetNodes n k p) (a σ) := by
  have hnew := logarithmicCappedBlock_split (hk.trans hnm) p (collarArrayPad n a σ)
  have hold := logarithmicCappedBlock_split hk p (a σ)
  rw [collarBlockSize_low_pad hk, collarBlockSize_coset_pad hnm] at hnew
  have h₁ : 0 ≤ collarBlockSize (logarithmicHighCosetNodes m k p) (collarArrayPad n a σ) :=
    Real.sqrt_nonneg _
  have h₂ : 0 ≤ collarBlockSize (logarithmicHighCosetNodes n k p) (a σ) := Real.sqrt_nonneg _
  nlinarith

/-- Coset labels absent from the original grid contribute neither low nor high norm. -/
theorem logarithmicCappedBlock_zero_of_missing {n k p : ℕ} (hk : k ≤ n)
    (hp : p ∉ logarithmicOddCosets n) (a : ℕ → ℝ) :
    collarBlockSize (logarithmicCosetNodes k p) a = 0 ∧
      collarBlockSize (logarithmicHighCosetNodes n k p) a = 0 := by
  have hnot (j : ℕ) (hj : j ∈ logarithmicCosetNodes n p) : False :=
    hp (Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩)
  constructor
  · have hz : (∑ j ∈ logarithmicCosetNodes k p, a j ^ 2) = 0 :=
      Finset.sum_eq_zero fun j hj => (hnot j (logarithmicCosetNodes_subset hk p hj)).elim
    simp only [collarBlockSize, hz, Real.sqrt_zero]
  · have hz : (∑ j ∈ logarithmicHighCosetNodes n k p, a j ^ 2) = 0 :=
      Finset.sum_eq_zero fun j hj => (hnot j (Finset.mem_sdiff.mp hj).1).elim
    simp only [collarBlockSize, hz, Real.sqrt_zero]

/-- Padding preserves the exact support at every fixed low cutoff. -/
theorem logarithmicCappedArraySupport_pad {n m k : ℕ} (hnm : n ≤ m) (hk : k ≤ n)
    (a : Bool → ℕ → ℝ) :
    logarithmicCappedArraySupport m k (collarArrayPad n a) = logarithmicCappedArraySupport n k a := by
  have hl : (fun σ p => collarBlockSize (logarithmicCosetNodes k p) (collarArrayPad n a σ)) =
      (fun σ p => collarBlockSize (logarithmicCosetNodes k p) (a σ)) := by
    funext σ p
    exact collarBlockSize_low_pad hk a σ p
  have hh : (fun σ p => collarBlockSize (logarithmicHighCosetNodes m k p) (collarArrayPad n a σ)) =
      (fun σ p => collarBlockSize (logarithmicHighCosetNodes n k p) (a σ)) := by
    funext σ p
    exact collarBlockSize_high_pad hnm hk a σ p
  unfold logarithmicCappedArraySupport
  rw [hl, hh]
  apply cappedCosetSupport_zero_extension _ _ (logarithmicOddCosets_subset hnm)
  intro p _ hp σ
  exact logarithmicCappedBlock_zero_of_missing hk hp (a σ)

theorem sum_logarithmic_collarArrayPad {n m : ℕ} (hnm : n ≤ m) (a : Bool → ℕ → ℝ) :
    (∑ j ∈ Finset.range (m + 1),
      (collarArrayPad n a false j + collarArrayPad n a true j)) =
        ∑ j ∈ Finset.range (n + 1), (a false j + a true j) := by
  have h := logarithmicArrayKernel_pad hnm a 0
  unfold logarithmicArrayKernel collarAllocationKernel collarDualScale at h
  rw [blockWeightNorm_collarArrayPad hnm a, sum_logarithmicSignedCosets m (collarArrayPad n a),
    sum_logarithmicSignedCosets n a] at h
  linarith

theorem logarithmicCappedArrayKernel_pad {n m k : ℕ} (hnm : n ≤ m) (hk : k ≤ n)
    (a : Bool → ℕ → ℝ) (W : ℝ) :
    logarithmicCappedArrayKernel m k (collarArrayPad n a) W = logarithmicCappedArrayKernel n k a W := by
  unfold logarithmicCappedArrayKernel
  rw [logarithmicCappedArraySupport_pad hnm hk, sum_logarithmic_collarArrayPad hnm]

namespace PhysicalCollarPartition
variable {n m k l : ℕ}

/-- Physical extension and stronger low constraints both improve the same kernel. -/
theorem cappedKernel_le_extend (ρ : PhysicalCollarPartition n)
    (hnm : n ≤ m) (hk : k ≤ n) (hkl : k ≤ l) (hlm : l ≤ m) (y : ℝ) :
    ρ.cappedKernel k y ≤ (ρ.extend hnm).cappedKernel l y := by
  rw [ρ.cappedKernel_eq_array, (ρ.extend hnm).cappedKernel_eq_array,
    ← logarithmicCappedArrayKernel_pad hnm hk]
  have hpad : ∀ σ j, 0 ≤ collarArrayPad n (fun σ j => ρ.weight σ j y) σ j := by
    intro σ j
    unfold collarArrayPad
    split_ifs
    · exact ρ.weight_nonneg σ j y
    · exact le_rfl
  exact (logarithmicCappedArrayKernel_mono_weights (hk.trans hnm)
    (collarArrayPad n (fun σ j => ρ.weight σ j y))
    (fun σ j => (ρ.extend hnm).weight σ j y) (archLevySinhWeight y) hpad
    (fun σ j => ρ.pad_weight_le_extend hnm σ j y)).trans
      (logarithmicCappedArrayKernel_mono_low hkl hlm _ _)

theorem cappedCoefficient_le_extend (ρ : PhysicalCollarPartition n)
    (hnm : n ≤ m) (hk : k ≤ n) (hkl : k ≤ l) (hlm : l ≤ m) :
    ρ.cappedCoefficient k ≤ (ρ.extend hnm).cappedCoefficient l :=
  integral_mono_ae (ρ.integrableOn_cappedKernel hk) ((ρ.extend hnm).integrableOn_cappedKernel hlm)
    (Filter.Eventually.of_forall (ρ.cappedKernel_le_extend hnm hk hkl hlm))

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
