import GaloisForLFunctions.RHTower.UniformPrimeSubsetEnergy
import GaloisForLFunctions.RHTower.MobiusDivisorAbelQuadraticDiagonal
import Mathlib.Data.Nat.Squarefree

/-!
# Literal Möbius–divisor source under half-probability prime selection

The source is partitioned by its remaining prime-factor sets. The one-prime
recurrence is the literal signed merger, and every intermediate partition
preserves the complete source. Empty and complete selection give the original
arithmetic diagonal and complete signed square.

Uniform subset averaging has an exact symmetric-difference energy kernel. Its
retained-head mean is the half-weighted Möbius divisor Abel sum and its square
is a lower bound for average energy. No numerical result is used and no upper
energy bound, RH conclusion, or analytic no-go is asserted in this module.
-/

noncomputable section
open Finset
open scoped symmDiff
namespace RHTower

/-- All prime labels strictly below the literal source cutoff. -/
def mobiusDivisorSelectionPrimes (M : ℕ) : Finset ℕ := (range M).filter Nat.Prime

/-- Nonzero-capable source indices; nonsquarefree and terminal channels vanish. -/
def mobiusDivisorSelectionIndices (M : ℕ) : Finset ℕ := (Icc 1 (M-1)).filter Squarefree

/-- The literal signed source retained at one unprocessed prime-factor label. -/
def mobiusDivisorSelectionFibre (M : ℕ) (P R : Finset ℕ) : ℝ :=
  subsetLabelFibre (mobiusDivisorSelectionIndices M) Nat.primeFactors (mobiusDivisorDilationChannel M) P R

/-- Complete retained energy after processing a given prime subset. -/
def mobiusDivisorSelectionEnergy (M : ℕ) (P : Finset ℕ) : ℝ :=
  subsetLabelEnergy (mobiusDivisorSelectionPrimes M) (mobiusDivisorSelectionIndices M)
    Nat.primeFactors (mobiusDivisorDilationChannel M) P

/-- Uniform average over all processed prime subsets: independent probability one half. -/
def mobiusDivisorHalfSelectionEnergy (M : ℕ) : ℝ :=
  uniformSubsetMean (mobiusDivisorSelectionPrimes M) (mobiusDivisorSelectionEnergy M)

/-- The arithmetic mean head exposed by half-probability prime selection. -/
def mobiusDivisorHalfSelectionHead (M : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d / (2:ℝ)^d.primeFactors.card

private theorem selection_labels (M : ℕ) : ∀ d ∈ mobiusDivisorSelectionIndices M,
    d.primeFactors ⊆ mobiusDivisorSelectionPrimes M := by
  intro d hd p hp
  obtain ⟨hd,hds⟩ := mem_filter.mp hd
  obtain ⟨hd1,hdM⟩ := mem_Icc.mp hd
  have hpd := Nat.le_of_mem_primeFactors hp
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), (Nat.mem_primeFactors.mp hp).1⟩

private theorem selection_source_self (M : ℕ) : mobiusDivisorDilationChannel M M = 0 := by
  by_cases hM : M=0
  · subst M
    simp [mobiusDivisorDilationChannel]
  · simp [mobiusDivisorDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<M)]

private theorem selection_source_nonsquarefree (M d : ℕ) (hd : ¬Squarefree d) :
    mobiusDivisorDilationChannel M d = 0 := by
  simp [mobiusDivisorDilationChannel,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

private theorem selection_sum (M : ℕ) (F : ℕ → ℝ → ℝ) (hF : ∀ d, F d 0=0) :
    (∑ d ∈ mobiusDivisorSelectionIndices M, F d (mobiusDivisorDilationChannel M d)) =
      ∑ d ∈ Icc 1 M, F d (mobiusDivisorDilationChannel M d) := by
  calc
    _ = ∑ d ∈ Icc 1 (M-1), F d (mobiusDivisorDilationChannel M d) := by
      rw [mobiusDivisorSelectionIndices,sum_filter]
      apply sum_congr rfl
      intro d hd
      by_cases hs : Squarefree d
      · simp [hs]
      · simp [hs,selection_source_nonsquarefree M d hs,hF]
    _ = _ := by
      apply sum_subset
      · intro d hd
        obtain ⟨hl,hu⟩ := mem_Icc.mp hd
        exact mem_Icc.mpr ⟨hl,by omega⟩
      · intro d hd hn
        have heq : d=M := by
          simp only [mem_Icc] at hd hn
          omega
        subst d
        rw [selection_source_self,hF]

/-- No prime selection gives exactly the original arithmetic diagonal. -/
theorem mobiusDivisorSelectionEnergy_empty (M : ℕ) :
    mobiusDivisorSelectionEnergy M ∅ = ∑ d ∈ Icc 1 M, (mobiusDivisorDilationChannel M d)^(2 : ℕ) := by
  rw [mobiusDivisorSelectionEnergy,subsetLabelEnergy_empty _ _ _ _ (selection_labels M)]
  · exact selection_sum M (fun _ x => x^(2 : ℕ)) (by simp)
  · intro d hd e he h
    have hdS := (mem_filter.mp hd).2
    have heS := (mem_filter.mp he).2
    rw [← Nat.prod_primeFactors_of_squarefree hdS,← Nat.prod_primeFactors_of_squarefree heS,h]

/-- Complete prime selection gives exactly the complete signed square. -/
theorem mobiusDivisorSelectionEnergy_full (M : ℕ) :
    mobiusDivisorSelectionEnergy M (mobiusDivisorSelectionPrimes M) =
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)^(2 : ℕ) := by
  rw [mobiusDivisorSelectionEnergy,subsetLabelEnergy_full _ _ _ _ (selection_labels M),
    selection_sum M (fun _ x => x) (by simp)]

/-- The half-weighted arithmetic head is exactly the mean retained cofactor-one source. -/
theorem mobiusDivisorHalfSelectionHead_eq_mean (M : ℕ) :
    mobiusDivisorHalfSelectionHead M =
      uniformSubsetMean (mobiusDivisorSelectionPrimes M) (fun P => mobiusDivisorSelectionFibre M P ∅) := by
  rw [show (fun P => mobiusDivisorSelectionFibre M P ∅) =
      (fun P => subsetLabelFibre (mobiusDivisorSelectionIndices M) Nat.primeFactors
        (mobiusDivisorDilationChannel M) P ∅) from rfl,
    uniformSubsetMean_labelHead _ _ _ _ (selection_labels M),
    selection_sum M (fun d x => x/(2:ℝ)^d.primeFactors.card) (by simp)]
  rfl

/-- The mean head squared is an unconditional lower bound for averaged retained energy. -/
theorem mobiusDivisorHalfSelectionHead_sq_le_energy (M : ℕ) :
    (mobiusDivisorHalfSelectionHead M)^(2 : ℕ) ≤ mobiusDivisorHalfSelectionEnergy M := by
  have h := uniformSubsetMean_labelHead_sq_le_energy (mobiusDivisorSelectionPrimes M)
    (mobiusDivisorSelectionIndices M) Nat.primeFactors (mobiusDivisorDilationChannel M)
    (selection_labels M)
  rw [selection_sum M (fun d x => x/(2:ℝ)^d.primeFactors.card) (by simp)] at h
  exact h

/-- Exact arithmetic averaged-energy kernel, with all squarefree source labels retained. -/
theorem mobiusDivisorHalfSelectionEnergy_eq_kernel (M : ℕ) :
    mobiusDivisorHalfSelectionEnergy M =
      ∑ d ∈ mobiusDivisorSelectionIndices M, ∑ e ∈ mobiusDivisorSelectionIndices M,
        mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e /
          (2:ℝ)^(d.primeFactors ∆ e.primeFactors).card := by
  exact uniformSubsetMean_labelEnergy _ _ _ _ (selection_labels M)



/-- One more prime acts by the literal signed two-fibre merger. -/
theorem mobiusDivisorSelectionFibre_insert (M : ℕ) (P R : Finset ℕ) (p : ℕ) :
    mobiusDivisorSelectionFibre M (insert p P) R =
      if p ∈ R then 0 else mobiusDivisorSelectionFibre M P R +
        mobiusDivisorSelectionFibre M P (insert p R) := by
  exact subsetLabelFibre_insert _ _ _ _ _ _

/-- Every processed subset preserves the complete arithmetic signed source. -/
theorem mobiusDivisorSelectionFibre_sum (M : ℕ) (P : Finset ℕ) :
    (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset, mobiusDivisorSelectionFibre M P R) =
      ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d := by
  rw [show (fun R => mobiusDivisorSelectionFibre M P R) =
      (fun R => subsetLabelFibre (mobiusDivisorSelectionIndices M) Nat.primeFactors
        (mobiusDivisorDilationChannel M) P R) from rfl,
    subsetLabelFibre_sum _ _ _ _ (selection_labels M),
    selection_sum M (fun _ x => x) (by simp)]



/-- The multiplicative source coefficient exposed by half-probability prime selection. -/
def halfSelectionMoebiusWeight (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (2:ℝ)^d.primeFactors.card

/-- Exact arithmetic landing of the averaged head, retaining the divisor defect and half-order clock. -/
theorem mobiusDivisorHalfSelectionHead_eq_divisor_abel (M : ℕ) :
    mobiusDivisorHalfSelectionHead M =
      ∑ k ∈ Icc 1 (M-1), (Real.sqrt (k+1:ℕ)-Real.sqrt k) *
        ∑ d ∈ Icc 1 k, halfSelectionMoebiusWeight d * primeFreeDivisorDefect (k/d) := by
  have hdrop : (∑ d ∈ Icc 1 (M-1),
      mobiusDivisorDilationChannel M d / (2:ℝ)^d.primeFactors.card) =
      mobiusDivisorHalfSelectionHead M := by
    apply sum_subset
    · intro d hd
      obtain ⟨hl,hu⟩ := mem_Icc.mp hd
      exact mem_Icc.mpr ⟨hl,by omega⟩
    · intro d hd hn
      have heq : d=M := by simp only [mem_Icc] at hd hn; omega
      subst d
      rw [selection_source_self,zero_div]
  have hpoint (d : ℕ) : mobiusDivisorDilationChannel M d / (2:ℝ)^d.primeFactors.card =
      ∑ k ∈ Icc d (M-1), (Real.sqrt (k+1:ℕ)-Real.sqrt k) *
        (halfSelectionMoebiusWeight d*primeFreeDivisorDefect (k/d)) := by
    rw [mobiusDivisorDilationChannel,mul_sum,sum_div]
    apply sum_congr rfl
    intro k hk
    unfold halfSelectionMoebiusWeight
    ring
  rw [← hdrop]
  simp_rw [hpoint,mul_sum]
  apply sum_comm'
  intro d k
  simp only [mem_Icc]
  omega

end RHTower
