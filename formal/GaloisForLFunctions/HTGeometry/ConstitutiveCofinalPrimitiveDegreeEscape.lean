import GaloisForLFunctions.HTGeometry.ConstitutivePrimitiveExecutionGenesis
import Mathlib

/-!
# Cofinal primitive-degree escape

Complete-complement failure systems have canonical central primitive laws whose degrees grow with
aperture.  Consequently every bounded primitive grammar fails at an explicit later aperture.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Every complement of one coordinate is a declared failure kernel. -/
def completeComplementFailureFamily (k : ℕ) : Finset (Finset (Fin k)) :=
  Finset.univ.image fun i => Finset.univ.erase i

/-- One unit of resource on every coordinate. -/
def completeComplementWeight (k : ℕ) (_ : Fin k) : ℕ := 1

/-- Every coordinate complement belongs to the complete-complement failure family. -/
theorem complement_mem_completeComplementFailureFamily (k : ℕ) (i : Fin k) :
    Finset.univ.erase i ∈ completeComplementFailureFamily k := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- The all-ones weight is locally admitted at grade `k - 1`. -/
theorem completeComplementWeight_local (k : ℕ) :
    WeightedLocalRepair (completeComplementFailureFamily k) (k - 1)
      (completeComplementWeight k) := by
  intro K hK
  rw [completeComplementFailureFamily] at hK
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hK
  simp [completeComplementWeight, Finset.card_erase_of_mem]

/-- A positive local law on a complete-complement system spends strictly more total resource than
its grade. -/
theorem completeComplement_positive_local_total_strict {k m : ℕ} (hk : 2 ≤ k)
    (a : Fin k → ℕ) (hm : 0 < m)
    (hlocal : WeightedLocalRepair (completeComplementFailureFamily k) m a) :
    m < ∑ i : Fin k, a i := by
  let i0 : Fin k := ⟨0, by omega⟩
  have hpart := hlocal (Finset.univ.erase i0)
    (complement_mem_completeComplementFailureFamily k i0)
  have htotalpos : 0 < ∑ i : Fin k, a i := by
    calc
      0 < m := hm
      _ ≤ ∑ i ∈ Finset.univ.erase i0, a i := hpart
      _ ≤ ∑ i : Fin k, a i :=
        Finset.sum_le_sum_of_subset (Finset.erase_subset i0 Finset.univ)
  have hex : ∃ i : Fin k, 0 < a i := by
    by_contra h
    have hz : ∀ i : Fin k, a i = 0 := by
      intro i
      by_contra hi
      exact h ⟨i, Nat.pos_of_ne_zero hi⟩
    simp [hz] at htotalpos
  obtain ⟨i, hi⟩ := hex
  have hiLocal := hlocal (Finset.univ.erase i)
    (complement_mem_completeComplementFailureFamily k i)
  have hsum := Finset.sum_erase_add (s := Finset.univ) (f := a) (Finset.mem_univ i)
  omega

/-- The all-ones law at grade `k - 1` is primitive for every aperture `k ≥ 2`. -/
theorem completeComplementCentralPrimitive (k : ℕ) (hk : 2 ≤ k) :
    WeightedPrimitiveRepair (completeComplementFailureFamily k) (k - 1)
      (completeComplementWeight k) := by
  refine ⟨by omega, completeComplementWeight_local k, ?_⟩
  rintro ⟨m₁, m₂, a₁, a₂, hm₁, hm₂, hgrade, hlocal₁, hlocal₂, hdom⟩
  have hlower₁ := completeComplement_positive_local_total_strict hk a₁ hm₁ hlocal₁
  have hlower₂ := completeComplement_positive_local_total_strict hk a₂ hm₂ hlocal₂
  have hupper : (∑ i : Fin k, a₁ i) + ∑ i : Fin k, a₂ i ≤ k := by
    calc
      (∑ i : Fin k, a₁ i) + ∑ i : Fin k, a₂ i =
          ∑ i : Fin k, (a₁ i + a₂ i) := by rw [Finset.sum_add_distrib]
      _ ≤ ∑ i : Fin k, completeComplementWeight k i :=
        Finset.sum_le_sum fun i _hi => hdom i
      _ = k := by simp [completeComplementWeight]
  omega

/-- A degree-`D` grammar misses the explicit degree-`D+1` primitive at aperture `D+2`. -/
theorem completeComplement_not_boundedGenerated (D : ℕ) :
    ¬ BoundedPrimitiveGeneratedRepair
      (completeComplementFailureFamily (D + 2)) D (D + 1)
      (completeComplementWeight (D + 2)) := by
  intro hgen
  have hp := completeComplementCentralPrimitive (D + 2) (by omega)
  have hle := primitive_boundedGenerated_degree_le
    (completeComplementFailureFamily (D + 2)) D (D + 1)
    (completeComplementWeight (D + 2)) hp hgen
  omega

/-- Primitive degrees in the cofinal complete-complement family escape every bound. -/
theorem completeComplementPrimitiveDegrees_unbounded :
    ∀ D : ℕ, ∃ k : ℕ, 2 ≤ k ∧ D < k - 1 ∧
      WeightedPrimitiveRepair (completeComplementFailureFamily k) (k - 1)
        (completeComplementWeight k) := by
  intro D
  exact ⟨D + 2, by omega, by omega, completeComplementCentralPrimitive (D + 2) (by omega)⟩

/-- Closed capstone: explicit primitive growth and failure of every bounded grammar. -/
theorem cofinalPrimitiveDegreeEscapeMechanism_closed :
    (∀ k : ℕ, 2 ≤ k →
      WeightedPrimitiveRepair (completeComplementFailureFamily k) (k - 1)
        (completeComplementWeight k)) ∧
    (∀ D : ℕ,
      ¬ BoundedPrimitiveGeneratedRepair
        (completeComplementFailureFamily (D + 2)) D (D + 1)
        (completeComplementWeight (D + 2))) ∧
    (∀ D : ℕ, ∃ k : ℕ, 2 ≤ k ∧ D < k - 1 ∧
      WeightedPrimitiveRepair (completeComplementFailureFamily k) (k - 1)
        (completeComplementWeight k)) := by
  exact ⟨completeComplementCentralPrimitive,
    completeComplement_not_boundedGenerated,
    completeComplementPrimitiveDegrees_unbounded⟩

end GaloisForLFunctions.HTGeometry
