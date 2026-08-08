import GaloisForLFunctions.HTGeometry.JetHypertranscendence

/-!
# Iterated constant-kernel rigidity in a free differential field

In the canonical free differential rational field, a nonconstant element stays nonconstant after
every number of differentiations.  Equivalently, if any iterated derivative lands in the constant
field, then the original element was constant.  At positive depth this sharpens to a zero law: a
positive jet can equal a base constant only when both the jet and that constant are zero.

This is the algebraic obstruction needed in branch-separation arguments.  An algebraic branch
cannot acquire a nonzero polynomial drift whose top derivative is constant without first creating
a forbidden antiderivative of a nonzero constant in the free field.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential
open JetField

noncomputable section

variable {C ι : Type*} [Field C] [CharZero C] [Fintype ι]

/-- If the derivative of an element of a free differential field is constant, then the element
itself is constant. -/
theorem mem_bot_of_deriv_mem_bot {u : JetField C ι}
    (hu : u′ ∈ (⊥ : IntermediateField C (JetField C ι))) :
    u ∈ (⊥ : IntermediateField C (JetField C ι)) := by
  by_contra hnot
  exact (deriv_notMem_bot_of_notMem_bot hnot) hu

/-- The constant field is exactly preserved by one differentiation. -/
theorem deriv_mem_bot_iff {u : JetField C ι} :
    u′ ∈ (⊥ : IntermediateField C (JetField C ι)) ↔
      u ∈ (⊥ : IntermediateField C (JetField C ι)) := by
  constructor
  · exact mem_bot_of_deriv_mem_bot
  · intro hu
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hu
    change JetField.jetDerivation (algebraMap C (JetField C ι) c) ∈
      (⊥ : IntermediateField C (JetField C ι))
    rw [Derivation.map_algebraMap]
    exact IntermediateField.zero_mem _

/-- If one iterated derivative is constant, the original element is constant. -/
theorem mem_bot_of_differentialJet_mem_bot {u : JetField C ι} (n : ℕ)
    (hu : differentialJet n u ∈ (⊥ : IntermediateField C (JetField C ι))) :
    u ∈ (⊥ : IntermediateField C (JetField C ι)) := by
  induction n with
  | zero => simpa only [differentialJet_zero] using hu
  | succ n ih =>
      exact ih ((deriv_mem_bot_iff (u := differentialJet n u)).mp
        (by simpa only [differentialJet_succ] using hu))

/-- Every iterated derivative detects the same constant subfield. -/
theorem differentialJet_mem_bot_iff {u : JetField C ι} (n : ℕ) :
    differentialJet n u ∈ (⊥ : IntermediateField C (JetField C ι)) ↔
      u ∈ (⊥ : IntermediateField C (JetField C ι)) := by
  constructor
  · exact mem_bot_of_differentialJet_mem_bot n
  · intro hu
    induction n with
    | zero => simpa only [differentialJet_zero] using hu
    | succ n ih =>
        rw [differentialJet_succ]
        exact (deriv_mem_bot_iff (u := differentialJet n u)).2 ih

omit [CharZero C] [Fintype ι] in
/-- Every positive jet of a constant element is zero. -/
theorem differentialJet_eq_zero_of_mem_bot {u : JetField C ι} {n : ℕ}
    (hn : 0 < n) (hu : u ∈ (⊥ : IntermediateField C (JetField C ι))) :
    differentialJet n u = 0 := by
  obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hu
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          rw [differentialJet_succ, differentialJet_zero]
          change JetField.jetDerivation (algebraMap C (JetField C ι) c) = 0
          exact Derivation.map_algebraMap _ c
      | succ n =>
          rw [differentialJet_succ, ih (by omega), map_zero]

/-- A positive jet vanishes exactly for elements of the constant field. -/
theorem differentialJet_eq_zero_iff {u : JetField C ι} {n : ℕ} (hn : 0 < n) :
    differentialJet n u = 0 ↔ u ∈ (⊥ : IntermediateField C (JetField C ι)) := by
  constructor
  · intro hu
    exact mem_bot_of_differentialJet_mem_bot n
      (hu ▸ IntermediateField.zero_mem _)
  · exact differentialJet_eq_zero_of_mem_bot hn

/-- Every jet of a nonconstant free differential rational expression is nonzero. -/
theorem differentialJet_ne_zero_of_notMem_bot {u : JetField C ι}
    (hu : u ∉ (⊥ : IntermediateField C (JetField C ι))) (n : ℕ) :
    differentialJet n u ≠ 0 := by
  intro hzero
  exact hu (mem_bot_of_differentialJet_mem_bot n
    (hzero ▸ IntermediateField.zero_mem _))

/-- At positive depth, a jet is a base constant exactly in the trivial zero case. -/
theorem differentialJet_eq_algebraMap_iff {u : JetField C ι} {c : C} {n : ℕ}
    (hn : 0 < n) :
    differentialJet n u = algebraMap C (JetField C ι) c ↔
      u ∈ (⊥ : IntermediateField C (JetField C ι)) ∧ c = 0 := by
  constructor
  · intro h
    have hmem : differentialJet n u ∈ (⊥ : IntermediateField C (JetField C ι)) := by
      rw [h]
      exact (⊥ : IntermediateField C (JetField C ι)).algebraMap_mem c
    have hu := mem_bot_of_differentialJet_mem_bot n hmem
    refine ⟨hu, ?_⟩
    have hzero := differentialJet_eq_zero_of_mem_bot hn hu
    rw [h, ← map_zero (algebraMap C (JetField C ι))] at hzero
    exact (algebraMap C (JetField C ι)).injective hzero
  · rintro ⟨hu, rfl⟩
    rw [map_zero]
    exact differentialJet_eq_zero_of_mem_bot hn hu

end

end GaloisForLFunctions.HTGeometry
