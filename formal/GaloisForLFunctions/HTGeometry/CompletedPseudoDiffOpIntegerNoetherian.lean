import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpIntegerPrincipal
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The completed pseudodifferential valuation ring is left Noetherian

The additive valuation of every nonzero element of the valuation ring is a nonnegative integer.
Thus every nonzero left ideal has an element of least valuation, and that element left-divides all
other members.  Every left ideal is principal; finite coordinate powers are therefore Noetherian.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- Natural additive valuation on the completed valuation ring, with the zero value filled by
zero (only the nonzero formula is used). -/
noncomputable def completedPseudoDiffOpIntegerNatValue
    (a : CompletedPseudoDiffOpInteger (K := K)) : ℕ := by
  classical
  exact if ha : (a : CompletedPseudoDiffOp K) = 0 then 0 else
    Int.toNat (completedPseudoDiffOpUnitAddValue
      (Units.mk0 (a : CompletedPseudoDiffOp K) ha))

theorem completedPseudoDiffOpAddValue_eq_natValue
    (a : CompletedPseudoDiffOpInteger (K := K))
    (ha : (a : CompletedPseudoDiffOp K) ≠ 0) :
    completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K) =
      (completedPseudoDiffOpIntegerNatValue a : WithTop ℤ) := by
  let z := completedPseudoDiffOpUnitAddValue
    (Units.mk0 (a : CompletedPseudoDiffOp K) ha)
  have hva : completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K) = (z : WithTop ℤ) := by
    simpa [z] using completedPseudoDiffOpAddValue_unit_eq_coe
      (Units.mk0 (a : CompletedPseudoDiffOp K) ha)
  have hnonneg : (0 : WithTop ℤ) ≤
      completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K) :=
    (mem_completedPseudoDiffOpInteger_iff_addValue_nonneg _).mp a.2
  have hz : 0 ≤ z := by
    rw [hva] at hnonneg
    exact_mod_cast hnonneg
  rw [hva]
  norm_cast
  simp [completedPseudoDiffOpIntegerNatValue, ha, z, Int.toNat_of_nonneg hz]

/-- Every left ideal of the completed pseudodifferential valuation ring is principal. -/
theorem exists_generator_completedPseudoDiffOpInteger
    (I : Submodule (CompletedPseudoDiffOpInteger (K := K))
      (CompletedPseudoDiffOpInteger (K := K))) :
    ∃ b : CompletedPseudoDiffOpInteger (K := K),
      I = Submodule.span (CompletedPseudoDiffOpInteger (K := K)) {b} := by
  classical
  by_cases hI : ∃ x ∈ I, (x : CompletedPseudoDiffOp K) ≠ 0
  · obtain ⟨x₀, hx₀I, hx₀⟩ := hI
    have hex : ∃ n : ℕ, ∃ x ∈ I, (x : CompletedPseudoDiffOp K) ≠ 0 ∧
        completedPseudoDiffOpIntegerNatValue x = n :=
      ⟨completedPseudoDiffOpIntegerNatValue x₀, x₀, hx₀I, hx₀, rfl⟩
    obtain ⟨b, hbI, hb0, hbval⟩ := Nat.find_spec hex
    refine ⟨b, le_antisymm (fun a haI => ?_) ?_⟩
    · by_cases ha0 : (a : CompletedPseudoDiffOp K) = 0
      · rw [Submodule.mem_span_singleton]
        refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa using ha0.symm
      · have hmin : Nat.find hex ≤ completedPseudoDiffOpIntegerNatValue a :=
          Nat.find_min' hex ⟨a, haI, ha0, rfl⟩
        have hval : completedPseudoDiffOpAddValue (b : CompletedPseudoDiffOp K) ≤
            completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K) := by
          rw [completedPseudoDiffOpAddValue_eq_natValue b hb0,
            completedPseudoDiffOpAddValue_eq_natValue a ha0, hbval]
          exact_mod_cast hmin
        obtain ⟨c, hc⟩ := exists_completedPseudoDiffOpInteger_left_factor hb0 hval
        rw [Submodule.mem_span_singleton]
        refine ⟨c, ?_⟩
        apply Subtype.ext
        exact hc
    · rw [Submodule.span_le]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rwa [ha]
  · refine ⟨0, le_antisymm (fun x hx => ?_) ?_⟩
    · have hx0 : (x : CompletedPseudoDiffOp K) = 0 := by
        by_contra hne
        exact hI ⟨x, hx, hne⟩
      have hx0' : x = 0 := Subtype.ext hx0
      subst x
      exact Submodule.zero_mem _
    · rw [Submodule.span_zero_singleton]
      exact bot_le

noncomputable instance completedPseudoDiffOpInteger_isNoetherian_self :
    IsNoetherian (CompletedPseudoDiffOpInteger (K := K))
      (CompletedPseudoDiffOpInteger (K := K)) := by
  refine isNoetherian_def.mpr fun I => ?_
  obtain ⟨b, rfl⟩ := exists_generator_completedPseudoDiffOpInteger I
  exact ⟨{b}, by simp⟩

noncomputable instance completedPseudoDiffOpInteger_isNoetherian_pi
    {ι : Type*} [Finite ι] :
    IsNoetherian (CompletedPseudoDiffOpInteger (K := K))
      (ι → CompletedPseudoDiffOpInteger (K := K)) :=
  isNoetherian_pi

end

end GaloisForLFunctions.HTGeometry.DiffOp
