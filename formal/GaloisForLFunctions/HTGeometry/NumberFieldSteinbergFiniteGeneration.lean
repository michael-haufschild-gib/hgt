import GaloisForLFunctions.HTGeometry.SteinbergGroupFiniteGeneration
import GaloisForLFunctions.HTGeometry.NumberFieldIntegerBasis

/-!
# Finite generation over a number ring

The ring of integers is finite as a `ℤ`-module.  Specializing the general Steinberg-generation
theorem at rank three therefore gives unconditional finite generation of both the Steinberg group
and its elementary quotient over `𝓞 K`.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

private theorem exists_distinct_from_pair_of_two_lt_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι) (i j : ι) :
    ∃ k, k ≠ i ∧ k ≠ j := by
  have hpairs : ({i, j} : Finset ι).card ≤ 2 := by
    simpa using Finset.card_insert_le i ({j} : Finset ι)
  have hne : ({i, j} : Finset ι) ≠ Finset.univ :=
    (Finset.card_lt_iff_ne_univ _).mp (lt_of_le_of_lt hpairs hcard)
  have hexists : ∃ k, k ∉ ({i, j} : Finset ι) := by
    by_contra h
    apply hne
    apply Finset.eq_univ_of_forall
    intro k
    by_contra hk
    exact h ⟨k, hk⟩
  rcases hexists with ⟨k, hk⟩
  exact ⟨k, by simpa using hk⟩

/-- The rank-three Steinberg group over a number ring is finitely generated. -/
theorem numberFieldInteger_steinbergGroup_fin3_fg
    (K : Type*) [Field K] [NumberField K] :
    Group.FG (SteinbergGroup (𝓞 K) (Fin 3)) := by
  apply steinbergGroup_fg_of_moduleFinite
  · infer_instance
  · exact exists_distinct_from_pair_of_two_lt_card (by simp)

/-- The rank-three elementary group over a number ring is finitely generated. -/
theorem numberFieldInteger_elementaryGroup_fin3_fg
    (K : Type*) [Field K] [NumberField K] :
    Group.FG (elementaryGroup (𝓞 K) (Fin 3)) := by
  apply elementaryGroup_fg
  · infer_instance
  · exact exists_distinct_from_pair_of_two_lt_card (by simp)

end GaloisForLFunctions.HTGeometry
