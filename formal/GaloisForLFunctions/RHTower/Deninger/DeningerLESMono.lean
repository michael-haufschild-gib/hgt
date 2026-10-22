import GaloisForLFunctions.RHTower.Deninger.DeningerCosetTransfer
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-!
# Vanishing from an injective comparison map

The long exact sequence kills the homology of the quotient in a degree where the middle term
vanishes and the comparison map one degree down is injective: the connecting map lands in something
where it is annihilated by an injection, so it is zero, and exactness leaves nothing.

This is weaker than asking the sub to be acyclic in that lower degree, and it is what a split
inclusion with acyclic complement provides.

* `deningerGroupHomology_isZero_X₃_of_mono` : the criterion.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

theorem deningerIsZero_of_exact_of_g_eq_zero {C : Type*} [Category C] [Abelian C]
    {S : ShortComplex C} (hS : S.Exact) (h₁ : IsZero S.X₁) (hg : S.g = 0) : IsZero S.X₂ := by
  have hf : S.f = 0 := h₁.eq_zero_of_src _
  haveI := hS.epi_f hg
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← cancel_epi S.f, hf, comp_zero, zero_comp]

variable {k G : Type u} [CommRing k] [Group G]

/-- **Vanishing from an injective comparison map.** -/
theorem deningerGroupHomology_isZero_X₃_of_mono {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (i j : ℕ) (hij : j + 1 = i)
    (h₂ : IsZero (groupHomology X.X₂ i))
    (hmono : Mono ((groupHomology.mapShortComplex₁ hX hij).g)) :
    IsZero (groupHomology X.X₃ i) := by
  have hδ : (groupHomology.mapShortComplex₃ hX hij).g = 0 := by
    refine hmono.right_cancellation _ 0 ?_
    rw [zero_comp]
    exact (groupHomology.mapShortComplex₁ hX hij).zero
  exact deningerIsZero_of_exact_of_g_eq_zero (groupHomology.mapShortComplex₃_exact hX hij) h₂ hδ

end RHTower
