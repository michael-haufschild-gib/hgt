import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The spectrum of a one-dimensional local domain

For a local domain `𝒪` which is not a field and in which every nonzero prime is maximal — for
instance a rank one valuation ring — the prime spectrum has exactly two points, the generic point
`(0)` and the closed point `𝔪`, and its only open sets are `∅`, `{η}` and the whole space.  The
open point is a basic open `D (f)` for any nonzero `f` of the maximal ideal.
-/

namespace HTGeometry

open PrimeSpectrum IsLocalRing

universe u

variable (O : Type u) [CommRing O] [IsDomain O] [IsLocalRing O]

/-- The generic point of the spectrum of a domain. -/
def specGeneric : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩

/-- The closed point of the spectrum of a local ring. -/
def specClosed : PrimeSpectrum O := ⟨maximalIdeal O, (maximalIdeal.isMaximal O).isPrime⟩

variable {O}

@[simp] theorem specGeneric_asIdeal : (specGeneric O).asIdeal = ⊥ := rfl

omit [IsDomain O] in
@[simp] theorem specClosed_asIdeal : (specClosed O).asIdeal = maximalIdeal O := rfl

theorem specGeneric_ne_specClosed (hfield : ¬ IsField O) :
    specGeneric O ≠ specClosed O := by
  intro h
  have := congrArg PrimeSpectrum.asIdeal h
  rw [specGeneric_asIdeal, specClosed_asIdeal] at this
  exact hfield (isField_iff_maximalIdeal_eq.2 this.symm)

variable (hdim : ∀ P : Ideal O, P.IsPrime → P = ⊥ ∨ P = maximalIdeal O)
include hdim

/-- Every point of the spectrum is the generic point or the closed point. -/
theorem spec_eq_generic_or_closed (q : PrimeSpectrum O) :
    q = specGeneric O ∨ q = specClosed O := by
  rcases hdim q.asIdeal q.isPrime with h | h
  · exact Or.inl (PrimeSpectrum.ext h)
  · exact Or.inr (PrimeSpectrum.ext h)

/-- The generic point is the unique point of a basic open at a nonzero element of the maximal
ideal. -/
theorem basicOpen_eq_generic {f : O} (hf : f ≠ 0) (hfm : f ∈ maximalIdeal O) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum O)) = {specGeneric O} := by
  ext q
  simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, Set.mem_singleton_iff]
  constructor
  · intro hq
    rcases spec_eq_generic_or_closed hdim q with h | h
    · exact h
    · exact absurd (h ▸ hfm) hq
  · rintro rfl
    intro hc
    exact hf (Ideal.mem_bot.1 hc)

/-- The generic point is an open point. -/
theorem isOpen_specGeneric (hfield : ¬ IsField O) :
    IsOpen ({specGeneric O} : Set (PrimeSpectrum O)) := by
  obtain ⟨f, hfm, hf⟩ : ∃ f : O, f ∈ maximalIdeal O ∧ f ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hfield (isField_iff_maximalIdeal_eq.2
      (le_antisymm (fun a ha => Ideal.mem_bot.2 (hc a ha)) bot_le))
  rw [← basicOpen_eq_generic hdim hf hfm]
  exact (PrimeSpectrum.basicOpen f).2

/-- Every nonempty open subset of the spectrum contains the generic point. -/
theorem specGeneric_mem_of_nonempty {U : Set (PrimeSpectrum O)} (hU : IsOpen U)
    (hne : U.Nonempty) : specGeneric O ∈ U := by
  obtain ⟨q, hq⟩ := hne
  rcases spec_eq_generic_or_closed hdim q with h | h
  · exact h ▸ hq
  · refine (PrimeSpectrum.le_iff_specializes (specGeneric O) q).1 ?_ |>.mem_open hU hq
    rw [h]
    exact bot_le

/-- The only open sets are `∅`, the generic point, and the whole space. -/
theorem spec_isOpen_cases {U : Set (PrimeSpectrum O)} (hU : IsOpen U) :
    U = ∅ ∨ U = {specGeneric O} ∨ U = Set.univ := by
  rcases Set.eq_empty_or_nonempty U with rfl | hne
  · exact Or.inl rfl
  have hgen : specGeneric O ∈ U := specGeneric_mem_of_nonempty hdim hU hne
  by_cases hcl : specClosed O ∈ U
  · refine Or.inr (Or.inr ?_)
    refine Set.eq_univ_of_forall fun q => ?_
    rcases spec_eq_generic_or_closed hdim q with h | h
    · exact h ▸ hgen
    · exact h ▸ hcl
  · refine Or.inr (Or.inl ?_)
    refine Set.eq_singleton_iff_unique_mem.2 ⟨hgen, fun q hq => ?_⟩
    rcases spec_eq_generic_or_closed hdim q with h | h
    · exact h
    · exact absurd (h ▸ hq) hcl

end HTGeometry
