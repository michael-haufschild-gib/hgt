import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheClassCharactersTogetherCarryTheContactsOfTheIdealsOfTrivialClass

/-!
# Fourier projectors onto every ideal class

Weighting a class-character sum by its inverse value at a target class selects exactly
that class. The same identity applies to arbitrary finite weighted ideal sums, providing
the orthogonality step of Lemma 5.3 of arXiv:2610.23742 for the number-field corpus.
-/

noncomputable section
open scoped BigOperators Classical
open NumberField
namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {G : Type*} [CommGroup G] [Finite G]
local instance : Fintype (G →* ℂˣ) := Fintype.ofFinite _

/-- Unnormalized Fourier projector onto a target element of a finite abelian group. -/
def classCharacterProjector (target g : G) : ℂ :=
  ∑ χ : G →* ℂˣ, ((χ (target⁻¹ * g) : ℂˣ) : ℂ)

/-- Character orthogonality selects any target class, including nonprincipal classes. -/
theorem classCharacterProjector_eq (target g : G) :
    classCharacterProjector target g =
      if g = target then (Fintype.card (G →* ℂˣ) : ℂ) else 0 := by
  by_cases h : g = target
  · subst g
    simp [classCharacterProjector]
  · rw [if_neg h]
    apply sum_monoidHom_apply_eq_zero
    intro he
    apply h
    simpa using congrArg (fun z => target * z) he

/-- A finite class Fourier transform of an arbitrary weighted family. -/
def finiteClassFourier {ι : Type*} (label : ι → G) (S : Finset ι) (weight : ι → ℂ)
    (χ : G →* ℂˣ) : ℂ :=
  ∑ i ∈ S, ((χ (label i) : ℂˣ) : ℂ) * weight i

/-- Inverse-character weighting recovers the exact mass of one class. -/
theorem finiteClassFourier_projector {ι : Type*} (label : ι → G) (S : Finset ι)
    (weight : ι → ℂ) (target : G) :
    (∑ χ : G →* ℂˣ, ((χ target⁻¹ : ℂˣ) : ℂ) * finiteClassFourier label S weight χ) =
      (Fintype.card (G →* ℂˣ) : ℂ) * ∑ i ∈ S.filter (fun i => label i = target), weight i := by
  simp only [finiteClassFourier, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (∑ χ : G →* ℂˣ,
      ((χ target⁻¹ : ℂˣ) : ℂ) * (((χ (label i) : ℂˣ) : ℂ) * weight i)) =
      classCharacterProjector target (label i) * weight i := by
    simp only [classCharacterProjector, Finset.sum_mul, map_mul, Units.val_mul, mul_assoc]
  rw [hi, classCharacterProjector_eq]
  split_ifs <;> simp

/-- Distinct class projectors have disjoint support, with the diagonal normalization explicit. -/
theorem classCharacterProjector_mul (a b g : G) :
    classCharacterProjector a g * classCharacterProjector b g =
      if a = b then (Fintype.card (G →* ℂˣ) : ℂ) * classCharacterProjector a g else 0 := by
  simp only [classCharacterProjector_eq]
  split_ifs <;> simp_all

variable (K : Type*) [Field K] [NumberField K]

/-- Fourier projection of any finite weighted family of nonzero ideals onto any ideal class. -/
theorem idealClassFourier_projector (S : Finset (Ideal (𝓞 K))⁰)
    (weight : (Ideal (𝓞 K))⁰ → ℂ) (C : ClassGroup (𝓞 K)) :
    (∑ χ : ClassGroup (𝓞 K) →* ℂˣ,
      ((χ C⁻¹ : ℂˣ) : ℂ) * finiteClassFourier ClassGroup.mk0 S weight χ) =
      (Fintype.card (ClassGroup (𝓞 K) →* ℂˣ) : ℂ) *
        ∑ I ∈ S.filter (fun I => ClassGroup.mk0 I = C), weight I :=
  finiteClassFourier_projector ClassGroup.mk0 S weight C

#print axioms finiteClassFourier_projector
#print axioms classCharacterProjector_mul
#print axioms idealClassFourier_projector

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
