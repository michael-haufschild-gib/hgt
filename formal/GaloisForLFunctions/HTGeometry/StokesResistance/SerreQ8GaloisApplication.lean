import GaloisForLFunctions.HTGeometry.StokesResistance.QuaternionEquivariantResponse
import GaloisForLFunctions.RHTower.SerreQ8ArtinGaloisRealization

/-!
# Serre `Q₈` Galois application of Stokes symmetry counting

This module transports Moreau's finite-group response formulas from the abstract quaternion group
to the corpus's actual degree-eight Serre Galois field. Its literal Artin carrier has no invariant
vector, so its Reynolds average and character average vanish and its invariance-defect system is
injective. Its self-equivariant response space is nevertheless the one-dimensional scalar line.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

open MonoidAlgebra Representation
open RHTower

local notation "K3" => SerreQ8TopField

local instance : Fintype Gal(K3/ℚ) :=
  Fintype.ofEquiv _ serreQ8_galoisEquivQ8.toEquiv.symm

/-- Serre's concrete quaternionic Artin carrier has no invariant vector. -/
theorem serreQ8ArtinRepresentation_invariants_eq_bot :
    serreQ8ArtinRepresentation.invariants = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hfix := hv (serreQ8_galoisEquivQ8.symm (QuaternionGroup.a 2))
  rw [serreQ8ArtinRepresentation_central_apply] at hfix
  apply Prod.ext
  · exact CharZero.neg_eq_self_iff.mp (by simpa using congrArg Prod.fst hfix)
  · exact CharZero.neg_eq_self_iff.mp (by simpa using congrArg Prod.snd hfix)

/-- Every endomorphism commuting with the concrete Serre Galois action is scalar. -/
theorem serreQ8Artin_schur
    (f : Q8Carrier →ₗ[ℂ] Q8Carrier)
    (hf : ∀ g : Gal(K3/ℚ),
      (serreQ8ArtinRepresentation g) ∘ₗ f =
        f ∘ₗ (serreQ8ArtinRepresentation g)) :
    ∃ c : ℂ, ∀ v, f v = c • v := by
  apply deningerQ8_schur f
  intro q
  simpa [serreQ8ArtinRepresentation, deningerQ8ArtinRepresentation] using
    hf (serreQ8_galoisEquivQ8.symm q)

/-- Exactly one self-equivariant linear response survives the Serre Galois action. -/
theorem serreQ8Artin_selfIntertwining_finrank :
    Module.finrank ℂ
      (Representation.IntertwiningMap serreQ8ArtinRepresentation
        serreQ8ArtinRepresentation) = 1 := by
  rw [← LinearEquiv.finrank_eq
    (Representation.invariantsEquivIntertwiningMap serreQ8ArtinRepresentation
      serreQ8ArtinRepresentation)]
  exact GaloisForLFunctions.HTGeometry.GroupCharacter.finrank_invariants_linHom_eq_one
    serreQ8ArtinRepresentation serreQ8Artin_schur

/-- Normalized character average of Serre's Artin carrier vanishes. -/
theorem serreQ8Artin_character_average_eq_zero :
    (Fintype.card Gal(K3/ℚ) : ℂ)⁻¹ *
      ∑ g : Gal(K3/ℚ),
        LinearMap.trace ℂ Q8Carrier (serreQ8ArtinRepresentation g) = 0 := by
  rw [← finrank_invariants_eq_character_average,
    serreQ8ArtinRepresentation_invariants_eq_bot]
  simp

/-- Normalized self-character average of Serre's Artin carrier is one. -/
theorem serreQ8Artin_character_self_average_eq_one :
    (Fintype.card Gal(K3/ℚ) : ℂ)⁻¹ *
      ∑ g : Gal(K3/ℚ),
        LinearMap.trace ℂ Q8Carrier (serreQ8ArtinRepresentation g⁻¹) *
          LinearMap.trace ℂ Q8Carrier (serreQ8ArtinRepresentation g) = 1 := by
  change (Fintype.card Gal(K3/ℚ) : ℂ)⁻¹ *
      ∑ g : Gal(K3/ℚ),
        Representation.character serreQ8ArtinRepresentation g⁻¹ *
          Representation.character serreQ8ArtinRepresentation g = 1
  rw [← finrank_intertwiningMap_eq_character_product_average,
    serreQ8Artin_selfIntertwining_finrank]
  norm_num

/-- Reynolds averaging annihilates the complete Serre Artin carrier. -/
theorem finiteGroupAverage_serreQ8ArtinRepresentation_eq_zero :
    finiteGroupAverage serreQ8ArtinRepresentation = 0 := by
  apply LinearMap.ext
  intro v
  have hv := finiteGroupAverage_mem_invariants serreQ8ArtinRepresentation v
  rw [serreQ8ArtinRepresentation_invariants_eq_bot, Submodule.mem_bot] at hv
  simpa only [LinearMap.zero_apply] using hv

/-- Serre Galois symmetry equations have trivial vector kernel. -/
theorem ker_serreQ8Artin_invarianceDefect_eq_bot :
    LinearMap.ker (invarianceDefect serreQ8ArtinRepresentation) = ⊥ := by
  rw [ker_invarianceDefect, serreQ8ArtinRepresentation_invariants_eq_bot]

end GaloisForLFunctions.HTGeometry.StokesResistance
