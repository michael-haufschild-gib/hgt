import GaloisForLFunctions.RHTower.SerreQ8MonomialSourceLaw
import GaloisForLFunctions.RHTower.Artin.ArtinFrobeniusReciprocity

/-!
# Central-character blocks in quaternionic induction and restriction

The central-character compatibility behind Lo--Ray, arXiv:2611.14156,
Lemma 5.3, applies directly to the corpus's literal `C₄ ⊂ Q₈` source.
Even powers of its quartic character have central sign `+1`, whereas the
quaternionic representation has sign `-1`. Their intertwining spaces
vanish, both before and after induction, without Langlands assumptions.
-/

namespace GaloisForLFunctions.RepresentationLifting
open RHTower
noncomputable section

local instance : Fintype q8CyclicSubgroup := Fintype.ofFinite _

/-- The quaternionic central involution inside the actual cyclic source. -/
def q8CentralInSource : q8CyclicSubgroup :=
  ⟨QuaternionGroup.a 2, ⟨Multiplicative.ofAdd (2 : ZMod 4), rfl⟩⟩

theorem q8SourceCharacter_central :
    (q8CyclicSubgroupCharacter q8CentralInSource : ℂ) = -1 := by
  rw [q8CentralInSource, q8CyclicSubgroupCharacter_apply, q8OrderFourCharacter_apply]
  rw [show (2 : ZMod 4).val = 2 from ZMod.val_cast_of_lt (by norm_num)]
  norm_num

/-- Every even power belongs to the positive central block. -/
def q8EvenSourceRepresentation (m : ℕ) : Representation ℂ q8CyclicSubgroup ℂ :=
  linearCharacterRepresentation (q8CyclicSubgroupCharacter ^ (2 * m))

theorem q8EvenSourceRepresentation_central (m : ℕ) (z : ℂ) :
    q8EvenSourceRepresentation m q8CentralInSource z = z := by
  change ((q8CyclicSubgroupCharacter q8CentralInSource : ℂ) ^ (2 * m)) * z = z
  rw [q8SourceCharacter_central, pow_mul]
  norm_num

/-- Opposite central signs annihilate every map into the restricted quaternionic carrier. -/
theorem q8EvenSource_restricted_intertwiner_zero (m : ℕ)
    (f : (q8EvenSourceRepresentation m).IntertwiningMap
      (deningerQ8Representation.comp q8CyclicSubgroup.subtype)) : f = 0 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun (f.2 q8CentralInSource) z
  change f (q8EvenSourceRepresentation m q8CentralInSource z) =
    deningerQ8Representation (QuaternionGroup.a 2) (f z) at h
  rw [q8EvenSourceRepresentation_central, deningerQ8Representation_central_apply] at h
  have htwo : (2 : ℂ) • f z = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Frobenius reciprocity transports the same block exclusion to induced representations. -/
theorem q8EvenSource_induced_intertwiner_zero (m : ℕ)
    (f : (Representation.ind q8CyclicSubgroup.subtype (q8EvenSourceRepresentation m)).IntertwiningMap
      deningerQ8Representation) : f = 0 := by
  apply (indResIntertwiningEquiv q8CyclicSubgroup.subtype
    (q8EvenSourceRepresentation m) deningerQ8Representation).injective
  rw [map_zero]
  exact q8EvenSource_restricted_intertwiner_zero m _

/-- The restriction multiplicity is exactly zero for every even source character. -/
theorem q8EvenSource_restriction_pairing_zero (m : ℕ) :
    characterPairing q8CyclicSubgroup (q8EvenSourceRepresentation m).character
      (Representation.character (deningerQ8Representation.comp q8CyclicSubgroup.subtype)) = 0 := by
  letI : Subsingleton ((q8EvenSourceRepresentation m).IntertwiningMap
      (deningerQ8Representation.comp q8CyclicSubgroup.subtype)) :=
    ⟨fun f g => (q8EvenSource_restricted_intertwiner_zero m f).trans
      (q8EvenSource_restricted_intertwiner_zero m g).symm⟩
  rw [representationCharacterPairing_eq_finrank, Module.finrank_zero_of_subsingleton,
    Nat.cast_zero]

/-- The induction multiplicity is the same exact zero. -/
theorem q8EvenSource_induction_pairing_zero (m : ℕ) :
    characterPairing (QuaternionGroup 2)
      (Representation.ind q8CyclicSubgroup.subtype (q8EvenSourceRepresentation m)).character
      (Representation.character deningerQ8Representation) = 0 := by
  rw [characterPairing_induced_restricted]
  exact q8EvenSource_restriction_pairing_zero m

#print axioms q8SourceCharacter_central
#print axioms q8EvenSource_restricted_intertwiner_zero
#print axioms q8EvenSource_induced_intertwiner_zero
#print axioms q8EvenSource_restriction_pairing_zero
#print axioms q8EvenSource_induction_pairing_zero

end
end GaloisForLFunctions.RepresentationLifting
