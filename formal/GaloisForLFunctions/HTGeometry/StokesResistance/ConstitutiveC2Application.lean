import GaloisForLFunctions.HTGeometry.StokesResistance.FiniteGroupCharacter
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConstitutiveSoldering

/-!
# `C₂` constitutive-soldering application of Stokes symmetry counting

The constitutive-soldering corpus contains a two-element example with trivial source action and
sign target action. Its Reynolds projection was computed directly to be zero. This module packages
both actions as genuine representations and derives the structural reason from Moreau's
equivariant-response character formula: the intertwining space has dimension zero because

`(1·1 + 1·(-1))/2 = 0`.

Thus no equivariant constitutive map connects the two histories. The result is the one-dimensional
`C₂` instance of the response-space symmetry counts used for Stokes resistance.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

open MonoidAlgebra Representation
open _root_.HTGeometry.ConstraintRelativity

/-- Trivial `C₂` matrix action as a representation on a one-dimensional carrier. -/
def c2TrivialRepresentation : Representation ℂ C2 (Fin 1 → ℂ) where
  toFun g := (c2Trivial g).toLin'
  map_one' := by ext v; simp [c2Trivial]
  map_mul' g h := by ext v; simp [c2Trivial_mul, Module.End.mul_apply]

/-- Sign `C₂` matrix action as a representation on a one-dimensional carrier. -/
def c2SignRepresentation : Representation ℂ C2 (Fin 1 → ℂ) where
  toFun g := (c2Sign g).toLin'
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp [c2Sign_mul, Module.End.mul_apply]

@[simp] theorem c2TrivialRepresentation_character (g : C2) :
    c2TrivialRepresentation.character g = 1 := by
  simp [Representation.character, c2TrivialRepresentation, c2Trivial,
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 1)), Matrix.trace]

@[simp] theorem c2SignRepresentation_character_one :
    c2SignRepresentation.character 1 = 1 := by
  simp [Representation.character, c2SignRepresentation,
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 1)), Matrix.trace]

@[simp] theorem c2SignRepresentation_character_gen :
    c2SignRepresentation.character c2Gen = -1 := by
  simp [Representation.character, c2SignRepresentation,
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 1)), Matrix.trace]

/-- Moreau's equivariant-map count gives no trivial-to-sign constitutive soldering. -/
theorem finrank_c2_trivial_sign_intertwining_eq_zero :
    Module.finrank ℂ
      (Representation.IntertwiningMap c2TrivialRepresentation c2SignRepresentation) = 0 := by
  have h := finrank_intertwiningMap_eq_character_product_average
    c2TrivialRepresentation c2SignRepresentation
  rw [c2_univ] at h
  rw [Finset.sum_insert (by simp [Ne.symm c2Gen_ne_one]), Finset.sum_singleton] at h
  norm_num at h
  exact_mod_cast h

end GaloisForLFunctions.HTGeometry.StokesResistance
