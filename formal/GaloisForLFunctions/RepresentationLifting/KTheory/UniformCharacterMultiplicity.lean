import GaloisForLFunctions.RepresentationLifting.KTheory.VirtualFreenessDetection
import GaloisForLFunctions.RepresentationLifting.KTheory.FiniteAbelianVirtualRing

/-!
# Uniform multiplicities and virtual freeness

For finite abelian groups, virtual freeness is exactly uniformity of the
integral character multiplicities. Fourier inversion turns the nonidentity
trace obstruction into a discrepancy between two integral coefficients.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

variable (G : Type*) [CommGroup G] [Fintype G]
local instance : Finite (LinearCharacter G) := RHTower.deningerCharacterGroup_finite
local instance : Fintype (LinearCharacter G) := Fintype.ofFinite _

/-- Integral multiplicity of a linear character in a virtual representation. -/
def linearMultiplicity (χ : LinearCharacter G) (θ : VirtualRepresentationRing G) : ℤ :=
  virtualMultiplicity G (linearVirtualCharacter G χ) ⟨θ.val, θ.property⟩

/-- Every linear character occurs once in the regular representation. -/
theorem linearMultiplicity_regular (χ : LinearCharacter G) :
    linearMultiplicity G χ (regularVirtualRepresentation G) = 1 := by
  classical
  apply Int.cast_injective (α := ℂ)
  rw [linearMultiplicity, virtualMultiplicity_cast, Int.cast_one]
  simp only [characterPairing, regularVirtualRepresentation_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, inv_one, linearVirtualCharacter_apply,
    map_one, Units.val_one, mul_one, Nat.card_eq_fintype_card]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Integer scaling scales every Fourier multiplicity. -/
theorem linearMultiplicity_zsmul (χ : LinearCharacter G) (m : ℤ)
    (θ : VirtualRepresentationRing G) :
    linearMultiplicity G χ (m • θ) = m * linearMultiplicity G χ θ := by
  apply Int.cast_injective (α := ℂ)
  simp only [linearMultiplicity, Int.cast_mul, virtualMultiplicity_cast]
  simp only [characterPairing, Subring.coe_zsmul, Pi.smul_apply, zsmul_eq_mul,
    mul_assoc, ← Finset.mul_sum]
  ring

/-- Fourier inversion in the concrete virtual-representation ring. -/
theorem virtualRepresentation_fourier (θ : VirtualRepresentationRing G) :
    θ = ∑ χ : LinearCharacter G, linearMultiplicity G χ θ • linearCharacterVirtualHom G χ := by
  apply Subtype.ext
  have h := congrArg (fun v : VirtualCharacter G => v.val)
    (finiteAbelian_virtual_fourier_integral_subtype (G := G) ⟨θ.val, θ.property⟩)
  simpa [linearMultiplicity, linearCharacterVirtualHom] using h

/-- Virtual freeness is uniform integral multiplicity across the character group. -/
theorem isVirtuallyFree_iff_uniform_multiplicity (θ : VirtualRepresentationRing G) :
    IsVirtuallyFree G θ ↔ ∃ m : ℤ, ∀ χ : LinearCharacter G, linearMultiplicity G χ θ = m := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, fun χ => by rw [linearMultiplicity_zsmul, linearMultiplicity_regular, mul_one]⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    conv_lhs => rw [virtualRepresentation_fourier]
    rw [virtualRepresentation_fourier G (regularVirtualRepresentation G)]
    simp only [linearMultiplicity_regular, one_smul, Finset.smul_sum, hm]

/-- Two unequal Fourier multiplicities are exactly the obstruction to virtual freeness. -/
theorem not_isVirtuallyFree_iff_multiplicity_discrepancy (θ : VirtualRepresentationRing G) :
    ¬ IsVirtuallyFree G θ ↔
      ∃ χ ψ : LinearCharacter G, linearMultiplicity G χ θ ≠ linearMultiplicity G ψ θ := by
  rw [isVirtuallyFree_iff_uniform_multiplicity]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    exact h ⟨linearMultiplicity G 1 θ, fun χ => hn χ 1⟩
  · rintro ⟨χ, ψ, h⟩ ⟨m, hm⟩
    exact h ((hm χ).trans (hm ψ).symm)

#print axioms linearMultiplicity_regular
#print axioms isVirtuallyFree_iff_uniform_multiplicity
#print axioms not_isVirtuallyFree_iff_multiplicity_discrepancy

end GaloisForLFunctions.RepresentationLifting
