import GaloisForLFunctions.RepresentationLifting.KTheory.VirtualFreenessDetection
import GaloisForLFunctions.RepresentationLifting.KTheory.FiniteAbelianVirtualRing

/-!
# Uniform multiplicities and virtual freeness

For finite abelian groups, virtual freeness is exactly uniformity of the
integral character multiplicities. Fourier inversion turns the nonidentity
trace obstruction into a discrepancy between two integral coefficients.
-/

open scoped BigOperators Classical
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

variable (G : Type*) [CommGroup G] [Fintype G]
local instance : Finite (LinearCharacter G) := RHTower.deningerCharacterGroup_finite
local instance : Fintype (LinearCharacter G) := Fintype.ofFinite _

/-- Integral multiplicity of a linear character in a virtual representation. -/
def linearMultiplicity (χ : LinearCharacter G) (θ : VirtualRepresentationRing G) : ℤ :=
  virtualMultiplicity G (linearVirtualCharacter G χ) ⟨θ.val, θ.property⟩

theorem linearMultiplicity_zero (χ : LinearCharacter G) :
    linearMultiplicity G χ 0 = 0 := by
  apply Int.cast_injective (α := ℂ)
  simp [linearMultiplicity, characterPairing]

theorem linearMultiplicity_add (χ : LinearCharacter G) (θ η : VirtualRepresentationRing G) :
    linearMultiplicity G χ (θ + η) = linearMultiplicity G χ θ + linearMultiplicity G χ η :=
  virtualMultiplicity_add_right G _ _ _

/-- Multiplicities are additive over any finite collection of virtual classes. -/
theorem linearMultiplicity_sum {ι : Type*} (χ : LinearCharacter G) (s : Finset ι)
    (θ : ι → VirtualRepresentationRing G) :
    linearMultiplicity G χ (∑ i ∈ s, θ i) = ∑ i ∈ s, linearMultiplicity G χ (θ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, linearMultiplicity_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, linearMultiplicity_add, ih,
      Finset.sum_insert hi]

/-- A linear character has multiplicity one in itself and zero in every other one. -/
theorem linearMultiplicity_linear (χ ψ : LinearCharacter G) :
    linearMultiplicity G χ (linearCharacterVirtualHom G ψ) = if χ = ψ then 1 else 0 := by
  classical
  apply Int.cast_injective (α := ℂ)
  rw [linearMultiplicity, virtualMultiplicity_cast]
  have hχ : (linearVirtualCharacter G χ).val = RHTower.deningerCharacterFn χ :=
    funext (linearVirtualCharacter_apply G χ)
  have hψ : (linearCharacterVirtualHom G ψ).val = RHTower.deningerCharacterFn ψ :=
    funext (linearVirtualCharacter_apply G ψ)
  rw [hχ, hψ, linearCharacterPairing_orthonormal]
  split_ifs <;> simp

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
  change characterPairing G (linearVirtualCharacter G χ).val (m • θ.val) =
    (m : ℂ) * characterPairing G (linearVirtualCharacter G χ).val θ.val
  simp only [characterPairing, Pi.smul_apply, zsmul_eq_mul, mul_assoc, ← Finset.mul_sum]
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
    push Not at hn
    exact h ⟨linearMultiplicity G 1 θ, fun χ => hn χ 1⟩
  · rintro ⟨χ, ψ, h⟩ ⟨m, hm⟩
    exact h ((hm χ).trans (hm ψ).symm)

/-- A virtually free class with no trivial-character component is zero. -/
theorem isVirtuallyFree_and_trivialMultiplicity_zero_iff (θ : VirtualRepresentationRing G) :
    (IsVirtuallyFree G θ ∧ linearMultiplicity G 1 θ = 0) ↔ θ = 0 := by
  constructor
  · rintro ⟨⟨m, rfl⟩, hm⟩
    rw [linearMultiplicity_zsmul, linearMultiplicity_regular, mul_one] at hm
    rw [hm, zero_smul]
  · rintro rfl
    exact ⟨⟨0, (zero_smul ℤ _).symm⟩, linearMultiplicity_zero G 1⟩

#print axioms linearMultiplicity_regular
#print axioms isVirtuallyFree_iff_uniform_multiplicity
#print axioms not_isVirtuallyFree_iff_multiplicity_discrepancy

end GaloisForLFunctions.RepresentationLifting
