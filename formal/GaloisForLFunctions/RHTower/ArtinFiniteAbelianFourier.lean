import GaloisForLFunctions.RHTower.ArtinCharacterMultiplicity
import GaloisForLFunctions.RHTower.DeningerFiniteCharacterBasis

/-!
# Integral Fourier decomposition of concrete Artin characters on finite abelian groups

For a finite abelian group, the existing Deninger character basis is a complex vector-space
basis.  This file supplies the missing integral lift: its Fourier coefficients on concrete virtual
characters are integers and on concrete genuine characters are naturals.  The result is standard
finite-group character theory, not an Artin-holomorphy claim.
-/

open scoped BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

noncomputable local instance finiteLinearCharacter
    {G : Type u} [CommGroup G] [Finite G] : Finite (LinearCharacter G) :=
  RHTower.deningerCharacterGroup_finite

noncomputable local instance fintypeLinearCharacter
    {G : Type u} [CommGroup G] [Finite G] : Fintype (LinearCharacter G) :=
  Fintype.ofFinite _

/-- Normalized character pairing of two concrete linear characters. -/
theorem linearCharacterPairing_orthonormal {G : Type u} [CommGroup G] [Fintype G]
    (χ ψ : LinearCharacter G) :
    characterPairing G (RHTower.deningerCharacterFn χ) (RHTower.deningerCharacterFn ψ) =
      if χ = ψ then 1 else 0 := by
  have hχ : (linearCharacterRepresentation χ).character =
      RHTower.deningerCharacterFn χ := by
    ext g
    exact linearGenuineCharacter_apply G χ g
  have hψ : (linearCharacterRepresentation ψ).character =
      RHTower.deningerCharacterFn ψ := by
    ext g
    exact linearGenuineCharacter_apply G ψ g
  rw [← hχ, ← hψ]
  classical
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  letI : Representation.IsIrreducible (linearCharacterRepresentation χ) := by
    apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
    exact (isSimpleModule_iff ..).mpr
      (is_simple_module_of_finrank_eq_one (A := MonoidAlgebra ℂ G) (by
        simpa using (linearCharacterRepresentation χ).asModuleEquiv.finrank_eq))
  letI : Representation.IsIrreducible (linearCharacterRepresentation ψ) := by
    apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
    exact (isSimpleModule_iff ..).mpr
      (is_simple_module_of_finrank_eq_one (A := MonoidAlgebra ℂ G) (by
        simpa using (linearCharacterRepresentation ψ).asModuleEquiv.finrank_eq))
  have hequiv : Nonempty ((linearCharacterRepresentation χ).Equiv
      (linearCharacterRepresentation ψ)) ↔ χ = ψ := by
    constructor
    · rintro ⟨e⟩
      apply MonoidHom.ext
      intro g
      apply Units.ext
      simpa only [linearCharacterRepresentation_character] using
        congrFun (Representation.char_iso e) g
    · intro h
      subst ψ
      exact ⟨Representation.Equiv.refl _⟩
  change (Nat.card G : ℂ)⁻¹ * ∑ g : G,
    (linearCharacterRepresentation ψ).character g *
      (linearCharacterRepresentation χ).character g⁻¹ = if χ = ψ then 1 else 0
  rw [Representation.char_orthonormal (linearCharacterRepresentation ψ)
    (linearCharacterRepresentation χ)]
  simp only [hequiv]

/-- Linearity of the normalized pairing in its second argument. -/
theorem characterPairing_smul_right {G : Type u} [Group G] [Fintype G]
    (χ ψ : G → ℂ) (a : ℂ) :
    characterPairing G χ (a • ψ) = a * characterPairing G χ ψ := by
  simp [characterPairing, Finset.mul_sum, mul_assoc, mul_comm]

/-- Fourier inversion in the finite-abelian character basis. -/
theorem finiteAbelian_fourier_reconstruction {G : Type u} [CommGroup G] [Fintype G]
    (f : G → ℂ) :
    (∑ χ : LinearCharacter G,
      characterPairing G (RHTower.deningerCharacterFn χ) f •
        RHTower.deningerCharacterFn χ) = f := by
  classical
  have hf : f ∈ Submodule.span ℂ
      (Set.range (RHTower.deningerCharacterFn : LinearCharacter G → (G → ℂ))) := by
    rw [RHTower.deningerCharacter_span]
    exact Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨ψ, rfl⟩ := hx
      simp only [linearCharacterPairing_orthonormal, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
  | zero => simp only [characterPairing_zero_right, zero_smul, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
      simp_rw [characterPairing_add_right]
      simp only [add_smul, Finset.sum_add_distrib, hx, hy]
  | smul a x _ hx =>
      simp_rw [characterPairing_smul_right]
      calc
        ∑ χ : LinearCharacter G,
            (a * characterPairing G (RHTower.deningerCharacterFn χ) x) •
              RHTower.deningerCharacterFn χ =
            a • (∑ χ : LinearCharacter G,
              characterPairing G (RHTower.deningerCharacterFn χ) x •
                RHTower.deningerCharacterFn χ) := by
              simp only [Finset.smul_sum, mul_smul]
        _ = a • x := by rw [hx]

/-- Integral Fourier decomposition of every concrete virtual character of a finite abelian group.
The coefficient of `χ` is the virtual multiplicity of `χ` in `θ`. -/
theorem finiteAbelian_virtual_fourier_integral {G : Type u} [CommGroup G] [Fintype G]
    (θ : VirtualCharacter G) :
    θ.val = ∑ χ : LinearCharacter G,
      (virtualMultiplicity G (linearVirtualCharacter G χ) θ : ℂ) •
        RHTower.deningerCharacterFn χ := by
  symm
  calc
    (∑ χ : LinearCharacter G,
        (virtualMultiplicity G (linearVirtualCharacter G χ) θ : ℂ) •
          RHTower.deningerCharacterFn χ) =
        ∑ χ : LinearCharacter G,
          characterPairing G (RHTower.deningerCharacterFn χ) θ.val •
            RHTower.deningerCharacterFn χ := by
          apply Finset.sum_congr rfl
          intro χ _
          rw [virtualMultiplicity_cast]
          congr 2
          ext g
          exact linearVirtualCharacter_apply G χ g
    _ = θ.val := finiteAbelian_fourier_reconstruction θ.val

/-- Nonnegative integral Fourier decomposition of every concrete genuine character of a finite
abelian group.  The coefficient of `χ` is its genuine multiplicity in `θ`. -/
theorem finiteAbelian_genuine_fourier_integral {G : Type u} [CommGroup G] [Fintype G]
    (θ : GenuineCharacter G) :
    θ.val = ∑ χ : LinearCharacter G,
      (genuineMultiplicity G (linearGenuineCharacter G χ) θ : ℂ) •
        RHTower.deningerCharacterFn χ := by
  symm
  calc
    (∑ χ : LinearCharacter G,
        (genuineMultiplicity G (linearGenuineCharacter G χ) θ : ℂ) •
          RHTower.deningerCharacterFn χ) =
        ∑ χ : LinearCharacter G,
          characterPairing G (RHTower.deningerCharacterFn χ) θ.val •
            RHTower.deningerCharacterFn χ := by
          apply Finset.sum_congr rfl
          intro χ _
          rw [genuineMultiplicity_cast]
          congr 2
          ext g
          exact linearGenuineCharacter_apply G χ g
    _ = θ.val := finiteAbelian_fourier_reconstruction θ.val

/-- The virtual Fourier formula lifted from functions to the concrete virtual-character subtype. -/
theorem finiteAbelian_virtual_fourier_integral_subtype {G : Type u} [CommGroup G] [Fintype G]
    (θ : VirtualCharacter G) :
    θ = ∑ χ : LinearCharacter G,
      virtualMultiplicity G (linearVirtualCharacter G χ) θ • linearVirtualCharacter G χ := by
  apply Subtype.ext
  ext g
  rw [finiteAbelian_virtual_fourier_integral]
  simp [RHTower.deningerCharacterFn_apply, linearVirtualCharacter_apply]

/-- The genuine Fourier formula lifted from functions to the concrete genuine-character subtype. -/
theorem finiteAbelian_genuine_fourier_integral_subtype {G : Type u} [CommGroup G] [Fintype G]
    (θ : GenuineCharacter G) :
    θ = ∑ χ : LinearCharacter G,
      genuineMultiplicity G (linearGenuineCharacter G χ) θ • linearGenuineCharacter G χ := by
  apply Subtype.ext
  ext g
  rw [finiteAbelian_genuine_fourier_integral]
  simp [RHTower.deningerCharacterFn_apply, linearGenuineCharacter_apply]

/-- Additive group generated by the concrete linear virtual characters. -/
def finiteAbelianLinearVirtualCharacterGroup (G : Type u) [Group G] [Fintype G] :
    AddSubgroup (G → ℂ) :=
  AddSubgroup.closure (Set.range fun χ : LinearCharacter G => (linearVirtualCharacter G χ).val)

/-- Additive monoid generated by the concrete linear genuine characters. -/
def finiteAbelianLinearGenuineCharacterMonoid (G : Type u) [Group G] [Fintype G] :
    AddSubmonoid (G → ℂ) :=
  AddSubmonoid.closure (Set.range fun χ : LinearCharacter G => (linearGenuineCharacter G χ).val)

/-- Every concrete virtual character of a finite abelian group is exactly an integer combination
of its linear characters. -/
theorem finiteAbelian_virtualCharacterGroup_eq_linear {G : Type u} [CommGroup G] [Fintype G] :
    virtualCharacterGroup G = finiteAbelianLinearVirtualCharacterGroup G := by
  apply le_antisymm
  · intro f hf
    let θ : VirtualCharacter G := ⟨f, hf⟩
    have hθ := finiteAbelian_virtual_fourier_integral_subtype θ
    have hval := congrArg (fun x : VirtualCharacter G => x.val) hθ
    have hval' : f = ∑ χ : LinearCharacter G,
        virtualMultiplicity G (linearVirtualCharacter G χ) θ • (linearVirtualCharacter G χ).val := by
      simpa using hval
    rw [hval']
    apply AddSubgroup.sum_mem
    intro χ _
    apply AddSubgroup.zsmul_mem
    show (linearVirtualCharacter G χ).val ∈ finiteAbelianLinearVirtualCharacterGroup G
    apply AddSubgroup.subset_closure
    exact ⟨χ, rfl⟩
  · apply (AddSubgroup.closure_le (virtualCharacterGroup G)).2
    rintro f ⟨χ, rfl⟩
    exact (linearVirtualCharacter G χ).property

/-- Every concrete genuine character of a finite abelian group is exactly a natural combination
of its linear characters. -/
theorem finiteAbelian_genuineCharacterMonoid_eq_linear {G : Type u} [CommGroup G] [Fintype G] :
    genuineCharacterMonoid G = finiteAbelianLinearGenuineCharacterMonoid G := by
  apply le_antisymm
  · intro f hf
    let θ : GenuineCharacter G := ⟨f, hf⟩
    have hθ := finiteAbelian_genuine_fourier_integral_subtype θ
    have hval := congrArg (fun x : GenuineCharacter G => x.val) hθ
    have hval' : f = ∑ χ : LinearCharacter G,
        genuineMultiplicity G (linearGenuineCharacter G χ) θ • (linearGenuineCharacter G χ).val := by
      simpa using hval
    rw [hval']
    apply AddSubmonoid.sum_mem
    intro χ _
    apply AddSubmonoid.nsmul_mem
    show (linearGenuineCharacter G χ).val ∈ finiteAbelianLinearGenuineCharacterMonoid G
    apply AddSubmonoid.subset_closure
    exact ⟨χ, rfl⟩
  · apply AddSubmonoid.closure_le.mpr
    rintro f ⟨χ, rfl⟩
    exact (linearGenuineCharacter G χ).property

end GaloisForLFunctions
