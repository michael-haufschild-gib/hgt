import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCharacterPoints

/-!
# Functorial classes of characters and dominant morphisms

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 4.5
(`t44n`).

An admissible class of characters is *functorial* when it is stable not only under precomposition
with an isomorphism of fields but under precomposition with an arbitrary homomorphism of fields.
A morphism of schemes induces on residue fields exactly such a homomorphism, so the character
points in a functorial admissible class are carried into the character points in that class.  This
contains Deninger's statement for a dominant morphism of integral normal schemes: no hypothesis on
the morphism is used.

The class of all characters is functorial, so the notion is not vacuous.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

universe u

variable {X Y : Scheme.{u}} {C : Type u} [Field C]

/-- **Deninger, §4.**  A *functorial* admissible class of characters: stable under precomposition
with an arbitrary homomorphism of fields. -/
structure DeningerFunctorialClass (C : Type u) [Field C] (N₀ : Submonoid ℕ) extends
    DeningerAdmissibleClass C N₀ where
  /-- The class is stable under precomposition with a homomorphism of fields. -/
  comp_mem : ∀ {k l : Type u} [Field k] [Field l] (σ : k →+* l) (χ : lˣ →* Cˣ),
    mem χ → mem (χ.comp (Units.map (σ : k →* l)))

/-- The class of all characters is admissible. -/
def deningerAllCharacters (C : Type u) [Field C] (N₀ : Submonoid ℕ) :
    DeningerAdmissibleClass C N₀ where
  mem _ := True
  comp_iff _ _ := Iff.rfl
  pow_iff _ _ _ _ := Iff.rfl

/-- The class of all characters is functorial, so functorial admissible classes exist. -/
def deningerAllCharactersFunctorial (C : Type u) [Field C] (N₀ : Submonoid ℕ) :
    DeningerFunctorialClass C N₀ where
  toDeningerAdmissibleClass := deningerAllCharacters C N₀
  comp_mem _ _ _ := trivial

/-- **Deninger, Proposition 4.5 (`t44n`).**  A morphism of schemes carries the character points
lying in a functorial admissible class into the character points lying in that class. -/
theorem deningerCharPointsIn_map_mem {N₀ : Submonoid ℕ} (E : DeningerFunctorialClass C N₀)
    (f : X ⟶ Y) {P : DeningerCharPoints X C}
    (hP : P ∈ deningerCharPointsIn E.toDeningerAdmissibleClass X) :
    deningerCharPointsMap f P ∈ deningerCharPointsIn E.toDeningerAdmissibleClass Y :=
  E.comp_mem (f.residueFieldMap P.1).hom P.2 hP

/-- **Deninger, Proposition 4.5 (`t44n`)**, as a statement about the two subsets. -/
theorem deningerCharPointsIn_mapsTo {N₀ : Submonoid ℕ} (E : DeningerFunctorialClass C N₀)
    (f : X ⟶ Y) :
    Set.MapsTo (deningerCharPointsMap (C := C) f)
      (deningerCharPointsIn E.toDeningerAdmissibleClass X)
      (deningerCharPointsIn E.toDeningerAdmissibleClass Y) :=
  fun _ hP => deningerCharPointsIn_map_mem E f hP

end RHTower
