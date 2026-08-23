import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import GaloisForLFunctions.RHTower.DeningerDynSysRootsOfUnityReduction

/-!
# Character points of a scheme and admissible classes of characters

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §3 and §4.

For a scheme `X` and a field `C`, the set

`X̂ (C) = { (x , P) | x ∈ X , P : κ (x)ˣ → Cˣ a homomorphism }`

carries the Frobenius operators `F_ν (x , P) = (x , P ^ ν)` and is functorial in `X`: a morphism
`f : X ⟶ Y` sends `(x , P)` to `(f x , P ∘ (κ (f x)ˣ → κ (x)ˣ))`.  The Frobenius operators are
injective as soon as the residue fields are algebraically closed, because two characters with the
same `ν`-th power agree on every `ν`-th power and `κ (x)ˣ` is `ν`-divisible.

Definition 4.1 introduces admissible classes of characters: classes stable under precomposition
with field isomorphisms and under raising to a power from a given submonoid of `ℕ`.  Proposition
4.2 says that the corresponding subsets of `X̂ (C)` are invariant under both structures, and
Corollary 4.4 that the projection to `X` is surjective for a class containing all injective
characters.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory Cardinal

universe u

variable {X Y Z : Scheme.{u}} {C : Type u} [Field C]

/-- **Deninger, §3.**  The space `X̂ (C)` of `C`-valued character points of a scheme: a point of
`X` together with a character of the units of its residue field. -/
abbrev DeningerCharPoints (X : Scheme.{u}) (C : Type u) [Field C] : Type u :=
  Σ x : X, ((X.residueField x)ˣ →* Cˣ)

/-- **Deninger, §3.**  The Frobenius operator `F_ν` on character points. -/
noncomputable def deningerCharFrobenius (ν : ℕ) (P : DeningerCharPoints X C) :
    DeningerCharPoints X C :=
  ⟨P.1, P.2 ^ ν⟩

@[simp] theorem deningerCharFrobenius_fst (ν : ℕ) (P : DeningerCharPoints X C) :
    (deningerCharFrobenius ν P).1 = P.1 := rfl

@[simp] theorem deningerCharFrobenius_snd (ν : ℕ) (P : DeningerCharPoints X C) :
    (deningerCharFrobenius ν P).2 = P.2 ^ ν := rfl

@[simp] theorem deningerCharFrobenius_one (P : DeningerCharPoints X C) :
    deningerCharFrobenius 1 P = P := by
  obtain ⟨x, χ⟩ := P
  exact congrArg (Sigma.mk x) (pow_one χ)

/-- The Frobenius operators compose multiplicatively. -/
theorem deningerCharFrobenius_comp (ν μ : ℕ) (P : DeningerCharPoints X C) :
    deningerCharFrobenius ν (deningerCharFrobenius μ P) = deningerCharFrobenius (μ * ν) P := by
  obtain ⟨x, χ⟩ := P
  exact congrArg (Sigma.mk x) (pow_mul χ μ ν).symm

/-- A character of the units of an algebraically closed field is determined by its `ν`-th power. -/
theorem deningerChar_pow_injective {k : Type*} [Field k] [IsAlgClosed k] {ν : ℕ} (hν : 0 < ν)
    {χ ψ : kˣ →* Cˣ} (h : χ ^ ν = ψ ^ ν) : χ = ψ := by
  ext a
  obtain ⟨b, rfl⟩ := deningerUnits_exists_pow (C := k) hν.ne' a
  have h2 : χ b ^ ν = ψ b ^ ν := by
    have hb := congrArg (fun f : kˣ →* Cˣ => f b) h
    simpa using hb
  rw [map_pow, map_pow, h2]

/-- **Deninger, Proposition 4.2, last assertion.**  The Frobenius operators act by injections on
the character points of a scheme with algebraically closed residue fields. -/
theorem deningerCharFrobenius_injective (halg : ∀ x : X, IsAlgClosed (X.residueField x)) {ν : ℕ}
    (hν : 0 < ν) : Function.Injective (deningerCharFrobenius (X := X) (C := C) ν) := by
  rintro ⟨x, χ⟩ ⟨y, ψ⟩ h
  simp only [deningerCharFrobenius, Sigma.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1
  haveI := halg x
  exact Sigma.ext rfl (heq_of_eq (deningerChar_pow_injective hν (eq_of_heq h2)))

/-! ## Functoriality -/

/-- The map on character points induced by a morphism of schemes. -/
noncomputable def deningerCharPointsMap (f : X ⟶ Y) (P : DeningerCharPoints X C) :
    DeningerCharPoints Y C :=
  ⟨f.base P.1, P.2.comp (Units.map (f.residueFieldMap P.1).hom.toMonoidHom)⟩

@[simp] theorem deningerCharPointsMap_fst (f : X ⟶ Y) (P : DeningerCharPoints X C) :
    (deningerCharPointsMap f P).1 = f.base P.1 := rfl

theorem deningerCharPointsMap_id (P : DeningerCharPoints X C) :
    deningerCharPointsMap (𝟙 X) P = P := by
  obtain ⟨x, χ⟩ := P
  refine Sigma.ext rfl (heq_of_eq ?_)
  show χ.comp (Units.map (Scheme.Hom.residueFieldMap (𝟙 X) x).hom.toMonoidHom) = χ
  rw [Scheme.residueFieldMap_id]
  ext a
  rfl

theorem deningerCharPointsMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (P : DeningerCharPoints X C) :
    deningerCharPointsMap (f ≫ g) P
      = deningerCharPointsMap g (deningerCharPointsMap f P) := by
  obtain ⟨x, χ⟩ := P
  refine Sigma.ext rfl (heq_of_eq ?_)
  show χ.comp (Units.map (Scheme.Hom.residueFieldMap (f ≫ g) x).hom.toMonoidHom) = _
  rw [Scheme.residueFieldMap_comp]
  ext a
  rfl

/-- Frobenius commutes with the functorial maps. -/
theorem deningerCharPointsMap_frobenius (f : X ⟶ Y) (ν : ℕ) (P : DeningerCharPoints X C) :
    deningerCharPointsMap f (deningerCharFrobenius ν P)
      = deningerCharFrobenius ν (deningerCharPointsMap f P) := by
  obtain ⟨x, χ⟩ := P
  refine Sigma.ext rfl (heq_of_eq ?_)
  ext a
  rfl

/-! ## Admissible classes of characters -/

/-- **Deninger, Definition 4.1.**  An `N₀`-admissible class of characters into `Cˣ`: a class of
characters on fields, stable under precomposition with field isomorphisms and under raising to a
power in the submonoid `N₀ ⊆ ℕ`. -/
structure DeningerAdmissibleClass (C : Type u) [Field C] (N₀ : Submonoid ℕ) where
  /-- Membership of a character in the class. -/
  mem : ∀ {k : Type u} [Field k], (kˣ →* Cˣ) → Prop
  /-- The class only depends on the character up to a field isomorphism. -/
  comp_iff : ∀ {k l : Type u} [Field k] [Field l] (σ : k ≃+* l) (χ : lˣ →* Cˣ),
    mem χ ↔ mem (χ.comp (Units.map (σ : k →* l)))
  /-- The class is forward and backward invariant under the `N₀`-power maps. -/
  pow_iff : ∀ {k : Type u} [Field k] (χ : kˣ →* Cˣ) {ν : ℕ}, ν ∈ N₀ → 0 < ν →
    (mem χ ↔ mem (χ ^ ν))

/-- The subset of `X̂ (C)` cut out by an admissible class. -/
def deningerCharPointsIn {N₀ : Submonoid ℕ} (E : DeningerAdmissibleClass C N₀)
    (X : Scheme.{u}) : Set (DeningerCharPoints X C) :=
  {P | E.mem P.2}

/-- **Deninger, Proposition 4.2.**  The subset cut out by an admissible class is forward and
backward invariant under the Frobenius operators. -/
theorem deningerCharPointsIn_frobenius_iff {N₀ : Submonoid ℕ} (E : DeningerAdmissibleClass C N₀)
    {ν : ℕ} (hν : ν ∈ N₀) (hν0 : 0 < ν) (P : DeningerCharPoints X C) :
    P ∈ deningerCharPointsIn E X ↔ deningerCharFrobenius ν P ∈ deningerCharPointsIn E X :=
  E.pow_iff P.2 hν hν0

/-- **Deninger, Proposition 4.2.**  The subset cut out by an admissible class is invariant under
every isomorphism of schemes; in particular under the Galois action. -/
theorem deningerCharPointsIn_map_iff {N₀ : Submonoid ℕ} (E : DeningerAdmissibleClass C N₀)
    (f : X ⟶ Y) [IsIso f] (P : DeningerCharPoints X C) :
    P ∈ deningerCharPointsIn E X ↔ deningerCharPointsMap f P ∈ deningerCharPointsIn E Y := by
  haveI : IsIso (f.residueFieldMap P.1) := inferInstance
  let e : Y.residueField (f.base P.1) ≅ X.residueField P.1 := asIso (f.residueFieldMap P.1)
  let σ : Y.residueField (f.base P.1) ≃+* X.residueField P.1 :=
    { toFun := e.hom.hom
      invFun := e.inv.hom
      left_inv := fun a => by simp
      right_inv := fun a => by simp
      map_mul' := map_mul _
      map_add' := map_add _ }
  exact E.comp_iff σ P.2

/-- **Deninger, Corollary 4.4.**  If the admissible class contains every injective character, the
projection to `X` is surjective, provided each residue field embeds multiplicatively into `C`. -/
theorem deningerCharPointsIn_fst_surjective {N₀ : Submonoid ℕ} (E : DeningerAdmissibleClass C N₀)
    [IsAlgClosed C] (hinj : ∀ {k : Type u} [Field k] (χ : kˣ →* Cˣ), Function.Injective χ →
      E.mem χ)
    (hne : ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ)
    (hcard : ∀ x : X, #(X.residueField x) ≤ #C)
    (hchar : ∀ x : X, ringChar C = 0 ∨ ringChar (X.residueField x) = ringChar C) (x : X) :
    ∃ P ∈ deningerCharPointsIn E X, P.1 = x := by
  obtain ⟨χ, hχ⟩ := deningerInjectiveCharacter_of_char (k := X.residueField x) (C := C) hne
    (by simpa using hcard x) (hchar x)
  exact ⟨⟨x, χ⟩, hinj χ hχ, rfl⟩

end RHTower
