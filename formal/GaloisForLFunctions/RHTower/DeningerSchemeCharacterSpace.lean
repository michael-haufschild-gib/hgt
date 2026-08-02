import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Data.Complex.Basic
import GaloisForLFunctions.RHTower.DeningerCharacterProjectionOpen

/-!
# The character space of an arithmetic scheme

A point of the character space of a scheme is a point of the scheme together with a character of
the multiplicative group of its residue field.  Forgetting the character is the arithmetic
projection, and pulling a character back along the residue field map makes the construction
functorial.

Along an open immersion the residue field map is an isomorphism, so the character space of an open
subscheme is exactly the part of the character space lying over that open: the induced map is
injective with image the preimage of the image of the immersion.  Giving the character space the
coarsest topology for which the projection is continuous, the induced map is an open embedding.

The Frobenius maps raise a character to a power.  They fix the underlying scheme point, so they
preserve the character space over every arithmetic open, and they compose multiplicatively.

* `DeningerCharacterSpace`, `deningerCharacterPr` : the space and the arithmetic projection.
* `deningerCharacterMap` : functoriality.
* `deningerCharacterMap_injective`, `deningerCharacterMap_range` : the character space of an open
  subscheme is the preimage of that open.
* `deningerCharacterMap_isOpenEmbedding` : it is an open embedding.
* `deningerCharacterFrobenius`, `_pr`, `_comp` : the Frobenius maps fix the scheme point and
  compose.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory Topology

universe u

/-- **The character space of a scheme.**  A point is a point of the scheme together with a
character of the multiplicative group of its residue field. -/
structure DeningerCharacterSpace (X : Scheme.{u}) : Type u where
  /-- The underlying scheme point. -/
  point : X
  /-- The character of the multiplicative group of the residue field at that point. -/
  char : (X.residueField point)ˣ →* ℂˣ

namespace DeningerCharacterSpace

variable {X Y : Scheme.{u}}

/-- **The arithmetic projection**, forgetting the character. -/
def deningerCharacterPr (p : DeningerCharacterSpace X) : X := p.point

@[simp]
theorem deningerCharacterPr_mk (x : X) (P : (X.residueField x)ˣ →* ℂˣ) :
    deningerCharacterPr (⟨x, P⟩ : DeningerCharacterSpace X) = x := rfl

/-- The map on residue field units induced by a scheme morphism. -/
noncomputable def deningerCharacterUnitsMap (f : X ⟶ Y) (x : X) :
    (Y.residueField (f x))ˣ →* (X.residueField x)ˣ :=
  Units.map (f.residueFieldMap x).hom.toMonoidHom

/-- **Functoriality.**  A scheme morphism carries a character of the residue field at a point to
the character obtained by pulling back along the residue field map. -/
noncomputable def deningerCharacterMap (f : X ⟶ Y) :
    DeningerCharacterSpace X → DeningerCharacterSpace Y :=
  fun p => ⟨f p.point, p.char.comp (deningerCharacterUnitsMap f p.point)⟩

@[simp]
theorem deningerCharacterMap_point (f : X ⟶ Y) (p : DeningerCharacterSpace X) :
    (deningerCharacterMap f p).point = f p.point := rfl

/-- The projection is natural. -/
theorem deningerCharacterPr_map (f : X ⟶ Y) (p : DeningerCharacterSpace X) :
    deningerCharacterPr (deningerCharacterMap f p) = f (deningerCharacterPr p) := rfl

section OpenImmersion

variable (f : X ⟶ Y) [IsOpenImmersion f]

/-- Along an open immersion the residue field map is an isomorphism, so the induced map on residue
field units is a group isomorphism. -/
noncomputable def deningerResidueUnitsEquiv (x : X) :
    (Y.residueField (f x))ˣ ≃* (X.residueField x)ˣ :=
  Units.mapEquiv (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.toMulEquiv

theorem deningerResidueUnitsEquiv_coe (x : X) :
    ⇑(deningerResidueUnitsEquiv f x) = deningerCharacterUnitsMap f x := rfl

theorem deningerCharacterUnitsMap_surjective (x : X) :
    Function.Surjective (deningerCharacterUnitsMap f x) := by
  rw [← deningerResidueUnitsEquiv_coe f]
  exact (deningerResidueUnitsEquiv f x).surjective

/-- **The character space of an open subscheme injects.** -/
theorem deningerCharacterMap_injective : Function.Injective (deningerCharacterMap f) := by
  intro p q h
  obtain ⟨x, P⟩ := p
  obtain ⟨y, Q⟩ := q
  have hbase : f x = f y := congrArg DeningerCharacterSpace.point h
  have hxy : x = y := (Scheme.Hom.isOpenEmbedding f).injective hbase
  subst hxy
  have hchar : P.comp (deningerCharacterUnitsMap f x) = Q.comp (deningerCharacterUnitsMap f x) :=
    eq_of_heq (DeningerCharacterSpace.mk.inj h).2
  have : P = Q := by
    refine MonoidHom.ext fun z => ?_
    obtain ⟨w, rfl⟩ := deningerCharacterUnitsMap_surjective f x z
    exact congrFun (congrArg (fun g : (Y.residueField (f x))ˣ →* ℂˣ => ⇑g) hchar) w
  rw [this]

/-- **The character space of an open subscheme is the part lying over that open.** -/
theorem deningerCharacterMap_range :
    Set.range (deningerCharacterMap f)
      = deningerCharacterOver (deningerCharacterPr (X := Y)) (Set.range f.base) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.point, rfl⟩
  · intro hq
    obtain ⟨y, Q⟩ := q
    obtain ⟨x, rfl⟩ := hq
    refine ⟨⟨x, Q.comp (deningerResidueUnitsEquiv f x).symm.toMonoidHom⟩, ?_⟩
    show (⟨f x, (Q.comp (deningerResidueUnitsEquiv f x).symm.toMonoidHom).comp
      (deningerCharacterUnitsMap f x)⟩ : DeningerCharacterSpace Y) = ⟨f x, Q⟩
    congr 1
    refine MonoidHom.ext fun z => ?_
    show Q ((deningerResidueUnitsEquiv f x).symm (deningerCharacterUnitsMap f x z)) = Q z
    rw [← deningerResidueUnitsEquiv_coe f, MulEquiv.symm_apply_apply]

end OpenImmersion

section Topology

variable (X)

/-- **The arithmetic topology**: the coarsest topology for which the arithmetic projection is
continuous. -/
instance instTopologicalSpace : TopologicalSpace (DeningerCharacterSpace X) :=
  TopologicalSpace.induced deningerCharacterPr inferInstance

variable {X}

theorem continuous_deningerCharacterPr :
    Continuous (deningerCharacterPr (X := X)) := continuous_induced_dom

/-- **The character space over an arithmetic open is open.** -/
theorem deningerCharacterSpaceOver_isOpen {U : Set X} (hU : IsOpen U) :
    IsOpen (deningerCharacterOver (deningerCharacterPr (X := X)) U) :=
  RHTower.deningerCharacterOver_isOpen continuous_deningerCharacterPr hU

theorem continuous_deningerCharacterMap (f : X ⟶ Y) :
    Continuous (deningerCharacterMap f) := by
  refine continuous_induced_rng.mpr ?_
  have : (deningerCharacterPr (X := Y)) ∘ deningerCharacterMap f
      = f.base ∘ deningerCharacterPr (X := X) := rfl
  rw [this]
  exact f.base.hom.continuous.comp continuous_deningerCharacterPr

variable (f : X ⟶ Y) [IsOpenImmersion f]

theorem deningerCharacterMap_isInducing : IsInducing (deningerCharacterMap f) := by
  constructor
  have hbase : (inferInstance : TopologicalSpace X)
      = TopologicalSpace.induced f.base inferInstance :=
    (Scheme.Hom.isOpenEmbedding f).isEmbedding.isInducing.eq_induced
  show TopologicalSpace.induced (deningerCharacterPr (X := X)) inferInstance
    = TopologicalSpace.induced (deningerCharacterMap f)
        (TopologicalSpace.induced (deningerCharacterPr (X := Y)) inferInstance)
  rw [induced_compose, hbase, induced_compose]
  rfl

/-- **Clause 2: the character space of an open subscheme is an open subspace.** -/
theorem deningerCharacterMap_isOpenEmbedding : IsOpenEmbedding (deningerCharacterMap f) := by
  refine ⟨⟨deningerCharacterMap_isInducing f, deningerCharacterMap_injective f⟩, ?_⟩
  rw [deningerCharacterMap_range f]
  exact deningerCharacterSpaceOver_isOpen (Scheme.Hom.isOpenEmbedding f).isOpen_range

end Topology

section Frobenius

/-- **The Frobenius maps.**  The `n`-th Frobenius raises a character to its `n`-th power and does
not move the underlying scheme point. -/
noncomputable def deningerCharacterFrobenius (n : ℕ) (p : DeningerCharacterSpace X) :
    DeningerCharacterSpace X :=
  ⟨p.point, (powMonoidHom n).comp p.char⟩

/-- **Equation `(7)`: Frobenius fixes the underlying scheme point.** -/
@[simp]
theorem deningerCharacterFrobenius_pr (n : ℕ) (p : DeningerCharacterSpace X) :
    deningerCharacterPr (deningerCharacterFrobenius n p) = deningerCharacterPr p := rfl

theorem deningerCharacterFrobenius_one (p : DeningerCharacterSpace X) :
    deningerCharacterFrobenius 1 p = p := by
  refine congrArg (fun Q => (⟨p.point, Q⟩ : DeningerCharacterSpace X)) ?_
  refine MonoidHom.ext fun z => ?_
  show (p.char z) ^ 1 = p.char z
  rw [pow_one]

theorem deningerCharacterFrobenius_comp (m n : ℕ) (p : DeningerCharacterSpace X) :
    deningerCharacterFrobenius m (deningerCharacterFrobenius n p)
      = deningerCharacterFrobenius (n * m) p := by
  refine congrArg (fun Q => (⟨p.point, Q⟩ : DeningerCharacterSpace X)) ?_
  refine MonoidHom.ext fun z => ?_
  show ((p.char z) ^ n) ^ m = (p.char z) ^ (n * m)
  rw [pow_mul]

theorem continuous_deningerCharacterFrobenius (n : ℕ) :
    Continuous (deningerCharacterFrobenius (X := X) n) := by
  refine continuous_induced_rng.mpr ?_
  have : (deningerCharacterPr (X := X)) ∘ deningerCharacterFrobenius n
      = deningerCharacterPr (X := X) := rfl
  rw [this]
  exact continuous_deningerCharacterPr

/-- **Frobenius stability of the character space over an arithmetic open.** -/
theorem deningerCharacterFrobenius_characterOver_mem (n : ℕ) (U : Set X)
    {p : DeningerCharacterSpace X}
    (hp : p ∈ deningerCharacterOver (deningerCharacterPr (X := X)) U) :
    deningerCharacterFrobenius n p ∈ deningerCharacterOver (deningerCharacterPr (X := X)) U :=
  deningerCharacterOver_map_mem (deningerCharacterFrobenius n)
    (deningerCharacterFrobenius_pr n) U hp

/-- Frobenius commutes with the functorial map, which is why the open embeddings commute with the
common Frobenius diagram. -/
theorem deningerCharacterMap_frobenius (f : X ⟶ Y) (n : ℕ) (p : DeningerCharacterSpace X) :
    deningerCharacterMap f (deningerCharacterFrobenius n p)
      = deningerCharacterFrobenius n (deningerCharacterMap f p) := rfl

end Frobenius

section ArithmeticOpen

variable (U : X.Opens)

/-- **Clause 1, Lemma 7.1.**  The character space of an arithmetic open is canonically the
character space over that open. -/
theorem deningerCharacterMap_range_opens :
    Set.range (deningerCharacterMap U.ι)
      = deningerCharacterOver (deningerCharacterPr (X := X)) (U : Set X) := by
  rw [deningerCharacterMap_range U.ι, U.range_ι]

/-- **Clause 1--2 for an arithmetic open**: the character space of the open subscheme is an open
subspace of the character space, with image the character space over that open. -/
theorem deningerCharacterMap_opens_isOpenEmbedding :
    IsOpenEmbedding (deningerCharacterMap U.ι) :=
  deningerCharacterMap_isOpenEmbedding U.ι

end ArithmeticOpen

end DeningerCharacterSpace

end RHTower


