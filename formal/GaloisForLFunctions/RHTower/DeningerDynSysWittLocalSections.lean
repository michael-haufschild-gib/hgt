import GaloisForLFunctions.RHTower.DeningerDynSysBigWittSheaf

/-!
# The sections of `W_rat (𝒪_X)` inside `W (𝒪_X)`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 2.1.

The presheaf `U ↦ W_rat (𝒪_X (U))` is a subpresheaf of the sheaf `U ↦ W (𝒪_X (U))`.  Its
sheafification is therefore realized inside `W (𝒪_X)` as the subpresheaf of *locally rational*
big Witt vectors: those whose restriction to some neighbourhood of each point of `U` is a rational
Witt vector.  This module builds that subpresheaf, shows it is a subring, is stable under
restriction, satisfies the sheaf axiom, and is the **smallest** local subpresheaf of `W (𝒪_X)`
containing `W_rat (𝒪_X (·))` — which is exactly the universal property of the sheafification as a
subobject of `W (𝒪_X)`.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf

universe u

variable {X : TopCat.{u}}

/-- Naturality of the embedding `W_rat (A) ↪ W (A)`, phrased for the ring homomorphism
`W_rat (f)`. -/
theorem deningerCanonicalRationalWittEmbedding_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (v : DeningerCanonicalRationalWittRing A) :
    deningerCanonicalRationalWittEmbedding (deningerCanonicalRationalWittMap f v)
      = deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding v) :=
  deningerCanonicalRationalWittEmbedding_mapFun f v

/-- The image of `W_rat (𝒪 (V))` in `W (𝒪 (V))`, as a subring. -/
noncomputable def deningerWittRationalRange (F : TopCat.Presheaf CommRingCat.{u} X)
    (V : Opens X) : Subring (DeningerBigWittRing (F.obj (op V))) :=
  (deningerCanonicalRationalWittEmbedding (A := F.obj (op V))).range

theorem deningerWittRationalRange_mem {F : TopCat.Presheaf CommRingCat.{u} X} {V : Opens X}
    {w : DeningerBigWittRing (F.obj (op V))} :
    w ∈ deningerWittRationalRange F V
      ↔ ∃ v : DeningerCanonicalRationalWittRing (F.obj (op V)),
          deningerCanonicalRationalWittEmbedding v = w :=
  Iff.rfl

/-- Composing two restrictions of the big Witt presheaf. -/
theorem deningerBigWittRing_res_trans (F : TopCat.Presheaf CommRingCat.{u} X)
    {W V U : Opens X} (hWV : W ≤ V) (hVU : V ≤ U) (w : DeningerBigWittRing (F.obj (op U))) :
    deningerBigWittRingMap (F.map (homOfLE hWV).op).hom
        (deningerBigWittRingMap (F.map (homOfLE hVU).op).hom w)
      = deningerBigWittRingMap (F.map (homOfLE (hWV.trans hVU)).op).hom w := by
  rw [← deningerBigWittRingMap_comp]
  congr 1
  rw [← CommRingCat.hom_comp, ← F.map_comp]
  rfl

/-- The rational image is carried into the rational image by restriction. -/
theorem deningerWittRationalRange_res (F : TopCat.Presheaf CommRingCat.{u} X)
    {V W : Opens X} (h : W ≤ V) {w : DeningerBigWittRing (F.obj (op V))}
    (hw : w ∈ deningerWittRationalRange F V) :
    deningerBigWittRingMap (F.map (homOfLE h).op).hom w ∈ deningerWittRationalRange F W := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨deningerCanonicalRationalWittMap (F.map (homOfLE h).op).hom v,
    deningerCanonicalRationalWittEmbedding_mapFun _ _⟩

/-- **Deninger, Proposition 2.1.**  A big Witt vector over `𝒪 (U)` is *locally rational* when every
point of `U` has a neighbourhood inside `U` on which it restricts to a rational Witt vector. -/
def DeningerWittLocallyRational (F : TopCat.Presheaf CommRingCat.{u} X) (U : Opens X)
    (w : DeningerBigWittRing (F.obj (op U))) : Prop :=
  ∀ x ∈ U, ∃ V : Opens X, ∃ h : V ≤ U, x ∈ V ∧
    deningerBigWittRingMap (F.map (homOfLE h).op).hom w ∈ deningerWittRationalRange F V

theorem deningerWittLocallyRational_iff (F : TopCat.Presheaf CommRingCat.{u} X) (U : Opens X)
    (w : DeningerBigWittRing (F.obj (op U))) :
    DeningerWittLocallyRational F U w
      ↔ ∀ x ∈ U, ∃ V : Opens X, ∃ h : V ≤ U, x ∈ V ∧
          ∃ v : DeningerCanonicalRationalWittRing (F.obj (op V)),
            deningerCanonicalRationalWittEmbedding v
              = deningerBigWittRingMap (F.map (homOfLE h).op).hom w :=
  Iff.rfl

/-- A rational Witt vector over `𝒪 (U)` is locally rational. -/
theorem deningerWittLocallyRational_of_range {F : TopCat.Presheaf CommRingCat.{u} X}
    {U : Opens X} {w : DeningerBigWittRing (F.obj (op U))}
    (hw : w ∈ deningerWittRationalRange F U) : DeningerWittLocallyRational F U w :=
  fun _ hx => ⟨U, le_refl U, hx, by
    obtain ⟨v, rfl⟩ := hw
    exact ⟨deningerCanonicalRationalWittMap (F.map (homOfLE (le_refl U)).op).hom v,
      deningerCanonicalRationalWittEmbedding_mapFun _ _⟩⟩

/-- The locally rational big Witt vectors form a subring. -/
noncomputable def deningerWittLocallyRationalSubring (F : TopCat.Presheaf CommRingCat.{u} X)
    (U : Opens X) : Subring (DeningerBigWittRing (F.obj (op U))) where
  carrier := {w | DeningerWittLocallyRational F U w}
  zero_mem' := deningerWittLocallyRational_of_range (Subring.zero_mem _)
  one_mem' := deningerWittLocallyRational_of_range (Subring.one_mem _)
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨V₁, h₁, hx₁, hv₁⟩ := ha x hx
    obtain ⟨V₂, h₂, hx₂, hv₂⟩ := hb x hx
    refine ⟨V₁ ⊓ V₂, le_trans inf_le_left h₁, ⟨hx₁, hx₂⟩, ?_⟩
    rw [map_add]
    refine Subring.add_mem _ ?_ ?_
    · rw [← deningerBigWittRing_res_trans F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) h₁]
      exact deningerWittRationalRange_res F _ hv₁
    · rw [← deningerBigWittRing_res_trans F (inf_le_right : V₁ ⊓ V₂ ≤ V₂) h₂]
      exact deningerWittRationalRange_res F _ hv₂
  mul_mem' := by
    intro a b ha hb x hx
    obtain ⟨V₁, h₁, hx₁, hv₁⟩ := ha x hx
    obtain ⟨V₂, h₂, hx₂, hv₂⟩ := hb x hx
    refine ⟨V₁ ⊓ V₂, le_trans inf_le_left h₁, ⟨hx₁, hx₂⟩, ?_⟩
    rw [map_mul]
    refine Subring.mul_mem _ ?_ ?_
    · rw [← deningerBigWittRing_res_trans F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) h₁]
      exact deningerWittRationalRange_res F _ hv₁
    · rw [← deningerBigWittRing_res_trans F (inf_le_right : V₁ ⊓ V₂ ≤ V₂) h₂]
      exact deningerWittRationalRange_res F _ hv₂
  neg_mem' := by
    intro a ha x hx
    obtain ⟨V, h, hxV, hv⟩ := ha x hx
    exact ⟨V, h, hxV, by rw [map_neg]; exact Subring.neg_mem _ hv⟩

@[simp] theorem deningerWittLocallyRationalSubring_mem
    {F : TopCat.Presheaf CommRingCat.{u} X} {U : Opens X}
    {w : DeningerBigWittRing (F.obj (op U))} :
    w ∈ deningerWittLocallyRationalSubring F U ↔ DeningerWittLocallyRational F U w := Iff.rfl

/-- Local rationality is stable under restriction. -/
theorem deningerWittLocallyRational_res (F : TopCat.Presheaf CommRingCat.{u} X)
    {U V : Opens X} (h : V ≤ U) {w : DeningerBigWittRing (F.obj (op U))}
    (hw : DeningerWittLocallyRational F U w) :
    DeningerWittLocallyRational F V (deningerBigWittRingMap (F.map (homOfLE h).op).hom w) := by
  intro x hx
  obtain ⟨V₁, h₁, hx₁, hv₁⟩ := hw x (h hx)
  refine ⟨V₁ ⊓ V, le_trans inf_le_right (le_refl V), ⟨hx₁, hx⟩, ?_⟩
  rw [deningerBigWittRing_res_trans F (inf_le_right : V₁ ⊓ V ≤ V) h,
    ← deningerBigWittRing_res_trans F (inf_le_left : V₁ ⊓ V ≤ V₁) h₁]
  exact deningerWittRationalRange_res F _ hv₁

/-- **Local rationality is a local condition**, hence the corresponding subpresheaf of the sheaf
`W (𝒪_X)` is a sheaf. -/
theorem deningerWittLocallyRational_of_cover (F : TopCat.Presheaf CommRingCat.{u} X)
    {U : Opens X} {ι : Type*} {V : ι → Opens X} (hV : ∀ i, V i ≤ U)
    (hcov : ∀ x ∈ U, ∃ i, x ∈ V i) {w : DeningerBigWittRing (F.obj (op U))}
    (h : ∀ i, DeningerWittLocallyRational F (V i)
      (deningerBigWittRingMap (F.map (homOfLE (hV i)).op).hom w)) :
    DeningerWittLocallyRational F U w := by
  intro x hx
  obtain ⟨i, hxi⟩ := hcov x hx
  obtain ⟨W, hWV, hxW, hw⟩ := h i x hxi
  refine ⟨W, hWV.trans (hV i), hxW, ?_⟩
  rw [← deningerBigWittRing_res_trans F hWV (hV i)]
  exact hw

/-- **The universal property of `W_rat (𝒪_X)` as a subsheaf of `W (𝒪_X)`.**  Every local
subpresheaf of `W (𝒪_X)` containing the rational Witt vectors contains all locally rational
vectors. -/
theorem deningerWittLocallyRational_le (F : TopCat.Presheaf CommRingCat.{u} X)
    (P : ∀ V : Opens X, Set (DeningerBigWittRing (F.obj (op V))))
    (hrat : ∀ (V : Opens X) (v : DeningerCanonicalRationalWittRing (F.obj (op V))),
      deningerCanonicalRationalWittEmbedding v ∈ P V)
    (hloc : ∀ (U : Opens X) (w : DeningerBigWittRing (F.obj (op U))),
      (∀ x ∈ U, ∃ V : Opens X, ∃ h : V ≤ U, x ∈ V ∧
        deningerBigWittRingMap (F.map (homOfLE h).op).hom w ∈ P V) → w ∈ P U)
    {U : Opens X} {w : DeningerBigWittRing (F.obj (op U))}
    (hw : DeningerWittLocallyRational F U w) : w ∈ P U := by
  refine hloc U w fun x hx => ?_
  obtain ⟨V, h, hxV, v, hv⟩ := hw x hx
  exact ⟨V, h, hxV, hv ▸ hrat V v⟩

end RHTower
