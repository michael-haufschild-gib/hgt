import GaloisForLFunctions.HTGeometry.StokesCellularMicrolocalSheaf

/-!
# Cellular Stokes categories and vanishing-cycle functors

This module constructs the local cellular Stokes category as rational linear cospans.  Its two
microlocalization functors are quotient functors, not numerical proxies: a morphism of cospans
induces the quotient map by naturality.  The quotient projection gives an exact
arc-to-wall-to-vanishing sequence.

For a positive exponential degree, the global boundary category is the representation category
of the cyclic bipartite incidence quiver of arcs and walls.  The quiver has no composable pair of
arrows, so its path category contains only identities and incidence arrows.  The alternating
exponential object is constructed in this category and its cellular Euler form is computed.
-/

open scoped BigOperators

open CategoryTheory
open CategoryTheory.Limits

namespace GaloisForLFunctions
namespace IrregularStokes
namespace CellularStokesCategory

noncomputable section

open CellularMicrolocal

/-- Abelian category of rational cellular sheaves on a one-wall germ. -/
abbrev GermCategory := WalkingCospan ⥤ ModuleCat ℚ

/-- Cellular exponential germ.  Its adjacent arc maps are complementary inclusions into the wall
stalk. -/
noncomputable def exponentialGerm (d : ℕ) (active : Bool) : GermCategory :=
  cospan (ModuleCat.ofHom (restriction d active))
    (ModuleCat.ofHom (restriction d (!active)))

/-- Source stalk selected by a conormal side. -/
def sideObject (F : GermCategory) : ConormalSide → ModuleCat ℚ
  | .left => F.obj WalkingCospan.left
  | .right => F.obj WalkingCospan.right

/-- Incidence map selected by a conormal side. -/
def sideMap (F : GermCategory) : (s : ConormalSide) →
    sideObject F s ⟶ F.obj WalkingCospan.one
  | .left => F.map WalkingCospan.Hom.inl
  | .right => F.map WalkingCospan.Hom.inr

/-- Cellular microstalk/vanishing-cycle space of a germ in a chosen conormal direction. -/
abbrev microstalkSpace (F : GermCategory) (s : ConormalSide) :=
  F.obj WalkingCospan.one ⧸ (sideMap F s).hom.range

/-- Component of a natural transformation on the source stalk selected by a side. -/
def sideComponent {F G : GermCategory} (α : F ⟶ G) :
    (s : ConormalSide) → sideObject F s ⟶ sideObject G s
  | .left => α.app WalkingCospan.left
  | .right => α.app WalkingCospan.right

/-- Naturality sends the image of an incidence map into the image of the target incidence map. -/
theorem sideMap_range_le {F G : GermCategory} (α : F ⟶ G) (s : ConormalSide) :
    (sideMap F s).hom.range ≤
      Submodule.comap (α.app WalkingCospan.one).hom (sideMap G s).hom.range := by
  cases s with
  | left =>
      rintro _ ⟨x, rfl⟩
      refine ⟨(α.app WalkingCospan.left).hom x, ?_⟩
      have h := α.naturality WalkingCospan.Hom.inl
      change (G.map WalkingCospan.Hom.inl).hom ((α.app WalkingCospan.left).hom x) =
        (α.app WalkingCospan.one).hom ((F.map WalkingCospan.Hom.inl).hom x)
      simpa using (congrArg (fun f => f.hom x) h).symm
  | right =>
      rintro _ ⟨x, rfl⟩
      refine ⟨(α.app WalkingCospan.right).hom x, ?_⟩
      have h := α.naturality WalkingCospan.Hom.inr
      change (G.map WalkingCospan.Hom.inr).hom ((α.app WalkingCospan.right).hom x) =
        (α.app WalkingCospan.one).hom ((F.map WalkingCospan.Hom.inr).hom x)
      simpa using (congrArg (fun f => f.hom x) h).symm

/-- Map induced on microlocal quotient spaces by a morphism of cellular sheaves. -/
noncomputable def inducedMicrostalkMap {F G : GermCategory} (α : F ⟶ G)
    (s : ConormalSide) : microstalkSpace F s →ₗ[ℚ] microstalkSpace G s :=
  (sideMap F s).hom.range.mapQ (sideMap G s).hom.range
    (α.app WalkingCospan.one).hom (sideMap_range_le α s)

/-- Microlocalization is a functor from cellular Stokes germs to rational modules. -/
noncomputable def microstalkFunctor (s : ConormalSide) : GermCategory ⥤ ModuleCat ℚ where
  obj F := ModuleCat.of ℚ (microstalkSpace F s)
  map α := ModuleCat.ofHom (inducedMicrostalkMap α s)
  map_id F := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro y
    rfl
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro y
    rfl

/-- Nearby cycles in the cellular germ are the wall stalk. -/
def nearbyCycleFunctor : GermCategory ⥤ ModuleCat ℚ where
  obj F := F.obj WalkingCospan.one
  map α := α.app WalkingCospan.one
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Canonical projection from nearby cycles to directed vanishing cycles. -/
def nearbyToVanishing (F : GermCategory) (s : ConormalSide) :
    F.obj WalkingCospan.one →ₗ[ℚ] microstalkSpace F s :=
  (sideMap F s).hom.range.mkQ

/-- Incidence image is exactly the kernel of the nearby-to-vanishing projection. -/
theorem arc_wall_vanishing_exact (F : GermCategory) (s : ConormalSide) :
    Function.Exact (sideMap F s).hom (nearbyToVanishing F s) := by
  rw [LinearMap.exact_iff]
  exact Submodule.ker_mkQ _

/-- Nearby-to-vanishing projection is onto. -/
theorem nearbyToVanishing_surjective (F : GermCategory) (s : ConormalSide) :
    Function.Surjective (nearbyToVanishing F s) :=
  Submodule.mkQ_surjective _

/-- Left directed vanishing cycles of the exponential germ are the previously computed
cellular microstalk. -/
theorem exponentialGerm_left_microstalk (d : ℕ) (active : Bool) :
    microstalkSpace (exponentialGerm d active) .left = microstalk d active := rfl

/-- Right directed vanishing cycles use the complementary adjacent arc. -/
theorem exponentialGerm_right_microstalk (d : ℕ) (active : Bool) :
    microstalkSpace (exponentialGerm d active) .right = microstalk d (!active) := rfl

theorem exponentialGerm_left_finrank (d : ℕ) (active : Bool) :
    Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .left) =
      if active then 0 else d :=
  finrank_microstalk d active

theorem exponentialGerm_right_finrank (d : ℕ) (active : Bool) :
    Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .right) =
      if active then d else 0 := by
  change Module.finrank ℚ (microstalk d (!active)) = if active then d else 0
  cases active with
  | false => exact finrank_microstalk d (!false)
  | true => exact finrank_microstalk d (!true)

/-- A positive-rank exponential germ has exactly one nonzero oriented vanishing cycle. -/
theorem exponentialGerm_exactly_one_vanishing {d : ℕ} (hd : 0 < d) (active : Bool) :
    (Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .left) = d ∧
        Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .right) = 0) ∨
      (Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .left) = 0 ∧
        Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .right) = d) := by
  cases active <;>
    simp [exponentialGerm_left_finrank, exponentialGerm_right_finrank, Nat.ne_of_gt hd]

/-- Finrank of an active/inactive arc stalk. -/
theorem finrank_arcStalk (d : ℕ) (active : Bool) :
    Module.finrank ℚ (arcStalk d active) = if active then d else 0 := by
  cases active with
  | false =>
      change Module.finrank ℚ (⊥ : Submodule ℚ (Fiber d)) = 0
      exact finrank_bot ℚ _
  | true =>
      change Module.finrank ℚ (⊤ : Submodule ℚ (Fiber d)) = d
      rw [finrank_top]
      simp [Fiber]

/-! ## Global cyclic incidence category -/

/-- Cyclic successor on the `Fin k` factor. -/
def succFin {k : ℕ} (hk : 0 < k) (a : Fin k) : Fin k :=
  ⟨(a.val + 1) % k, Nat.mod_lt _ hk⟩

/-- Cyclic successor on the `2k` walls, ordered by the Boolean half-step. -/
def nextWall {k : ℕ} (hk : 0 < k) : StokesWall k → StokesWall k
  | (a, false) => (a, true)
  | (a, true) => (succFin hk a, false)

/-- Cells of the cyclic Stokes stratification. -/
inductive BoundaryCell (k : ℕ)
  | arc : StokesWall k → BoundaryCell k
  | wall : StokesWall k → BoundaryCell k

/-- Incidence arrows from each arc to its initial and terminal walls. -/
inductive BoundaryArrow (k : ℕ) (hk : 0 < k) : BoundaryCell k → BoundaryCell k → Type
  | initial (w : StokesWall k) : BoundaryArrow k hk (.arc w) (.wall w)
  | terminal (w : StokesWall k) : BoundaryArrow k hk (.arc w) (.wall (nextWall hk w))

/-- Type synonym retaining the positivity witness in the quiver type. -/
def BoundaryQuiver (k : ℕ) (_hk : 0 < k) := BoundaryCell k

instance (k : ℕ) (hk : 0 < k) : Quiver (BoundaryQuiver k hk) where
  Hom := BoundaryArrow k hk

/-- Entrance-path category of the cyclic cellular stratification. -/
abbrev BoundaryPath (k : ℕ) (hk : 0 < k) := CategoryTheory.Paths (BoundaryQuiver k hk)

/-- Global cellular Stokes category on a degree-`k` boundary circle. -/
abbrev BoundaryCategory (k : ℕ) (hk : 0 < k) := BoundaryPath k hk ⥤ ModuleCat ℚ

/-- Its abelian structure follows from the abelian target module category. -/
@[reducible] noncomputable def boundaryCategoryAbelian (k : ℕ) (hk : 0 < k) :
    Abelian (BoundaryCategory k hk) := inferInstance

/-- No two nonidentity incidence arrows compose. -/
theorem no_two_step {k : ℕ} {hk : 0 < k} {X Y Z : BoundaryCell k}
    (f : BoundaryArrow k hk X Y) (g : BoundaryArrow k hk Y Z) : False := by
  cases f <;> cases g

/-- The entrance path category has no hidden paths of length greater than one. -/
theorem path_length_le_one {k : ℕ} {hk : 0 < k}
    {X Y : BoundaryQuiver k hk}
    (p : @Quiver.Path (BoundaryQuiver k hk)
      (inferInstance : Quiver (BoundaryQuiver k hk)) X Y) : p.length ≤ 1 := by
  cases p with
  | nil => simp
  | cons p f =>
      cases p with
      | nil => simp
      | cons q g => exact False.elim (no_two_step g f)

/-- Quiver representation underlying the global exponential boundary object. -/
def boundaryPrefunctor (k d : ℕ) (hk : 0 < k) : BoundaryQuiver k hk ⥤q ModuleCat ℚ where
  obj
    | .arc w => ModuleCat.of ℚ (arcStalk d w.2)
    | .wall _ => ModuleCat.of ℚ (Fiber d)
  map := by
    intro X Y f
    change BoundaryArrow k hk X Y at f
    cases f with
    | initial w => exact ModuleCat.ofHom (restriction d w.2)
    | terminal w => exact ModuleCat.ofHom (restriction d w.2)

/-- Alternating exponential sheaf on the cyclic Stokes boundary. -/
noncomputable def exponentialBoundary (k d : ℕ) (hk : 0 < k) : BoundaryCategory k hk :=
  CategoryTheory.Paths.lift (boundaryPrefunctor k d hk)

@[simp]
theorem exponentialBoundary_map_initial (k d : ℕ) (hk : 0 < k) (w : StokesWall k) :
    (exponentialBoundary k d hk).map
      (Quiver.Hom.toPath (BoundaryArrow.initial w)) =
      ModuleCat.ofHom (restriction d w.2) := by
  simp [exponentialBoundary, boundaryPrefunctor]

@[simp]
theorem exponentialBoundary_map_terminal (k d : ℕ) (hk : 0 < k) (w : StokesWall k) :
    (exponentialBoundary k d hk).map
      (Quiver.Hom.toPath (BoundaryArrow.terminal w)) =
      ModuleCat.ofHom (restriction d w.2) := by
  simp [exponentialBoundary, boundaryPrefunctor]

/-- Euler form of a cyclic incidence-quiver dimension vector. -/
def boundaryEuler (k : ℕ) (hk : 0 < k)
    (wallDim arcDim : StokesWall k → ℕ) : ℤ :=
  (∑ w, (wallDim w : ℤ) ^ 2) + (∑ w, (arcDim w : ℤ) ^ 2) -
    (∑ w, (arcDim w : ℤ) * wallDim w) -
    (∑ w, (arcDim w : ℤ) * wallDim (nextWall hk w))

def exponentialWallDim (d : ℕ) (_w : StokesWall k) : ℕ := d

def exponentialArcDim (d : ℕ) (w : StokesWall k) : ℕ := if w.2 then d else 0

/-- Exactly half of the `2k` arc stalks are active. -/
theorem exponentialArcDim_sum (k d : ℕ) :
    (∑ w : StokesWall k, exponentialArcDim d w) = k * d := by
  rw [Fintype.sum_prod_type]
  simp [exponentialArcDim]

/-- Cellular Euler form of the alternating exponential object is the positive local channel
`k d^2`. -/
theorem exponential_boundaryEuler (k d : ℕ) (hk : 0 < k) :
    boundaryEuler k hk (exponentialWallDim d) (exponentialArcDim d) =
      (k : ℤ) * d ^ 2 := by
  have hw : (∑ w : StokesWall k, ((exponentialWallDim d w : ℕ) : ℤ) ^ 2) =
      2 * (k : ℤ) * d ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp [exponentialWallDim]
    ring
  have ha2 : (∑ w : StokesWall k, ((exponentialArcDim d w : ℕ) : ℤ) ^ 2) =
      (k : ℤ) * d ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp [exponentialArcDim]
  have hal : (∑ w : StokesWall k,
      ((exponentialArcDim d w : ℕ) : ℤ) * exponentialWallDim d w) =
      (k : ℤ) * d ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp [exponentialArcDim, exponentialWallDim]
    exact Or.inl (pow_two (d : ℤ)).symm
  have har : (∑ w : StokesWall k,
      ((exponentialArcDim d w : ℕ) : ℤ) * exponentialWallDim d (nextWall hk w)) =
      (k : ℤ) * d ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp [exponentialArcDim, exponentialWallDim]
    exact Or.inl (pow_two (d : ℤ)).symm
  simp only [boundaryEuler]
  rw [hw, ha2, hal, har]
  ring

end
end CellularStokesCategory
end IrregularStokes
end GaloisForLFunctions
