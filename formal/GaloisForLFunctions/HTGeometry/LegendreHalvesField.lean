import GaloisForLFunctions.HTGeometry.LegendreHalfCoordinates
import GaloisForLFunctions.HTGeometry.QuadraticAdjoinSquareKernel

/-!
# The field of halves of a Legendre point

Let `F ⊆ Ω` be fields of characteristic zero and `P` a point of a Legendre curve over `F`.  Suppose
that over every intermediate field `E` the image of `P` has a half exactly when a fixed `c ∈ F`
becomes a square, and let `r ∈ Ω` with `r² = c`.  Then the coordinates of every half of `P` over `Ω`
lie in `F(r)`, and the coordinates of any single half generate `F(r)`.  Thus `F(r)` is the field of
halves of `P`; it has degree two over `F` when `c` is not a square.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.LegendreDoubling
open WeierstrassCurve.Affine
open scoped IntermediateField

local instance (priority := high) (X : Type*) : DecidableEq X := Classical.decEq X

section Comp
variable {A B C : Type*} [Field A] [Field B] [Field C] [CharZero A] [CharZero B] [CharZero C]

theorem pointMap_pointMap (f : A →+* B) (g : B →+* C) {lam : A} {mu : B} {nu : C}
    (hmu : f lam = mu) (hnu : g mu = nu) (P : (curve lam).Point) :
    pointMap g hnu (pointMap f hmu P) =
      pointMap (g.comp f) (by rw [RingHom.comp_apply, hmu, hnu]) P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

end Comp

variable {F Ω : Type*} [Field F] [Field Ω] [CharZero F] [CharZero Ω] [Algebra F Ω]

omit [CharZero F] [CharZero Ω] in
private theorem tower (E : IntermediateField F Ω) (z : F) :
    algebraMap E Ω (algebraMap F E z) = algebraMap F Ω z :=
  (IsScalarTower.algebraMap_apply F E Ω z).symm

/-- Points over an intermediate field, viewed over `Ω`. -/
private theorem pointMap_tower (E : IntermediateField F Ω) {lam : F} (P : (curve lam).Point) :
    pointMap (algebraMap E Ω) (tower E lam) (pointMap (algebraMap F E) rfl P) =
      pointMap (algebraMap F Ω) rfl P := by
  rw [pointMap_pointMap]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [pointMap_some, RingHom.comp_apply, tower]

variable {lam c : F} {P : (curve lam).Point} {r : Ω}

/-- A half over an intermediate field `E` exists exactly when `c` is a square in `E`. -/
def HalvingDecidedBy (P : (curve lam).Point) (c : F) : Prop :=
  ∀ E : IntermediateField F Ω, (∃ R : (curve (algebraMap F E lam)).Point,
    R + R = pointMap (algebraMap F E) rfl P) ↔ IsSquare (algebraMap F E c)

/-- Every half over `Ω` has its coordinates in `F(r)`. -/
theorem half_coordinates_mem_adjoin (hr : r * r = algebraMap F Ω c)
    (hcrit : HalvingDecidedBy (Ω := Ω) P c) {x y : Ω}
    {h : (curve (algebraMap F Ω lam)).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = pointMap (algebraMap F Ω) rfl P) :
    x ∈ F⟮r⟯ ∧ y ∈ F⟮r⟯ := by
  set E := F⟮r⟯
  obtain ⟨R₀, hR₀⟩ := (hcrit E).mpr ((adjoin_root_le_iff_isSquare hr E).mp le_rfl)
  rw [← pointMap_tower E P] at hR
  obtain ⟨hx, hy⟩ := half_coordinates_mem_range (algebraMap E Ω) (tower E lam) hR₀ hR
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  exact ⟨x'.2, y'.2⟩

/-- A field containing the coordinates of a half over `Ω` admits that half. -/
theorem has_half_of_coordinates (E : IntermediateField F Ω) {x y : Ω}
    {h : (curve (algebraMap F Ω lam)).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = pointMap (algebraMap F Ω) rfl P)
    (hx : x ∈ E) (hy : y ∈ E) :
    ∃ R : (curve (algebraMap F E lam)).Point, R + R = pointMap (algebraMap F E) rfl P := by
  obtain ⟨R, hR'⟩ := exists_pointMap_eq (algebraMap E Ω) (tower E lam) h ⟨⟨x, hx⟩, rfl⟩
    ⟨⟨y, hy⟩, rfl⟩
  refine ⟨R, pointMap_injective (algebraMap E Ω) (tower E lam) ?_⟩
  rw [pointMap_add, hR', hR, pointMap_tower]

/-- **Field of halves.**  The coordinates of any half of `P` over `Ω` generate `F(r)`. -/
theorem adjoin_half_coordinates (hr : r * r = algebraMap F Ω c)
    (hcrit : HalvingDecidedBy (Ω := Ω) P c) {x y : Ω}
    {h : (curve (algebraMap F Ω lam)).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = pointMap (algebraMap F Ω) rfl P) :
    IntermediateField.adjoin F ({x, y} : Set Ω) = F⟮r⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact half_coordinates_mem_adjoin hr hcrit hR
  · set E := IntermediateField.adjoin F ({x, y} : Set Ω)
    apply (adjoin_root_le_iff_isSquare hr E).mpr
    apply (hcrit E).mp
    exact has_half_of_coordinates E hR (IntermediateField.subset_adjoin _ _ (by simp))
      (IntermediateField.subset_adjoin _ _ (by simp))

/-- Over `Ω` the point has a half as soon as `c` has a root there. -/
theorem exists_half_closure (hr : r * r = algebraMap F Ω c)
    (hcrit : HalvingDecidedBy (Ω := Ω) P c) :
    ∃ R : (curve (algebraMap F Ω lam)).Point, R + R = pointMap (algebraMap F Ω) rfl P := by
  set E := F⟮r⟯
  obtain ⟨R₀, hR₀⟩ := (hcrit E).mpr ((adjoin_root_le_iff_isSquare hr E).mp le_rfl)
  refine ⟨pointMap (algebraMap E Ω) (tower E lam) R₀, ?_⟩
  rw [← pointMap_add, hR₀, pointMap_tower]

/-- For a smooth curve the point has exactly four halves over `Ω`. -/
theorem ncard_halves_closure (hl0 : lam ≠ 0) (hl1 : lam ≠ 1) (hr : r * r = algebraMap F Ω c)
    (hcrit : HalvingDecidedBy (Ω := Ω) P c) :
    {R : (curve (algebraMap F Ω lam)).Point |
      R + R = pointMap (algebraMap F Ω) rfl P}.ncard = 4 := by
  obtain ⟨R₀, hR₀⟩ := exists_half_closure hr hcrit
  exact ncard_halves ((map_ne_zero _).mpr hl0)
    (fun h => hl1 ((algebraMap F Ω).injective (by rw [h, map_one]))) hR₀

end GaloisForLFunctions.HTGeometry.LegendreDoubling
