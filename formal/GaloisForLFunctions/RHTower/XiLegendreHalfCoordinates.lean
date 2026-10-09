import GaloisForLFunctions.HTGeometry.LegendreHalfCoordinates
import GaloisForLFunctions.RHTower.XiLegendreJointHalvingFields

/-!
# Coordinates of all halves of the actual Xi Legendre sections

Over the algebraic closure of the infinite marked field each original section `P_n` and each
translated section `Q_n` has exactly four halves.  The coordinates of every half of `P_n` lie in
the common quadratic field `M(√ξ)`, and those of every half of `Q_n` in `M(√ξ, √λ_n)`; the
coordinates of any one half generate that field.  For a nonempty finite label set `T`, the
coordinates of all halves of the sections `Q_n`, `n ∈ T`, generate exactly the joint field of
degree `2^(|T|+1)`.  The two-torsion `{0, (0,0), (1,0), (λ_n,0)}` is rational, so the halves form
one coset defined over the minimal field.
-/

noncomputable section
open GaloisForLFunctions.HTGeometry WeierstrassCurve.Affine
open scoped IntermediateField
namespace RHTower.XiGlobalKummer
local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective
local instance (priority := high) (F : Type*) : DecidableEq F := Classical.decEq F

private theorem tower (E : IntermediateField Marked HalvingClosure) (z : Marked) :
    algebraMap E HalvingClosure (algebraMap Marked E z) = algebraMap Marked HalvingClosure z :=
  (IsScalarTower.algebraMap_apply Marked E HalvingClosure z).symm

/-- Points over an intermediate field, viewed over the algebraic closure. -/
def toClosure (E : IntermediateField Marked HalvingClosure) (n : ℕ) :
    (sourceCurveOver E n).Point → (sourceCurveOver HalvingClosure n).Point :=
  LegendreDoubling.pointMap (algebraMap E HalvingClosure) (tower E (1 + sourceParameter n))

theorem toClosure_injective (E : IntermediateField Marked HalvingClosure) (n : ℕ) :
    Function.Injective (toClosure E n) :=
  LegendreDoubling.pointMap_injective _ _

theorem toClosure_add (E : IntermediateField Marked HalvingClosure) (n : ℕ)
    (P Q : (sourceCurveOver E n).Point) :
    toClosure E n (P + Q) = toClosure E n P + toClosure E n Q :=
  LegendreDoubling.pointMap_add _ _ P Q

theorem toClosure_sourceSection (E : IntermediateField Marked HalvingClosure) (n : ℕ) :
    toClosure E n (sourceSectionOver E n) = sourceSectionOver HalvingClosure n := by
  unfold toClosure sourceSectionOver
  exact (Point.some.injEq ..).mpr ⟨tower E _, tower E _⟩

theorem toClosure_translatedSection (E : IntermediateField Marked HalvingClosure) (n : ℕ) :
    toClosure E n (translatedSectionOver E n) = translatedSectionOver HalvingClosure n := by
  unfold toClosure translatedSectionOver
  exact (Point.some.injEq ..).mpr ⟨tower E _, tower E _⟩

private theorem mem_of_mem_range (E : IntermediateField Marked HalvingClosure) {z : HalvingClosure}
    (hz : z ∈ (algebraMap E HalvingClosure).range) : z ∈ E := by
  obtain ⟨e, rfl⟩ := hz
  exact e.2

private theorem mem_range_of_mem (E : IntermediateField Marked HalvingClosure) {z : HalvingClosure}
    (hz : z ∈ E) : z ∈ (algebraMap E HalvingClosure).range :=
  ⟨⟨z, hz⟩, rfl⟩

/-- If a section has a half over `E`, all its halves over the closure have coordinates in `E`. -/
private theorem coordinates_mem (E : IntermediateField Marked HalvingClosure) (n : ℕ)
    {S : (sourceCurveOver E n).Point} {R₀ : (sourceCurveOver E n).Point} (hR₀ : R₀ + R₀ = S)
    {x y : HalvingClosure} {h : (sourceCurveOver HalvingClosure n).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = toClosure E n S) : x ∈ E ∧ y ∈ E := by
  obtain ⟨hx, hy⟩ := LegendreDoubling.half_coordinates_mem_range (algebraMap E HalvingClosure)
    (tower E (1 + sourceParameter n)) hR₀ hR
  exact ⟨mem_of_mem_range E hx, mem_of_mem_range E hy⟩

/-- A field containing the coordinates of a half over the closure admits that half. -/
private theorem has_half_of_coordinates (E : IntermediateField Marked HalvingClosure) (n : ℕ)
    {S : (sourceCurveOver E n).Point} {x y : HalvingClosure}
    {h : (sourceCurveOver HalvingClosure n).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = toClosure E n S) (hx : x ∈ E) (hy : y ∈ E) :
    ∃ R : (sourceCurveOver E n).Point, R + R = S := by
  obtain ⟨R, hR'⟩ := LegendreDoubling.exists_pointMap_eq (algebraMap E HalvingClosure)
    (tower E (1 + sourceParameter n)) h (mem_range_of_mem E hx) (mem_range_of_mem E hy)
  refine ⟨R, toClosure_injective E n ?_⟩
  have hRc : toClosure E n R = Point.some x y h := hR'
  rw [toClosure_add, ← hR, hRc]

private theorem lambdaClosure_ne_zero (n : ℕ) :
    algebraMap Marked HalvingClosure (1 + sourceParameter n) ≠ 0 :=
  (map_ne_zero _).mpr (sourceLambda_ne_zero n)

private theorem lambdaClosure_ne_one (n : ℕ) :
    algebraMap Marked HalvingClosure (1 + sourceParameter n) ≠ 1 := by
  intro he
  have h : 1 + sourceParameter n = 1 :=
    (algebraMap Marked HalvingClosure).injective (by simpa using he)
  exact sourceParameter_ne_zero n (by linear_combination h)

/-! ## Original sections -/

theorem sourceSection_has_half_closure (n : ℕ) :
    ∃ R : (sourceCurveOver HalvingClosure n).Point, R + R = sourceSectionOver HalvingClosure n :=
  (sourceSectionOver_has_half_iff HalvingClosure n).mpr ⟨commonHalfRoot, commonHalfRoot_sq.symm⟩

/-- Each original section has exactly four halves over the algebraic closure. -/
theorem sourceSection_ncard_halves (n : ℕ) :
    {R : (sourceCurveOver HalvingClosure n).Point |
      R + R = sourceSectionOver HalvingClosure n}.ncard = 4 := by
  obtain ⟨R₀, hR₀⟩ := sourceSection_has_half_closure n
  exact LegendreDoubling.ncard_halves (lambdaClosure_ne_zero n) (lambdaClosure_ne_one n) hR₀

/-- **All halves are defined over the common quadratic field.** -/
theorem sourceHalf_coordinates_mem (n : ℕ) {x y : HalvingClosure}
    {h : (sourceCurveOver HalvingClosure n).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = sourceSectionOver HalvingClosure n) :
    x ∈ commonHalvingField ∧ y ∈ commonHalvingField := by
  obtain ⟨R₀, hR₀⟩ := sourceSection_has_half_commonHalvingField n
  rw [← toClosure_sourceSection commonHalvingField n] at hR
  exact coordinates_mem commonHalvingField n hR₀ hR

/-- The coordinates of any half of an original section generate the common quadratic field. -/
theorem adjoin_sourceHalf_coordinates (n : ℕ) {x y : HalvingClosure}
    {h : (sourceCurveOver HalvingClosure n).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = sourceSectionOver HalvingClosure n) :
    IntermediateField.adjoin Marked ({x, y} : Set HalvingClosure) = commonHalvingField := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact sourceHalf_coordinates_mem n hR
  · set E := IntermediateField.adjoin Marked ({x, y} : Set HalvingClosure)
    apply (commonHalvingField_le_iff_has_half E n).mpr
    rw [← toClosure_sourceSection E n] at hR
    exact has_half_of_coordinates E n hR (IntermediateField.subset_adjoin _ _ (by simp))
      (IntermediateField.subset_adjoin _ _ (by simp))

/-! ## Translated sections -/

theorem translatedSection_has_half_closure (n : ℕ) :
    ∃ R : (sourceCurveOver HalvingClosure n).Point,
      R + R = translatedSectionOver HalvingClosure n :=
  (translatedSectionOver_has_half_iff HalvingClosure n).mpr
    ⟨⟨commonHalfRoot, commonHalfRoot_sq.symm⟩, ⟨labelledHalfRoot n, (labelledHalfRoot_sq n).symm⟩⟩

/-- Each translated section has exactly four halves over the algebraic closure. -/
theorem translatedSection_ncard_halves (n : ℕ) :
    {R : (sourceCurveOver HalvingClosure n).Point |
      R + R = translatedSectionOver HalvingClosure n}.ncard = 4 := by
  obtain ⟨R₀, hR₀⟩ := translatedSection_has_half_closure n
  exact LegendreDoubling.ncard_halves (lambdaClosure_ne_zero n) (lambdaClosure_ne_one n) hR₀

/-- **All halves of a translated section are defined over its biquadratic field.** -/
theorem translatedHalf_coordinates_mem (n : ℕ) {x y : HalvingClosure}
    {h : (sourceCurveOver HalvingClosure n).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = translatedSectionOver HalvingClosure n) :
    x ∈ translatedHalvingField n ∧ y ∈ translatedHalvingField n := by
  obtain ⟨R₀, hR₀⟩ := translatedSection_has_half_translatedHalvingField n
  rw [← toClosure_translatedSection (translatedHalvingField n) n] at hR
  exact coordinates_mem (translatedHalvingField n) n hR₀ hR

/-- The coordinates of any half of a translated section generate its biquadratic field. -/
theorem adjoin_translatedHalf_coordinates (n : ℕ) {x y : HalvingClosure}
    {h : (sourceCurveOver HalvingClosure n).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = translatedSectionOver HalvingClosure n) :
    IntermediateField.adjoin Marked ({x, y} : Set HalvingClosure) = translatedHalvingField n := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact translatedHalf_coordinates_mem n hR
  · set E := IntermediateField.adjoin Marked ({x, y} : Set HalvingClosure)
    apply (translatedHalvingField_le_iff_has_half E n).mpr
    rw [← toClosure_translatedSection E n] at hR
    exact has_half_of_coordinates E n hR (IntermediateField.subset_adjoin _ _ (by simp))
      (IntermediateField.subset_adjoin _ _ (by simp))

/-! ## Finite label sets -/

/-- Coordinates of all halves over the closure of the translated sections with labels in `T`. -/
def translatedHalfCoordinates (T : Finset ℕ) : Set HalvingClosure :=
  {z | ∃ n ∈ T, ∃ (x y : HalvingClosure) (h : (sourceCurveOver HalvingClosure n).Nonsingular x y),
    Point.some x y h + Point.some x y h = translatedSectionOver HalvingClosure n ∧ (z = x ∨ z = y)}

/-- Every half of every translated section with label in `T` is defined over the joint field. -/
theorem translatedHalfCoordinates_subset (T : Finset ℕ) :
    translatedHalfCoordinates T ⊆ jointHalvingField T := by
  rintro z ⟨n, hn, x, y, h, hR, hz⟩
  obtain ⟨R₀, hR₀⟩ := translatedSection_has_half_jointHalvingField T hn
  rw [← toClosure_translatedSection (jointHalvingField T) n] at hR
  obtain ⟨hx, hy⟩ := coordinates_mem (jointHalvingField T) n hR₀ hR
  rcases hz with rfl | rfl
  · exact hx
  · exact hy

/-- **The joint field is generated by the coordinates of all requested halves.**  For a nonempty
finite label set `T` it has degree `2^(|T|+1)` (`jointHalvingField_finrank`). -/
theorem adjoin_translatedHalfCoordinates (T : Finset ℕ) (hne : T.Nonempty) :
    IntermediateField.adjoin Marked (translatedHalfCoordinates T) = jointHalvingField T := by
  apply le_antisymm
  · exact (IntermediateField.adjoin_le_iff).mpr (translatedHalfCoordinates_subset T)
  · set E := IntermediateField.adjoin Marked (translatedHalfCoordinates T)
    apply (jointHalvingField_le_iff_has_halves T hne E).mpr
    intro n hn
    obtain ⟨R, hR⟩ := translatedSection_has_half_closure n
    rcases R with _ | ⟨x, y, h⟩
    · exact absurd hR.symm (Point.some_ne_zero _)
    have hx : x ∈ E := IntermediateField.subset_adjoin _ _ ⟨n, hn, x, y, h, hR, Or.inl rfl⟩
    have hy : y ∈ E := IntermediateField.subset_adjoin _ _ ⟨n, hn, x, y, h, hR, Or.inr rfl⟩
    rw [← toClosure_translatedSection E n] at hR
    exact has_half_of_coordinates E n hR hx hy

end RHTower.XiGlobalKummer
