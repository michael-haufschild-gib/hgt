import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity

/-!
# The coefficient sectors of the bi-anomaly

The bi-anomaly uses three coefficient sectors inside the ambient meromorphic field: the holomorphic
nowhere-vanishing one, the differentially algebraic one, and their intersection.

All three are multiplicative groups stable under translation, hence stable under the entrywise
group differential.  The holomorphic sector is the image of the units of the entire germ ring, and
translation acts on that ring by a ring isomorphism, so it carries units to units.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The holomorphic nowhere-vanishing sector: images of units of the entire germ ring. -/
def oSector : Set (meroField (Set.univ : Set ℂ)) :=
  {x | ∃ u : (analyticSubring (Set.univ : Set ℂ))ˣ,
    algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (u : analyticSubring (Set.univ : Set ℂ)) = x}

theorem oSector_one : (1 : meroField (Set.univ : Set ℂ)) ∈ oSector :=
  ⟨1, by rw [Units.val_one, map_one]⟩

theorem oSector_mul {x y : meroField (Set.univ : Set ℂ)} (hx : x ∈ oSector) (hy : y ∈ oSector) :
    x * y ∈ oSector := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  exact ⟨u * v, by rw [Units.val_mul, map_mul, hu, hv]⟩

theorem oSector_ne_zero {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ oSector) : x ≠ 0 := by
  obtain ⟨u, hu⟩ := hx
  intro h0
  rw [h0] at hu
  have hzero : (u : analyticSubring (Set.univ : Set ℂ)) = 0 :=
    (meroField_algebraMap_eq_zero_iff Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty _).mp hu
  have hunit : IsUnit (0 : analyticSubring (Set.univ : Set ℂ)) := by
    rw [← hzero]
    exact u.isUnit
  exact not_isUnit_zero hunit

theorem oSector_inv {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ oSector) : x⁻¹ ∈ oSector := by
  obtain ⟨u, hu⟩ := hx
  refine ⟨u⁻¹, ?_⟩
  have hmul : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      ((u⁻¹ : (analyticSubring (Set.univ : Set ℂ))ˣ) :
        analyticSubring (Set.univ : Set ℂ)) * x = 1 := by
    rw [← hu, ← map_mul]
    have hval : ((u⁻¹ : (analyticSubring (Set.univ : Set ℂ))ˣ) :
        analyticSubring (Set.univ : Set ℂ)) * (u : analyticSubring (Set.univ : Set ℂ)) = 1 :=
      u.inv_mul
    rw [hval, map_one]
  have hxne : x ≠ 0 := oSector_ne_zero ⟨u, hu⟩
  field_simp at hmul ⊢
  rw [hmul]

/-- **The holomorphic sector is translation stable.** -/
theorem oSector_addTranslationMeroEquiv (q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ oSector) : addTranslationMeroEquiv q x ∈ oSector := by
  obtain ⟨u, hu⟩ := hx
  refine ⟨Units.map (addTranslationAnalyticEquiv q).toMonoidHom u, ?_⟩
  rw [← hu]
  change algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (addTranslationAnalyticEquiv q (u : analyticSubring (Set.univ : Set ℂ))) = _
  rw [addTranslationMeroEquiv_algebraMap]

/-- **The holomorphic sector is stable under the shift quotient.** -/
theorem oSector_shiftQuotient (q : ℂ) {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ oSector) :
    shiftQuotient q x ∈ oSector := by
  rw [shiftQuotient, div_eq_mul_inv]
  exact oSector_mul (oSector_addTranslationMeroEquiv q hx) (oSector_inv hx)

/-- The intersection sector of the bi-anomaly: holomorphic, nowhere vanishing, and differentially
algebraic. -/
def aSector : Set (meroField (Set.univ : Set ℂ)) := oSector ∩ daSector

theorem aSector_mul {x y : meroField (Set.univ : Set ℂ)} (hx : x ∈ aSector) (hy : y ∈ aSector) :
    x * y ∈ aSector :=
  ⟨oSector_mul hx.1 hy.1, differentialAlgebraicOver_mul hx.2 hy.2⟩

theorem aSector_inv {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ aSector) : x⁻¹ ∈ aSector :=
  ⟨oSector_inv hx.1, differentialAlgebraicOver_inv hx.2⟩

/-- **The intersection sector is translation stable.** -/
theorem aSector_addTranslationMeroEquiv (q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ aSector) : addTranslationMeroEquiv q x ∈ aSector :=
  ⟨oSector_addTranslationMeroEquiv q hx.1, daSector_addTranslationMeroEquiv q hx.2⟩

/-- **The intersection sector is a subcomplex for the group differential.** -/
theorem aSector_shiftQuotient (q : ℂ) {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ aSector) :
    shiftQuotient q x ∈ aSector :=
  ⟨oSector_shiftQuotient q hx.1, daSector_shiftQuotient q hx.2⟩

/-- **The Koszul coboundary preserves the intersection sector.** -/
theorem aSector_koszulCoboundary (sigma tau : ℂ) {p : meroField (Set.univ : Set ℂ)
    × meroField (Set.univ : Set ℂ)} (h1 : p.1 ∈ aSector) (h2 : p.2 ∈ aSector) :
    koszulCoboundary sigma tau p ∈ aSector := by
  rw [koszulCoboundary, div_eq_mul_inv]
  exact aSector_mul (aSector_shiftQuotient tau h1) (aSector_inv (aSector_shiftQuotient sigma h2))

end

end GaloisForLFunctions.HTGeometry
