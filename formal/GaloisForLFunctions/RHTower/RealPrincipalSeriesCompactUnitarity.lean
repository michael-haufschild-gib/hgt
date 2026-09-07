import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactHarishChandra
import GaloisForLFunctions.RHTower.RealSphericalComplementarySeries

/-!
# Complementary-series unitarity in the compact picture

The explicit complementary-series Hermitian form is transported to the finite normalized
compact-picture principal series.  Positivity and `e† = -f` invariance are proved in both
directions across the Fourier equivalence, giving the exact compact-picture unitarity locus
`(-1,1)` without assuming an exponent bound.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Pull back a complex Hermitian form along a complex-linear map in both variables. -/
def pullbackComplexHermitianForm {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (B : ComplexHermitianForm V) (e : W →ₗ[ℂ] V) :
    ComplexHermitianForm W :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun v w ↦ B (e v) (e w))
    (by intro; simp)
    (by intro; simp)
    (by intro; simp)
    (by intro; simp)

@[simp]
theorem pullbackComplexHermitianForm_apply {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (B : ComplexHermitianForm V) (e : W →ₗ[ℂ] V)
    (v w : W) : pullbackComplexHermitianForm B e v w = B (e v) (e w) :=
  rfl

/-- Complementary-series Hermitian form on finite compact-picture K-types. -/
def compactSphericalComplementaryHermitianForm (s : ℝ) :
    ComplexHermitianForm (normalizedRealCompactKFiniteSubmodule s) :=
  pullbackComplexHermitianForm (sphericalComplementaryHermitianForm s)
    (sphericalModelCompactKFiniteEquiv s).symm.toLinearMap

@[simp]
theorem compactSphericalComplementaryHermitianForm_apply (s : ℝ)
    (v w : normalizedRealCompactKFiniteSubmodule s) :
    compactSphericalComplementaryHermitianForm s v w =
      sphericalComplementaryHermitianForm s
        ((sphericalModelCompactKFiniteEquiv s).symm v)
        ((sphericalModelCompactKFiniteEquiv s).symm w) :=
  rfl

/-- Infinitesimal invariance relation on finite compact-picture K-types. -/
def IsCompactSphericalPrincipalInvariant (s : ℝ)
    (B : ComplexHermitianForm (normalizedRealCompactKFiniteSubmodule s)) : Prop :=
  ∀ v w,
    B (compactSphericalPrincipalE s v) w =
      -B v (compactSphericalPrincipalF s w)

theorem compactSphericalComplementaryHermitianForm_positiveDefinite
    (s : ℝ) (hs : |s| < 1) :
    IsPositiveDefiniteHermitian (compactSphericalComplementaryHermitianForm s) := by
  have hsource := sphericalComplementaryHermitianForm_positiveDefinite s hs
  constructor
  · constructor
    intro v w
    exact hsource.1.eq
      ((sphericalModelCompactKFiniteEquiv s).symm v)
      ((sphericalModelCompactKFiniteEquiv s).symm w)
  · intro v hv
    apply hsource.2
    exact (sphericalModelCompactKFiniteEquiv s).symm.map_ne_zero_iff.mpr hv

theorem compactSphericalComplementaryHermitianForm_invariant
    (s : ℝ) (hs : |s| < 1) :
    IsCompactSphericalPrincipalInvariant s
      (compactSphericalComplementaryHermitianForm s) := by
  intro v w
  rcases (sphericalModelCompactKFiniteEquiv s).surjective v with ⟨x, rfl⟩
  rcases (sphericalModelCompactKFiniteEquiv s).surjective w with ⟨y, rfl⟩
  simpa using sphericalComplementaryHermitianForm_invariant s hs x y

/-- Compact-picture parameters admitting a positive-definite infinitesimally invariant form. -/
def UnitarizableCompactSphericalPrincipalParameter : Set ℝ :=
  {s | ∃ B : ComplexHermitianForm (normalizedRealCompactKFiniteSubmodule s),
    IsPositiveDefiniteHermitian B ∧ IsCompactSphericalPrincipalInvariant s B}

theorem mem_unitarizableCompactSphericalPrincipalParameter
    (s : ℝ) (hs : |s| < 1) :
    s ∈ UnitarizableCompactSphericalPrincipalParameter := by
  exact ⟨compactSphericalComplementaryHermitianForm s,
    compactSphericalComplementaryHermitianForm_positiveDefinite s hs,
    compactSphericalComplementaryHermitianForm_invariant s hs⟩

theorem unitarizableCompactSphericalPrincipalParameter_subset :
    UnitarizableCompactSphericalPrincipalParameter ⊆ Set.Ioo (-1) 1 := by
  intro s hs
  obtain ⟨B, hpos, hinv⟩ := hs
  let Bsource : ComplexHermitianForm SphericalKFiniteModel :=
    pullbackComplexHermitianForm B
      (sphericalModelCompactKFiniteEquiv s).toLinearMap
  have hsourcePos : IsPositiveDefiniteHermitian Bsource := by
    constructor
    · constructor
      intro v w
      exact hpos.1.eq (sphericalModelCompactKFiniteEquiv s v)
        (sphericalModelCompactKFiniteEquiv s w)
    · intro v hv
      apply hpos.2
      exact (sphericalModelCompactKFiniteEquiv s).map_ne_zero_iff.mpr hv
  have hsourceInv : IsSphericalPrincipalInvariant s Bsource := by
    intro v w
    simpa [Bsource] using hinv
      (sphericalModelCompactKFiniteEquiv s v)
      (sphericalModelCompactKFiniteEquiv s w)
  exact unitarizableSphericalPrincipalParameter_subset
    ⟨Bsource, hsourcePos, hsourceInv⟩

/-- Exact unitarity locus in the finite normalized compact picture. -/
theorem unitarizableCompactSphericalPrincipalParameter_eq_Ioo :
    UnitarizableCompactSphericalPrincipalParameter = Set.Ioo (-1) 1 := by
  apply Set.Subset.antisymm
  · exact unitarizableCompactSphericalPrincipalParameter_subset
  · intro s hs
    exact mem_unitarizableCompactSphericalPrincipalParameter s (abs_lt.mpr hs)

end
end GaloisForLFunctions.RHTower
