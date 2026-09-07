import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactKAction

/-!
# Finite K-types inside algebraic coinduction

Finite even Fourier expansion is extended through Iwasawa decomposition, giving an injective map
from the explicit spherical Harish-Chandra model into normalized algebraic coinduction.  The basis
functions are written explicitly and the embedding is proved to intertwine the actual restricted
right-translation action of `K`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Normalized algebraically coinduced principal-series function space with parameter `s`. -/
abbrev normalizedRealPrincipalSeriesSpace (s : ℝ) :=
  Representation.coindV realUpperBorel.subtype
    (realUpperBorelExponentRepresentation (s + 1))

/-- Injective Iwasawa extension of finite spherical K-types into normalized algebraic coinduction. -/
def normalizedRealPrincipalSeriesKFiniteEmbedding (s : ℝ) :
    SphericalKFiniteModel →ₗ[ℂ] normalizedRealPrincipalSeriesSpace s :=
  (algebraicRealPrincipalSeriesCompactPicture (s + 1)).symm.toLinearMap.comp
    (realCompactKFiniteEmbedding (s + 1))

theorem normalizedRealPrincipalSeriesKFiniteEmbedding_injective (s : ℝ) :
    Function.Injective (normalizedRealPrincipalSeriesKFiniteEmbedding s) :=
  (algebraicRealPrincipalSeriesCompactPicture (s + 1)).symm.injective.comp
    (realCompactKFiniteEmbedding_injective (s + 1))

/-- Explicit Iwasawa formula for a basis K-type in algebraic coinduction. -/
@[simp]
theorem normalizedRealPrincipalSeriesKFiniteEmbedding_single_apply
    (s : ℝ) (m : ℤ) (z : ℂ) (g : SL2R) :
    (normalizedRealPrincipalSeriesKFiniteEmbedding s (Finsupp.single m z)).1 g =
      realUpperBorelRpowCharacter (s + 1) (realIwasawaB g) *
        (z * realSphericalKTypeCharacter m (realIwasawaK g)) := by
  change (realCompactPictureExtend (s + 1)
    (realCompactKFiniteEmbedding (s + 1) (Finsupp.single m z))).1 g = _
  rw [realCompactKFiniteEmbedding_single]
  rfl

/-- The coinduced finite-K-type embedding intertwines diagonal K-types with right translation. -/
theorem normalizedRealPrincipalSeriesKFiniteEmbedding_intertwines_K
    (s : ℝ) (q : upperHalfPlaneStabilizer) :
    (normalizedRealPrincipalSeriesKFiniteEmbedding s).comp
        (sphericalKTypeRepresentation q) =
      ((algebraicRealPrincipalSeries (s + 1)) (q : SL2R)).comp
        (normalizedRealPrincipalSeriesKFiniteEmbedding s) := by
  apply LinearMap.ext
  intro v
  apply (algebraicRealPrincipalSeriesCompactPicture (s + 1)).injective
  simp only [LinearMap.comp_apply]
  rw [show (algebraicRealPrincipalSeriesCompactPicture (s + 1))
      (normalizedRealPrincipalSeriesKFiniteEmbedding s
        (sphericalKTypeRepresentation q v)) =
      realCompactKFiniteEmbedding (s + 1) (sphericalKTypeRepresentation q v) by
    simp [normalizedRealPrincipalSeriesKFiniteEmbedding]]
  change realCompactKFiniteEmbedding (s + 1) (sphericalKTypeRepresentation q v) =
    realPrincipalSeriesRestrictToK (s + 1)
      ((algebraicRealPrincipalSeries (s + 1)) (q : SL2R)
        (normalizedRealPrincipalSeriesKFiniteEmbedding s v))
  rw [realPrincipalSeriesRestrictToK_intertwines]
  rw [show realPrincipalSeriesRestrictToK (s + 1)
      (normalizedRealPrincipalSeriesKFiniteEmbedding s v) =
      realCompactKFiniteEmbedding (s + 1) v by
    change realPrincipalSeriesRestrictToK (s + 1)
      (realCompactPictureExtend (s + 1) (realCompactKFiniteEmbedding (s + 1) v)) = _
    exact realPrincipalSeriesRestrictToK_extend (s + 1)
      (realCompactKFiniteEmbedding (s + 1) v)]
  exact LinearMap.congr_fun
    (realCompactKFiniteEmbedding_intertwines_K (s + 1) q) v

/-- Finite K-type subspace inside normalized algebraic coinduction. -/
def normalizedRealPrincipalSeriesKFiniteSubmodule (s : ℝ) :
    Submodule ℂ (normalizedRealPrincipalSeriesSpace s) :=
  LinearMap.range (normalizedRealPrincipalSeriesKFiniteEmbedding s)

/-- The coinduced finite-K-type subspace is stable under right translation by `K`. -/
theorem normalizedRealPrincipalSeriesKFiniteSubmodule_K_invariant
    (s : ℝ) (q : upperHalfPlaneStabilizer) :
    normalizedRealPrincipalSeriesKFiniteSubmodule s ≤
      (normalizedRealPrincipalSeriesKFiniteSubmodule s).comap
        ((algebraicRealPrincipalSeries (s + 1)) (q : SL2R)) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨sphericalKTypeRepresentation q v, ?_⟩
  exact LinearMap.congr_fun
    (normalizedRealPrincipalSeriesKFiniteEmbedding_intertwines_K s q) v

end
end GaloisForLFunctions.RHTower
