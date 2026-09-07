import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactAction
import GaloisForLFunctions.RHTower.RealPrincipalSeriesKTypes

/-!
# K-action on finite compact-picture Fourier types

Every even Fourier vector is proved to be a genuine K-type eigenvector for the transported
principal-series action.  The diagonal K-representation on finitely supported weight sequences is
constructed and its finite Fourier embedding into the compact picture is proved intertwining.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem compactRealPrincipalSeries_KType_eigenvector (σ : ℝ)
    (q : upperHalfPlaneStabilizer) (m : ℤ) :
    compactRealPrincipalSeries σ (q : SL2R) (realCompactKType σ m) =
      realSphericalKTypeCharacter m q • realCompactKType σ m := by
  ext k
  change realUpperBorelRpowCharacter σ
        (realIwasawaB ((k : SL2R) * (q : SL2R))) *
      realSphericalKTypeCharacter m
        (realIwasawaK ((k : SL2R) * (q : SL2R))) =
    realSphericalKTypeCharacter m q * realSphericalKTypeCharacter m k
  have hkq : (k : SL2R) * (q : SL2R) = ((k * q : upperHalfPlaneStabilizer) : SL2R) := rfl
  rw [hkq, realIwasawaB_of_K, realIwasawaK_of_K]
  simp only [map_one, one_mul, map_mul]
  exact mul_comm _ _

/-- Diagonal action of `K` on the explicit finite-support K-type model. -/
def sphericalKTypeAction (q : upperHalfPlaneStabilizer) :
    Module.End ℂ SphericalKFiniteModel :=
  weightedShift 0 (fun m ↦ realSphericalKTypeCharacter m q)

@[simp]
theorem sphericalKTypeAction_single (q : upperHalfPlaneStabilizer)
    (m : ℤ) (z : ℂ) :
    sphericalKTypeAction q (Finsupp.single m z) =
      Finsupp.single m (realSphericalKTypeCharacter m q * z) := by
  simp [sphericalKTypeAction]

/-- Representation of `K` on finite spherical K-types by their even characters. -/
def sphericalKTypeRepresentation :
    Representation ℂ upperHalfPlaneStabilizer SphericalKFiniteModel where
  toFun q := sphericalKTypeAction q
  map_one' := by
    apply Finsupp.lhom_ext
    intro m z
    simp
  map_mul' q r := by
    apply Finsupp.lhom_ext
    intro m z
    rw [Module.End.mul_eq_comp, LinearMap.comp_apply]
    rw [sphericalKTypeAction_single, sphericalKTypeAction_single,
      sphericalKTypeAction_single]
    rw [map_mul]
    simp [mul_assoc]

/-- Finite Fourier expansion intertwines the diagonal K-type representation with compact-picture
right translation restricted to `K`. -/
theorem realCompactKFiniteEmbedding_intertwines_K (σ : ℝ)
    (q : upperHalfPlaneStabilizer) :
    (realCompactKFiniteEmbedding σ).comp (sphericalKTypeRepresentation q) =
      (compactRealPrincipalSeries σ (q : SL2R)).comp
        (realCompactKFiniteEmbedding σ) := by
  apply Finsupp.lhom_ext
  intro m z
  change realCompactKFiniteEmbedding σ
      (sphericalKTypeAction q (Finsupp.single m z)) =
    compactRealPrincipalSeries σ (q : SL2R)
      (realCompactKFiniteEmbedding σ (Finsupp.single m z))
  rw [sphericalKTypeAction_single,
    realCompactKFiniteEmbedding_single, realCompactKFiniteEmbedding_single]
  rw [map_smul, compactRealPrincipalSeries_KType_eigenvector]
  simp [smul_smul, mul_comm]

end
end GaloisForLFunctions.RHTower
