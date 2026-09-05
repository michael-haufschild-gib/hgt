import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaDimensionlessReality
import Mathlib.Tactic

/-!
# Real region-I form of the dimensionless curvature equation

For positive `q₀`, the canonical real Jacobian converts arclength dynamics into the paper's
dimensionless equation `(q')² = 4(q₀-q)(q²+(1+γ²)q₀q-q₀²ν²)` with no residual scale factor.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Stationary elastica whose real parameters realize a point of paper region I. -/
structure RegionICenteredElastica
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  parameter : RegionIParameters
  normalization : CenteredElasticaNormalization V
  gammaSq_match : normalization.gamma ^ 2 = gammaSq parameter.val
  nuSq_match : normalization.nu ^ 2 = nuSq parameter.val

noncomputable def regionICurvatureProfile
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : RegionICenteredElastica V) (v : ℝ) : ℝ :=
  dimensionlessSquaredCurvature R.normalization R.parameter.val.q₀
    (v / regionIDimensionlessJacobian R.parameter R.normalization.curvatureUnit)

noncomputable def regionICurvatureProfileVelocity
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : RegionICenteredElastica V) (v : ℝ) : ℝ :=
  dimensionlessSquaredCurvatureVelocity R.normalization R.parameter.val.q₀
      (v / regionIDimensionlessJacobian R.parameter R.normalization.curvatureUnit) *
    (1 / regionIDimensionlessJacobian R.parameter R.normalization.curvatureUnit)

theorem regionICurvatureProfile_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : RegionICenteredElastica V) (v : ℝ) :
    HasDerivAt (regionICurvatureProfile R) (regionICurvatureProfileVelocity R v) v := by
  let σ := regionIDimensionlessJacobian R.parameter R.normalization.curvatureUnit
  have hscale : HasDerivAt (fun x : ℝ => x / σ) (1 / σ) v :=
    (hasDerivAt_id v).div_const σ
  have h := (dimensionlessSquaredCurvature_hasDerivAt R.normalization
    R.parameter.val.q₀ (v / σ)).comp v hscale
  change HasDerivAt
    (dimensionlessSquaredCurvature R.normalization R.parameter.val.q₀ ∘
      fun x => x / σ)
    (dimensionlessSquaredCurvatureVelocity R.normalization R.parameter.val.q₀ (v / σ) *
      (1 / σ)) v
  exact h

theorem regionICurvatureProfile_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : RegionICenteredElastica V) :
    regionICurvatureProfile R 0 = (R.parameter.val.q₀ : ℝ) := by
  rw [regionICurvatureProfile, zero_div,
    dimensionlessSquaredCurvature_zero]

theorem regionICurvatureProfileVelocity_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : RegionICenteredElastica V) :
    regionICurvatureProfileVelocity R 0 = 0 := by
  rw [regionICurvatureProfileVelocity, zero_div,
    dimensionlessSquaredCurvatureVelocity_zero, zero_mul]

/-- Paper equation (62), now as an actual real differential equation throughout region I. -/
theorem regionICurvatureProfile_equation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : RegionICenteredElastica V) (v : ℝ) :
    regionICurvatureProfileVelocity R v ^ 2 =
      dimensionlessCurvatureRHS (R.parameter.val.q₀ : ℝ)
        R.normalization.gamma R.normalization.nu (regionICurvatureProfile R v) := by
  let σ := regionIDimensionlessJacobian R.parameter R.normalization.curvatureUnit
  let s := v / σ
  have harc := dimensionlessSquaredCurvature_arclength_equation R.normalization
    R.parameter.val.q₀ s
  have hσ := regionIDimensionlessJacobian_sq R.parameter R.normalization.curvatureUnit
  have hσpos := regionIDimensionlessJacobian_pos R.parameter R.normalization.curvatureUnit
  change (dimensionlessSquaredCurvatureVelocity R.normalization R.parameter.val.q₀ s *
      (1 / σ)) ^ 2 =
    dimensionlessCurvatureRHS (R.parameter.val.q₀ : ℝ)
      R.normalization.gamma R.normalization.nu
        (dimensionlessSquaredCurvature R.normalization R.parameter.val.q₀ s)
  change σ ^ 2 = dimensionlessArclengthFactor R.normalization.curvatureUnit
    R.parameter.val.q₀ at hσ
  rw [dimensionlessArclengthFactor] at hσ
  change σ ^ 2 = R.normalization.frame.geometry.curvature 0 ^ 2 /
    (4 * (R.parameter.val.q₀ : ℝ)) at hσ
  rw [← hσ] at harc
  change 0 < σ at hσpos
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  field_simp [hσne]
  nlinarith [harc]

/-- Parameter-only version of the region-I cubic, using the paper's definitions of `γ²` and
`ν²`. -/
theorem regionICurvatureProfile_parameter_equation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : RegionICenteredElastica V) (v : ℝ) :
    regionICurvatureProfileVelocity R v ^ 2 =
      4 * ((R.parameter.val.q₀ : ℝ) - regionICurvatureProfile R v) *
        (regionICurvatureProfile R v ^ 2 +
          (1 + gammaSq R.parameter.val) * (R.parameter.val.q₀ : ℝ) *
            regionICurvatureProfile R v -
          (R.parameter.val.q₀ : ℝ) ^ 2 * nuSq R.parameter.val) := by
  rw [regionICurvatureProfile_equation, dimensionlessCurvatureRHS,
    R.gammaSq_match, R.nuSq_match]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
