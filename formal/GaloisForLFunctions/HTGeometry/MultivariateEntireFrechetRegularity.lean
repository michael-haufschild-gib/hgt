import GaloisForLFunctions.HTGeometry.MultivariateEntireAffinePullback
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic

/-!
# Fréchet regularity of compact-open multivariate entire sources

Continuity plus entireness on every affine complex line implies a convergent Fréchet power series
in finite complex dimension.  Thus the intrinsic affine-line definition of `MultivariateEntire`
already supplies global analyticity and smoothness; downstream jet theorems need no extra
regularity premise.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The stored line-entire property is the generic affine-line-entire condition. -/
theorem MultivariateEntire.affineLineEntire {d : ℕ} (f : MultivariateEntire d) :
    AffineLineEntire f.1 :=
  f.2

/-- Every compact-open multivariate entire source is analytic everywhere. -/
theorem MultivariateEntire.analyticOnNhd {d : ℕ} (f : MultivariateEntire d) :
    AnalyticOnNhd ℂ f.1 Set.univ :=
  analyticOnNhd_of_continuous_affineLineEntire f.1.continuous
    (MultivariateEntire.affineLineEntire f)

/-- Every compact-open multivariate entire source is globally Fréchet-smooth. -/
theorem MultivariateEntire.contDiff {d : ℕ} (f : MultivariateEntire d) :
    ContDiff ℂ (⊤ : WithTop ℕ∞) f.1 :=
  (MultivariateEntire.analyticOnNhd f).contDiff

end

end GaloisForLFunctions.HTGeometry
