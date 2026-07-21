import GaloisForLFunctions.RHTower.HermiteEvenCarrier
import GaloisForLFunctions.HilbertMetric.SlaterPluckerConnector

/-!
# Hermite-even Slater--Pluecker connector

The step-four Hermite family is already an orthonormal Fourier-fixed family in the complex even
carrier.  Realifying its inner product gives a square Gram coordinate frame.  Since every orbital
of that square frame is occupied, its canonical Pluecker partition is one exponential carrying
the total degree.  Its logarithm is globally affine: the first jet is the total degree and every
higher curvature contribution, beginning with the second jet, vanishes.

This is a finite static identity.  It assumes no ambient finite-dimensionality, aperture limit,
zero-location statement, or Riemann-hypothesis premise.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

local instance evenSubspaceRealInnerProductSpace : InnerProductSpace ℝ evenSubspace :=
  InnerProductSpace.rclikeToReal ℂ evenSubspace

/-- The complex orthonormal step-four Hermite block remains orthonormal after realification. -/
theorem orthonormal_hermiteEvenUnit_real (m : ℕ) :
    Orthonormal ℝ (fun j : Fin m => hermiteEvenUnit (j : ℕ)) := by
  have hc := orthonormal_hermiteEvenUnit m
  rw [orthonormal_iff_ite] at hc ⊢
  intro i j
  rw [real_inner_eq_re_inner, hc i j]
  split <;> simp

/-- Real Gram coordinates of the first `m` Fourier-fixed Hermite vectors. -/
def hermiteEvenRealGramCoordinates (m : ℕ) : Fin m → Fin m → ℝ :=
  fun i j => inner ℝ (hermiteEvenUnit (i : ℕ)) (hermiteEvenUnit (j : ℕ))

@[simp] theorem hermiteEvenRealGramCoordinates_apply (m : ℕ) (i j : Fin m) :
    hermiteEvenRealGramCoordinates m i j = if i = j then 1 else 0 := by
  exact (orthonormal_iff_ite.mp (orthonormal_hermiteEvenUnit_real m)) i j

/-- The actual Hermite Gram coordinates discharge HilbertMetric's abstract orthonormal coordinate
frame interface. -/
theorem hermiteEvenRealGramCoordinates_isOrthonormalCoordinateFrame (m : ℕ) :
    IsOrthonormalCoordinateFrame (hermiteEvenRealGramCoordinates m) := by
  intro i j
  simp only [hermiteEvenRealGramCoordinates_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The exponential Gram path of the square Hermite frame is diagonal, with one exponential degree
weight on each occupied orbital. -/
theorem exponentialFeatureGram_hermiteEvenRealGramCoordinates
    (m : ℕ) (degree : Fin m → ℕ) (s : ℝ) :
    exponentialFeatureGram (hermiteEvenRealGramCoordinates m) degree s =
      Matrix.diagonal (fun k => Real.exp (s * (degree k : ℝ))) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [exponentialFeatureGram]
  · simp [exponentialFeatureGram, hij]

/-- **Exact Hermite Pluecker partition.**  Along exponential degree scaling, the canonical feature
volume of the fully occupied Hermite block is one exponential carrying the total orbital degree. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_exp_eq_exp_totalDegree
    (m : ℕ) (degree : Fin m → ℕ) (s : ℝ) :
    canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
        degree (Real.exp s) =
      Real.exp (s * ∑ k, (degree k : ℝ)) := by
  rw [← det_exponentialFeatureGram_eq_canonicalFeatureVolume]
  rw [exponentialFeatureGram_hermiteEvenRealGramCoordinates, Matrix.det_diagonal]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The logarithm of the full Hermite Pluecker partition is globally affine in the scaling
parameter, not merely flat to second order at the origin. -/
theorem hermiteEvenRealGram_log_canonicalFeatureVolume_exp_eq
    (m : ℕ) (degree : Fin m → ℕ) (s : ℝ) :
    Real.log (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
        degree (Real.exp s)) = s * ∑ k, (degree k : ℝ) := by
  rw [hermiteEvenRealGram_canonicalFeatureVolume_exp_eq_exp_totalDegree, Real.log_exp]

/-- Full occupancy of the square Hermite coordinate frame makes its additive spectral mean the
sum of the assigned orbital energies. -/
theorem slaterSpectralMean_hermiteEvenRealGramCoordinates
    (m : ℕ) (energy : Fin m → ℝ) :
    slaterSpectralMean (hermiteEvenRealGramCoordinates m) energy = ∑ k, energy k := by
  simp [slaterSpectralMean, orbitalSpectralMean]

/-- Full occupancy has no residual degree fluctuation: the Slater compression variance of the
square Hermite coordinate frame vanishes for every energy assignment. -/
theorem slaterSpectralVariance_hermiteEvenRealGramCoordinates
    (m : ℕ) (energy : Fin m → ℝ) :
    slaterSpectralVariance (hermiteEvenRealGramCoordinates m) energy = 0 := by
  simp [slaterSpectralVariance, orbitalSpectralSecondMoment,
    slaterCompressedSpectralEnergy]

/-- **Exact Hermite--Slater--Pluecker log-jet law.**  For every finite step-four Hermite block and
every natural orbital-degree assignment, the first logarithmic jet of the canonical Pluecker
partition is the total occupied degree and the second logarithmic jet is exactly zero. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_logJets_exact
    (m : ℕ) (degree : Fin m → ℕ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s))) 0 = ∑ k, (degree k : ℝ) ∧
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s)))) 0 = 0 := by
  constructor
  · calc
      deriv (fun s => Real.log
          (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
            degree (Real.exp s))) 0 =
          slaterSpectralMean (hermiteEvenRealGramCoordinates m)
            (fun k => (degree k : ℝ)) :=
        canonicalFeatureVolume_logDerivative_eq_slaterSpectralMean
          (hermiteEvenRealGramCoordinates m) degree
          (hermiteEvenRealGramCoordinates_isOrthonormalCoordinateFrame m)
      _ = ∑ k, (degree k : ℝ) :=
        slaterSpectralMean_hermiteEvenRealGramCoordinates m _
  · calc
      deriv (deriv (fun s => Real.log
          (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
            degree (Real.exp s)))) 0 =
          slaterSpectralVariance (hermiteEvenRealGramCoordinates m)
            (fun k => (degree k : ℝ)) :=
        canonicalFeatureVolume_logSecondDerivative_eq_slaterSpectralVariance
          (hermiteEvenRealGramCoordinates m) degree
          (hermiteEvenRealGramCoordinates_isOrthonormalCoordinateFrame m)
      _ = 0 := slaterSpectralVariance_hermiteEvenRealGramCoordinates m _

end

end RHTower
