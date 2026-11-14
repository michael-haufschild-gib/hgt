import GaloisForLFunctions.HTGeometry.Probability.ComplexSphereMellin
import GaloisForLFunctions.HTGeometry.Probability.BlockSphereBetaLaw

/-!
# The beta law of a complex spherical coordinate

The squared norm of a complex coordinate on the normalized sphere has law
`Beta(1, dim(V)/2)`, where `V` is its nonzero real orthogonal complement.
This is the two-dimensional block case of the spherical projection law.
Power weighting gives exact concentration laws for high coordinate monomials.
-/

open MeasureTheory ProbabilityTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

section Coordinate

variable (V : Type*) [NormedAddCommGroup V]

/-- Squared complex-coordinate modulus on the unit sphere. -/
def complexBlockSphereCoordinate (ω : sphere (0 : BlockSpace ℂ V) 1) : ℝ :=
  blockSphereCoordinate ℂ V ω

theorem continuous_complexBlockSphereCoordinate : Continuous (complexBlockSphereCoordinate V) :=
  continuous_blockSphereCoordinate ℂ V

/-- The squared coordinate lies in the unit interval. -/
theorem complexBlockSphereCoordinate_mem (ω : sphere (0 : BlockSpace ℂ V) 1) :
    complexBlockSphereCoordinate V ω ∈ Icc (0 : ℝ) 1 :=
  blockSphereCoordinate_mem ℂ V ω

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Probability law of the squared coordinate under normalized spherical measure. -/
def complexBlockCoordinateLaw : Measure ℝ := blockCoordinateLaw ℂ V

instance complexBlockCoordinateLaw_isProbability : IsProbabilityMeasure (complexBlockCoordinateLaw V) :=
  blockCoordinateLaw_isProbability ℂ V

/-- The coordinate law is carried by `[0,1]`. -/
theorem complexBlockCoordinateLaw_carried :
    complexBlockCoordinateLaw V (Icc (0 : ℝ) 1)ᶜ = 0 :=
  blockCoordinateLaw_carried ℂ V

/-- All coordinate moments are integrable, since the coordinate lies in a compact interval. -/
theorem integrable_complexBlockCoordinateLaw_pow (k : ℕ) :
    Integrable (fun u : ℝ => u ^ k) (complexBlockCoordinateLaw V) :=
  integrable_blockCoordinateLaw_pow ℂ V k

/-- Moments of the coordinate probability law are the spherical Mellin moments. -/
theorem integral_complexBlockCoordinateLaw_pow (k : ℕ) :
    (∫ u : ℝ, u ^ k ∂complexBlockCoordinateLaw V) = complexBlockSphereMellin V k :=
  integral_blockCoordinateLaw_pow ℂ V k

end Coordinate

section Beta

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- The full squared-coordinate law is beta, in every real dimension with a nonzero complement. -/
theorem complexBlockCoordinateLaw_eq_beta :
    complexBlockCoordinateLaw V = betaMeasure 1 ((Module.finrank ℝ V : ℝ) / 2) := by
  simpa [complexBlockCoordinateLaw] using blockCoordinateLaw_eq_beta ℂ V

/-- The normalized monomial-power tilt of the squared-coordinate law. -/
def complexBlockCoordinateTilt (k : ℕ) : Measure ℝ := blockCoordinateTilt ℂ V k

/-- Weighting by `|z₁|^(2k)` shifts the first beta parameter from `1` to `k+1`. -/
theorem complexBlockCoordinateTilt_eq_beta (k : ℕ) :
    complexBlockCoordinateTilt V k =
      betaMeasure (1 + (k : ℝ)) ((Module.finrank ℝ V : ℝ) / 2) := by
  simpa [complexBlockCoordinateTilt] using blockCoordinateTilt_eq_beta ℂ V k

/-- Exact mean transverse squared radius under a high-coordinate-power tilt. -/
theorem integral_complexBlockCoordinateTilt_transverse (k : ℕ) :
    (∫ u : ℝ, 1 - u ∂complexBlockCoordinateTilt V k) =
      ((Module.finrank ℝ V : ℝ) / 2) /
        (1 + (k : ℝ) + (Module.finrank ℝ V : ℝ) / 2) := by
  simpa [complexBlockCoordinateTilt] using integral_blockCoordinateTilt_transverse ℂ V k

end Beta

end GaloisForLFunctions.HTGeometry
