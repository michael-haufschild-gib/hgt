import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrimeQuantileHaarCarrier
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSquaredSeamPencil

/-!
# Xi divisor modes cannot have finite stationary prime-flow carriers

Every multiplicity-labelled Xi divisor point is a nonzero eigenmode of the fixed compact theta
source inverse.  Prime translation, however, is a strict parabolic flow on the intrinsic quantile
interval.  This module combines those two source-native facts.

No nonzero finite measure supported on the quantile interval can be stationary under a genuine
prime flow, independently of the divisor point and independently of RH.  The canonical invariant
survivor is instead the transported Haar measure, whose interior mass is infinite.  Consequently,
finite-state stationarity cannot be the missing principle selecting critical-line divisor modes;
any successful stationary interpretation must first pass to a quotient, relative class, or other
non-probability carrier.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- **Finite-stationarity no-go for genuine Xi modes.**  Every Xi copy remains an eigenmode of the
fixed compact theta source inverse, but no nonzero finite carrier supported on its intrinsic
quantile interval is invariant under any genuine integer prime flow.  This obstruction applies on
and off the critical line, so finite stationary mass cannot distinguish RH. -/
theorem thetaXiDivisorEigenmode_no_finite_stationary_carrier
    (q : XiZeroCopy) {n : ℕ} (hn : 1 < n)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) (hsupp : μ (Ioo (0 : ℝ) 1)ᶜ = 0) :
    thetaCompactSourceInverse (thetaXiDivisorEigenvector q) =
        thetaXiReciprocalEigenvalue q • thetaXiDivisorEigenvector q ∧
      Measure.map (thetaIntegerQuantileFlow n) μ ≠ μ := by
  refine ⟨thetaCompactSourceInverse_thetaXi_eigen q, ?_⟩
  intro hinv
  exact hμ (finiteMeasure_eq_zero_of_map_thetaIntegerQuantileFlow_eq_self
    μ hn hsupp hinv)

/-- **Positive survivor: infinite-volume covariance.**  Every genuine Xi eigenmode coexists with
the canonical prime-flow-invariant theta quantile Haar carrier.  Its full interior mass is
infinite, exactly the feature that evades the finite-stationarity no-go. -/
theorem thetaXiDivisorEigenmode_infiniteHaar_survivor
    (q : XiZeroCopy) (n : ℕ) :
    thetaCompactSourceInverse (thetaXiDivisorEigenvector q) =
        thetaXiReciprocalEigenvalue q • thetaXiDivisorEigenvector q ∧
      Measure.map (thetaIntegerQuantileFlow n) thetaQuantileHaarMeasure =
        thetaQuantileHaarMeasure ∧
      thetaQuantileHaarMeasure (Ioo (0 : ℝ) 1) = ⊤ := by
  exact ⟨thetaCompactSourceInverse_thetaXi_eigen q,
    map_thetaIntegerQuantileFlow_thetaQuantileHaarMeasure n,
    thetaQuantileHaarMeasure_Ioo⟩

end


end RHTower
