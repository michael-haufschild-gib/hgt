import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceCompressedInverseDeterminant
import GaloisForLFunctions.RHTower.PrimeArchXiCompactThorinRH

/-!
# Hedenmalm theta Green-square boundary law

Route P's compact Markov/Thorin carrier and positivity of the squared nonzero spectrum of the
source-built Hedenmalm theta inverse are the same RH-strength condition.  The exact singular-metric
Green identity localizes the difference between the source square and a positive bulk square to
the universal rank-two pinned boundary current.
-/

open Complex MeasureTheory

namespace RHTower.HedenmalmThetaSource

noncomputable section

open GaloisForLFunctions.HTGeometry

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Every nonzero spectral value of the source inverse has strictly positive real square.  The
operator is constructed from the theta source before the Xi divisor is read. -/
def ThetaSquaredSeamSpectrumPositive : Prop :=
  ∀ mu : ℂ, mu ∈ spectrum ℂ thetaKernelOperator → mu ≠ 0 →
    ∃ r : ℝ, 0 < r ∧ mu ^ (2 : ℕ) = (r : ℂ)

/-- The universal rank-two boundary current is neutral on every multiplicity-exact theta divisor
mode. -/
def ThetaGreenBoundaryNeutral : Prop :=
  ∀ q : XiZeroCopy, thetaXiRankTwoBoundaryFlux q = 0

/-- Squared spectral positivity of the fixed theta source inverse is exactly RH.  The reverse
direction has no imaginary-axis loophole: a strictly positive real complex square has a real
nonzero square root. -/
theorem thetaSquaredSeamSpectrumPositive_iff_riemannHypothesis :
    ThetaSquaredSeamSpectrumPositive ↔ RiemannHypothesis := by
  constructor
  · intro hsquare
    rw [riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real]
    intro mu hspec hmu
    obtain ⟨r, hr, hsq⟩ := hsquare mu hspec hmu
    have hre := congrArg Complex.re hsq
    have him := congrArg Complex.im hsq
    simp only [pow_two, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im] at hre him
    have hprod : mu.re * mu.im = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hrealZero | himZero
    · have : r ≤ 0 := by nlinarith [sq_nonneg mu.im]
      exact (not_le_of_gt hr this).elim
    · refine ⟨mu.re, ?_⟩
      apply Complex.ext
      · simp
      · simp [himZero]
  · intro hRH mu hspec hmu
    have hreal :=
      (riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real.mp hRH)
        mu hspec hmu
    obtain ⟨t, rfl⟩ := hreal
    have ht : t ≠ 0 := by
      intro ht0
      apply hmu
      simp [ht0]
    refine ⟨t ^ (2 : ℕ), sq_pos_of_ne_zero ht, ?_⟩
    norm_num

/-- Neutrality of the source-built Green boundary current on every divisor mode is exactly RH. -/
theorem thetaGreenBoundaryNeutral_iff_riemannHypothesis :
    ThetaGreenBoundaryNeutral ↔ RiemannHypothesis := by
  constructor
  · intro hneutral
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hflux := hneutral q
    rw [thetaXiRankTwoBoundaryFlux_eq] at hflux
    have hcoefficient :
        2 * thetaSource.mass * thetaXiRootEnergy q ≠ 0 := by
      exact ne_of_gt (mul_pos
        (mul_pos (by norm_num) thetaSource.mass_pos)
        (thetaXiRootEnergy_pos q))
    have hproduct :
        (2 * thetaSource.mass * thetaXiRootEnergy q) *
            (xiSpectralPoint q).im = 0 := by
      calc
        (2 * thetaSource.mass * thetaXiRootEnergy q) *
            (xiSpectralPoint q).im =
            2 * thetaSource.mass * (xiSpectralPoint q).im *
              thetaXiRootEnergy q := by ring
        _ = 0 := hflux
    have him : (xiSpectralPoint q).im = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hcoefficient
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [him]
  · intro hRH q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [thetaXiRankTwoBoundaryFlux_eq, ht]
    simp

/-- Route P squared spectral positivity and pointwise Green-boundary neutrality are the same
source law. -/
theorem thetaSquaredSeamSpectrumPositive_iff_greenBoundaryNeutral :
    ThetaSquaredSeamSpectrumPositive ↔ ThetaGreenBoundaryNeutral := by
  rw [thetaSquaredSeamSpectrumPositive_iff_riemannHypothesis,
    thetaGreenBoundaryNeutral_iff_riemannHypothesis]

/-- The source-built squared-spectrum condition is exactly Route P's compact Markov-germ
representation. -/
theorem thetaSquaredSeamSpectrumPositive_iff_compactMarkov :
    ThetaSquaredSeamSpectrumPositive ↔ PrimeArchCompactMarkovGermRepresentation := by
  rw [thetaSquaredSeamSpectrumPositive_iff_riemannHypothesis,
    primeArchCompactMarkovGermRepresentation_iff_riemannHypothesis]

/-- Route P's Markov carrier exists exactly when the rank-two theta Green boundary is neutral on
every divisor mode. -/
theorem thetaGreenBoundaryNeutral_iff_compactMarkov :
    ThetaGreenBoundaryNeutral ↔ PrimeArchCompactMarkovGermRepresentation := by
  rw [thetaGreenBoundaryNeutral_iff_riemannHypothesis,
    primeArchCompactMarkovGermRepresentation_iff_riemannHypothesis]

/-- The same source-built condition is exactly Route P's compact Thorin-exponent
representation. -/
theorem thetaSquaredSeamSpectrumPositive_iff_compactThorin :
    ThetaSquaredSeamSpectrumPositive ↔ PrimeArchCompactThorinExponentRepresentation := by
  rw [thetaSquaredSeamSpectrumPositive_iff_riemannHypothesis,
    primeArchCompactThorinExponentRepresentation_iff_riemannHypothesis]

/-- Route P's Thorin carrier exists exactly when the same rank-two source boundary is neutral. -/
theorem thetaGreenBoundaryNeutral_iff_compactThorin :
    ThetaGreenBoundaryNeutral ↔ PrimeArchCompactThorinExponentRepresentation := by
  rw [thetaGreenBoundaryNeutral_iff_riemannHypothesis,
    primeArchCompactThorinExponentRepresentation_iff_riemannHypothesis]

/-- The Green-square correction lands in the same two-dimensional affine boundary space as the
universal pinned defect. -/
theorem range_pinnedBoundary_mul_thetaKernel_le_affineSubspace :
    LinearMap.range (pinnedBoundaryCLM * thetaKernelOperator).toLinearMap ≤
      pinnedAffineSubspace := by
  rintro y ⟨f, rfl⟩
  exact pinnedBoundaryCLM_mem_affineSubspace (thetaKernelOperator f)

/-- **Green-square boundary decomposition.**  The singular-metric square of the fixed theta source
inverse is a positive bulk square plus one rank-two boundary correction.  This is the exact
operator landing of Route P's coupled source-cancellation problem. -/
theorem thetaMetric_greenSquare_boundary_decomposition :
    thetaMetricOperator * (thetaKernelOperator * thetaKernelOperator) =
      ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator *
          thetaKernelOperator +
        Complex.I • (pinnedBoundaryCLM * thetaKernelOperator) := by
  have h := thetaMetric_commutator_thetaKernelOperator
  have h' :
      thetaMetricOperator * thetaKernelOperator =
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator +
          Complex.I • pinnedBoundaryCLM := by
    rw [sub_eq_iff_eq_add] at h
    simpa only [add_comm] using h
  calc
    thetaMetricOperator * (thetaKernelOperator * thetaKernelOperator) =
        (thetaMetricOperator * thetaKernelOperator) * thetaKernelOperator := by
          rw [mul_assoc]
    _ = (ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator +
          Complex.I • pinnedBoundaryCLM) * thetaKernelOperator := by rw [h']
    _ = ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator *
          thetaKernelOperator +
        Complex.I • (pinnedBoundaryCLM * thetaKernelOperator) := by
          rw [add_mul, smul_mul_assoc]

end

end RHTower.HedenmalmThetaSource
