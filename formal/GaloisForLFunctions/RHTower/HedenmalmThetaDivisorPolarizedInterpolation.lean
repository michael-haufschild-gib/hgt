import GaloisForLFunctions.RHTower.HedenmalmThetaQuantileResolventPortLaw
import GaloisForLFunctions.RHTower.HedenmalmThetaCompactFluxEnergy

/-!
# Polarized interpolation on every theta divisor mode

The lightlike theta quantile source has a fixed, nonzero polarized response against every
multiplicity copy of the Xi divisor.  The two source-built metric probes are genuinely
nonproportional, and no divisor eigenmode is dark to both probes.

These are unconditional observability statements.  They do not assert a uniform lower frame
bound and therefore do not prove RH.
-/

open Complex MeasureTheory
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmClosedWeightedDerivative

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Every multiplicity copy of the Xi divisor has the same nonzero monopole. -/
theorem pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass (q : XiZeroCopy) :
    pinnedMean (thetaXiDivisorEigenvector q) =
      (Real.sqrt thetaSource.mass : ℂ) := by
  exact pinnedMean_thetaDivisorEigenvector
    (xiSpectralPoint q) (thetaXiSpectralPoint_mem_sourceStrip q)
      (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- The boundary polarization of the quantile source against every divisor mode is one fixed
nonzero scalar. -/
theorem inner_pinnedBoundaryCLM_thetaQuantileCoordinate_thetaXiDivisorEigenvector
    (q : XiZeroCopy) :
    (inner ℂ (pinnedBoundaryCLM thetaQuantileCoordinate)
      (thetaXiDivisorEigenvector q) : ℂ) =
        -pinnedFirstMoment thetaQuantileCoordinate *
          (Real.sqrt thetaSource.mass : ℂ) := by
  rw [inner_pinnedBoundaryCLM_thetaQuantileCoordinate,
    pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass]

/-- Exact divisor interpolation law for the fixed-source symplectic metric current. -/
theorem thetaXiDivisor_metricSymplectic_eq_I_mul_dipole_sqrt_mass
    (q : XiZeroCopy) :
    (inner ℂ
        (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate))
        (thetaXiDivisorEigenvector q) : ℂ) -
      inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
        (thetaKernelOperator (thetaXiDivisorEigenvector q)) =
      Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
        (Real.sqrt thetaSource.mass : ℂ) := by
  have h := thetaQuantileBoundaryDipole_mul_pinnedMean_eq_metricSymplectic
    (thetaXiDivisorEigenvector q)
  rw [pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass] at h
  have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    norm_num
  calc
    (inner ℂ
        (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate))
        (thetaXiDivisorEigenvector q) : ℂ) -
          inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
            (thetaKernelOperator (thetaXiDivisorEigenvector q)) =
        (Complex.I * (-Complex.I)) *
          ((inner ℂ
              (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate))
              (thetaXiDivisorEigenvector q) : ℂ) -
            inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
              (thetaKernelOperator (thetaXiDivisorEigenvector q))) := by
          rw [hI, one_mul]
    _ = Complex.I *
          (pinnedFirstMoment thetaQuantileCoordinate *
            (Real.sqrt thetaSource.mass : ℂ)) := by
          rw [mul_assoc, ← h]
    _ = Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
          (Real.sqrt thetaSource.mass : ℂ) := by ring

/-- On a divisor eigenmode, the two fixed metric probes obey an affine interpolation law whose
right side is independent of the divisor point. -/
theorem thetaXiDivisor_metricProbe_affine_interpolation (q : XiZeroCopy) :
    (inner ℂ
        (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate))
        (thetaXiDivisorEigenvector q) : ℂ) -
      thetaXiReciprocalEigenvalue q *
        inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
          (thetaXiDivisorEigenvector q) =
      Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
        (Real.sqrt thetaSource.mass : ℂ) := by
  have heigen :
      thetaKernelOperator (thetaXiDivisorEigenvector q) =
        thetaXiReciprocalEigenvalue q • thetaXiDivisorEigenvector q := by
    rw [thetaKernelOperator_eq_thetaCompactSourceInverse]
    exact thetaCompactSourceInverse_thetaXi_eigen q
  rw [← thetaXiDivisor_metricSymplectic_eq_I_mul_dipole_sqrt_mass q,
    heigen, inner_smul_right]

/-- The quantile source is a nonzero state. -/
theorem thetaQuantileCoordinate_ne_zero : thetaQuantileCoordinate ≠ (0 : ThetaH) := by
  intro hQ
  apply pinnedBoundaryCLM_thetaQuantileCoordinate_ne_zero
  rw [hQ, map_zero]

/-- The compact source inverse does not preserve the quantile-source line.  The zero-eigenvalue
case uses injectivity of the pinned primitive on the centered hyperplane; the nonzero case uses
the exact eigenmode monopole obstruction. -/
theorem thetaKernelOperator_thetaQuantileCoordinate_ne_smul (c : ℂ) :
    thetaKernelOperator thetaQuantileCoordinate ≠ c • thetaQuantileCoordinate := by
  intro hline
  by_cases hc : c = 0
  · have hkernel : thetaCompactSourceInverse thetaQuantileCoordinate = 0 := by
      rw [← thetaKernelOperator_eq_thetaCompactSourceInverse, hline, hc, zero_smul]
    have hprimitive : pinnedVolterra thetaQuantileCoordinate = 0 :=
      pinnedVolterra_eq_zero_of_kernelOperator_eq_zero hkernel
    have hQzero := eq_zero_of_pinnedMean_eq_zero_of_pinnedVolterra_eq_zero
      thetaQuantileCoordinate pinnedMean_thetaQuantileCoordinate_eq_zero hprimitive
    exact thetaQuantileCoordinate_ne_zero hQzero
  · have heigen : thetaCompactSourceInverse thetaQuantileCoordinate =
        c • thetaQuantileCoordinate := by
      rw [← thetaKernelOperator_eq_thetaCompactSourceInverse]
      exact hline
    have hmean := pinnedMean_ne_zero_of_thetaCompactSourceInverse_eigen hc
      thetaQuantileCoordinate_ne_zero heigen
    exact hmean pinnedMean_thetaQuantileCoordinate_eq_zero

/-- Injectivity of the singular metric preserves the genuinely rank-two source control port. -/
theorem thetaMetricProbe_ne_smul (c : ℂ) :
    thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate) ≠
      c • thetaMetricOperator thetaQuantileCoordinate := by
  intro hline
  have hGinj : Function.Injective thetaMetricOperator :=
    metricOperator_injective thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le
  apply thetaKernelOperator_thetaQuantileCoordinate_ne_smul c
  apply hGinj
  simpa only [map_smul] using hline

/-- No Xi divisor eigenmode is simultaneously dark to both fixed metric probes. -/
theorem thetaXiDivisor_not_jointly_metric_dark (q : XiZeroCopy) :
    ¬ ((inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
          (thetaXiDivisorEigenvector q) : ℂ) = 0 ∧
        (inner ℂ
          (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate))
          (thetaXiDivisorEigenvector q) : ℂ) = 0) := by
  rintro ⟨hQ, hBQ⟩
  have hinterp := thetaXiDivisor_metricProbe_affine_interpolation q
  rw [hQ, hBQ, mul_zero, sub_zero] at hinterp
  have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  have hnonzero : Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
      (Real.sqrt thetaSource.mass : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero Complex.I_ne_zero
      pinnedFirstMoment_thetaQuantileCoordinate_ne_zero) hsqrt
  exact hnonzero hinterp.symm

/-- Every two eigenvectors at the same nonzero eigenvalue are proportional.  Thus every nonzero
point eigenspace of the compact theta source inverse is geometrically one-dimensional. -/
theorem thetaCompactSourceInverse_eigenvectors_proportional
    {c : ℂ} (hc : c ≠ 0) {f g : ThetaH}
    (hf : thetaCompactSourceInverse f = c • f)
    (hg : thetaCompactSourceInverse g = c • g) (hg0 : g ≠ 0) :
    ∃ a : ℂ, f = a • g := by
  have hmg : pinnedMean g ≠ 0 :=
    pinnedMean_ne_zero_of_thetaCompactSourceInverse_eigen hc hg0 hg
  let a : ℂ := pinnedMean f / pinnedMean g
  have hcenter : pinnedMean (f - a • g) = 0 := by
    calc
      pinnedMean (f - a • g) = thetaPinnedMeanCLM (f - a • g) :=
        (thetaPinnedMeanCLM_apply _).symm
      _ = 0 := by
        rw [map_sub, map_smul, thetaPinnedMeanCLM_apply,
          thetaPinnedMeanCLM_apply]
        dsimp only [a]
        simp only [smul_eq_mul]
        field_simp
        ring
  have heigen : thetaCompactSourceInverse (f - a • g) = c • (f - a • g) := by
    rw [map_sub, map_smul, hf, hg, smul_smul]
    module
  have hzero : f - a • g = 0 := by
    by_contra hne
    exact (pinnedMean_ne_zero_of_thetaCompactSourceInverse_eigen hc hne heigen) hcenter
  exact ⟨a, sub_eq_zero.mp hzero⟩

theorem thetaXiReciprocalEigenvalue_ne_zero (q : XiZeroCopy) :
    thetaXiReciprocalEigenvalue q ≠ 0 := by
  exact neg_ne_zero.mpr (inv_ne_zero (xiSpectralPoint_ne_zero q))

/-- A divisor eigenspace is reconstructed canonically from one scalar monopole. -/
theorem thetaCompactSourceInverse_eigenvector_eq_mean_smul_thetaXiDivisorEigenvector
    (q : XiZeroCopy) {f : ThetaH}
    (hf : thetaCompactSourceInverse f =
      thetaXiReciprocalEigenvalue q • f) :
    f = (pinnedMean f / (Real.sqrt thetaSource.mass : ℂ)) •
      thetaXiDivisorEigenvector q := by
  obtain ⟨a, hfa⟩ := thetaCompactSourceInverse_eigenvectors_proportional
    (thetaXiReciprocalEigenvalue_ne_zero q) hf
      (thetaCompactSourceInverse_thetaXi_eigen q)
      (thetaXiDivisorEigenvector_ne_zero q)
  have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  have hmean := congrArg pinnedMean hfa
  rw [pinnedMean_smul,
    pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass] at hmean
  have ha : a = pinnedMean f / (Real.sqrt thetaSource.mass : ℂ) := by
    apply (eq_div_iff hsqrt).2
    exact hmean.symm
  calc
    f = a • thetaXiDivisorEigenvector q := hfa
    _ = (pinnedMean f / (Real.sqrt thetaSource.mass : ℂ)) •
        thetaXiDivisorEigenvector q := by rw [ha]

/-- Mean-normalized divisor eigenvectors are unique, even when the corresponding Xi zero has
unknown algebraic multiplicity. -/
theorem thetaCompactSourceInverse_eigenvector_eq_thetaXiDivisorEigenvector_of_mean
    (q : XiZeroCopy) {f : ThetaH}
    (hf : thetaCompactSourceInverse f =
      thetaXiReciprocalEigenvalue q • f)
    (hmean : pinnedMean f = (Real.sqrt thetaSource.mass : ℂ)) :
    f = thetaXiDivisorEigenvector q := by
  rw [thetaCompactSourceInverse_eigenvector_eq_mean_smul_thetaXiDivisorEigenvector q hf,
    hmean, div_self, one_smul]
  exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'

end

end RHTower.HedenmalmThetaSource
