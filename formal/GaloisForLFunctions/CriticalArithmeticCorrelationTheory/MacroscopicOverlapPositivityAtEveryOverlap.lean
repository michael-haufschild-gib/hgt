import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheUpwardPrimeWindowsCarryTheShellCorrection
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilResidualIsTheUpwardDefect
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapTiltedSplineReserve

/-!
# The complete Weil matrix is eventually positive at every fixed overlap

At every fixed overlap `c > 0` the normalized Ramanujan vectors are norm quasimodes of the
complete Weil matrix with the completed conductor energies `E_m(c)`: the complete residual is
minus the upward defect up to a vanishing term, and the upward non-ratio prime rows carry the
shell correction `κ_m(c)` in `ℓ²`. For the boosted unit spline the fixed-overlap prime-defect
reserve and the common positive conductor floor then force the complete Weil matrix to be
eventually positive definite. In particular this holds at the macroscopic overlap `c = 3/2`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-- **Norm quasimodes at every overlap.** For a `C²` profile on `[0,1]` with positive mass, the
normalized Ramanujan vector of conductor `m` is an asymptotic eigenvector of the complete Weil
matrix at overlap `c` with eigenvalue the completed conductor energy `E_m(c)`. -/
theorem tendsto_completeWeilMatrix_ramanujan_quasimode_norm {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N)
        (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  have hres := tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm hφ hsupp hM hc hm
  -- the upward defect vanishes in norm
  have hup : Tendsto (fun N : ℕ => ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_sum_sq_upwardPrimeRow_sub_shellCorrection hφ hsupp hM hc hm)
    rw [Real.sqrt_zero] at h
    refine h.congr fun N => ?_
    simp only [Function.comp]
    rw [← norm_sq_upwardPrimeVector_sub, Real.sqrt_sq (norm_nonneg _)]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using hres.add hup)
  set a := Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
    completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N
  set b := upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
    shellCorrection φ c m • normalizedRamanujanHorizonVector m N
  calc ‖a‖ = ‖(a + b) - b‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖a + b‖ + ‖b‖ := norm_sub_le _ _

/-- **Positivity at every fixed overlap.** For the boosted unit spline the complete Weil matrix
at any fixed overlap `c > 0` is positive definite for all sufficiently large horizons. -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix tiltedUnitSpline c N).PosDef :=
  eventually_tiltedUnitSpline_completeWeilMatrix_posDef_of_quasimodes hc fun _ hm =>
    tendsto_completeWeilMatrix_ramanujan_quasimode_norm contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm

/-- **The macroscopic overlap `c = 3/2`.** -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_three_halves :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix tiltedUnitSpline (3 / 2) N).PosDef :=
  eventually_tiltedUnitSpline_completeWeilMatrix_posDef (by norm_num)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
