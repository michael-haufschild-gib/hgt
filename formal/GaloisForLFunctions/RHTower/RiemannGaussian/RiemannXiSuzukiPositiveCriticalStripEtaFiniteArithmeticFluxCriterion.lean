import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteArithmeticFlux

/-!
# Source criterion and obstruction for finite paired-eta heat flux

The diagonal construction already supplies literal finite paired-eta
Dirichlet-polynomial fluxes converging to the complete upper-spectral
boundary-heat detector.  This module closes that interface: convergence of
this one arithmetic sequence to zero is equivalent to RH.  Conversely, an
off-axis zero forces the same literal finite arithmetic flux to be strictly
positive at all sufficiently late stages.

Thus a prospective arithmetic ``zero-winding'' argument has one exact target:
it must make this concrete finite flux tend to zero.  It cannot use finite
truncation alone, since a non-RH divisor produces an eventual positive source
response.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit diagonal sequence of finite paired-eta arithmetic fluxes
vanishes precisely when there are no upper spectral zeros. -/
theorem tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFluxDiagonal_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
          x tau (n : ℝ)
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
            (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n))
      atTop (nhds 0) ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    have hlimit :=
      tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFluxDiagonal x htau
    have hscaled : 2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      tendsto_nhds_unique hlimit hzero
    have hfactor : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hheat : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (mul_eq_zero.mp hscaled).resolve_left hfactor
    exact (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh x htau).mp hheat
  · intro hRH
    have hheat : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh x htau).mpr hRH
    simpa [hheat] using
      (tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFluxDiagonal x htau)

/-- If an off-axis zero exists, the literal diagonal finite arithmetic flux is
strictly positive at every sufficiently late stage. -/
theorem eventually_pos_pairedEtaBoundaryHeatFiniteArithmeticRadialFluxDiagonal_of_not_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) (hRH : ¬ RiemannHypothesis) :
    ∀ᶠ n : ℕ in atTop,
      0 < pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
        x tau (n : ℝ)
          (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
          (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n) := by
  obtain ⟨w, hwzero, hwupper⟩ :=
    exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
  obtain ⟨rho, rfl⟩ :=
    (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
  have hheat : 0 < riemannXiUpperHyperbolicBoundaryHeatTotal x tau :=
    riemannXiUpperHyperbolicBoundaryHeatTotal_pos_of_upper_zero
      x htau rho hwupper
  have hlimit :=
    tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFluxDiagonal x htau
  have htarget : 0 < 2 * Real.pi *
      riemannXiUpperHyperbolicBoundaryHeatTotal x tau := by positivity
  exact hlimit.eventually (eventually_gt_nhds htarget)

end

end RiemannGaussian
