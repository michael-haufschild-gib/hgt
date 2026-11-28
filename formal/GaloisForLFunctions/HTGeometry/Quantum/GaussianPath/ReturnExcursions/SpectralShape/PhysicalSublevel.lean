import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.GaussianDirection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.PauliDirections
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.PolynomialLine

/-! # A uniform spectral-shape price under the original Gaussian disorder -/

open MeasureTheory ProbabilityTheory Polynomial Set WithLp
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields
noncomputable section

private theorem continuous_skew (n : ℕ) (c : ℝ) :
    Continuous (skewConstraint (n:=n) c) := by
  have hH : Continuous (fun h : PathShell n => pathHamiltonian h) :=
    (pathHamiltonianLM n).continuous_of_finiteDimensional
  unfold skewConstraint thirdMoment Matrix.trace
  fun_prop

/-- For the physical path Hamiltonian, a specified squared skewness has a uniform
sixth-root small-ball bound. Neither the direction nor the polynomial degree
depends on the sampled Hamiltonian. -/
theorem physical_skew_price (n : ℕ) (c r : ℝ) (hr : 0<r) :
    (fieldLaw n).real {h | |skewConstraint c (toLp 2 h)|<(2/3)*r^6} ≤ 12*r := by
  let S := {h : PathShell n | |skewConstraint c h|<(2/3)*r^6}
  have hS : MeasurableSet S := measurableSet_lt (continuous_skew n c).abs.measurable measurable_const
  obtain ⟨v,hv,hv'⟩ := uniform_direction n c
  let i : PathLabel n := .inl (0,0)
  have hμ := gaussian_line_price i v hv S hS (ENNReal.ofReal (12*r)) (by
    intro y
    exact line_sublevel c y v hr hv')
  have hT : MeasurePreserving (toLp 2 : Coeff n → PathShell n) (fieldLaw n) (stdGaussian (PathShell n)) :=
    ⟨(MeasurableEquiv.toLp 2 (Coeff n)).measurable,map_pi_eq_stdGaussian⟩
  change (fieldLaw n).real (toLp 2 ⁻¹' S)≤_
  rw [hT.measureReal_preimage hS.nullMeasurableSet]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ).trans_eq (ENNReal.toReal_ofReal (by positivity))

#print axioms physical_skew_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
