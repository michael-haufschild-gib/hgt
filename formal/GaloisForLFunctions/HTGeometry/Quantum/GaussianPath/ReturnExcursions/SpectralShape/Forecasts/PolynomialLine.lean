import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.MomentPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel

/-! # The physical skewness constraint on one Gaussian line -/

open MeasureTheory ProbabilityTheory Polynomial Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
noncomputable section

/-- At fixed exterior fields only the leading coefficient on the chosen line
enters the sublevel bound. -/
theorem line_sublevel {n : ℕ} (c : ℝ) (y v : PathShell n) {r : ℝ} (hr : 0<r)
    (hv' : 2/3≤|skewConstraint c v|) :
    gaussianReal 0 1 {t : ℝ | |skewConstraint c (y+t • v)|<(2/3)*r^6}≤ENNReal.ofReal (12*r) := by
  have hdir : skewConstraint c v≠0 := abs_pos.mp ((by norm_num : (0:ℝ)<2/3).trans_le hv')
  obtain ⟨P,hd,hc,he⟩ := constraint_polynomial c y v
  have hcoeff : P.coeff 6≠0 := hc.trans_ne (Complex.ofReal_ne_zero.mpr hdir)
  have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hd hcoeff
  have hl : P.leadingCoeff=(skewConstraint c v:ℂ) := by rw [leadingCoeff,hdeg,hc]
  have hsub := gaussian_polynomial_sublevel P r hr.le
  simp only [hl,hdeg,Complex.norm_real,Real.norm_eq_abs,he,Nat.cast_ofNat] at hsub
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hsub.trans_eq (by ring))
  intro t ht
  exact lt_of_lt_of_le (show |skewConstraint c (y+t • v)|<(2/3)*r^6 from ht)
    (mul_le_mul_of_nonneg_right hv' (pow_nonneg hr.le 6))

#print axioms line_sublevel
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
