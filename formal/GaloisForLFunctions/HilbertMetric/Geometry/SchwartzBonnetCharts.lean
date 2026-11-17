import GaloisForLFunctions.HilbertMetric.Geometry.SeparableSchwartzHessian
import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzInversion
import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzRadius

/-!
# Compatible smooth support charts with a positive nonscalar radius matrix

The explicit reciprocal-cosh potential is Schwartz and has no scalar
Euclidean Hessian. The Bonnet transform preserves this absence while an
explicit Schwartz-seminorm scale makes its radius matrix positive.
Complex inversion supplies the smooth chart at infinity, flat to every order.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.SchwartzBonnetCharts
open GaloisForLFunctions.HTGeometry.GaussBonnet
open SeparableHessian BonnetSupport SchwartzRadius SchwartzInversion
noncomputable section

/-- The explicit planar potential in complex coordinates. -/
def complexPotential : SchwartzMap ℂ ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ Complex.equivRealProdCLM dampedSeedSchwartz

theorem complexPotential_apply (z : ℂ) : complexPotential z = dampedSeed z.re z.im := by
  change dampedSeedSchwartz (z.re, z.im) = _
  exact dampedSeedSchwartz_apply _

/-- A fixed positive scale computed from the actual explicit Schwartz potential. -/
def amplitude : ℝ := positiveScale dampedSeedSchwartz

theorem amplitude_pos : 0 < amplitude := positiveScale_pos _

def south : ℝ × ℝ → ℝ := support dampedSeedSchwartz amplitude

def north : ℂ → ℝ := northSupport complexPotential amplitude

theorem south_smooth : ContDiff ℝ ∞ south :=
  support_smooth (dampedSeedSchwartz.smooth ⊤) amplitude

theorem north_smooth : ContDiff ℝ ∞ north := northSupport_contDiff _ _

theorem south_eq_complex (z : ℂ) :
    south (z.re, z.im) = southSupport complexPotential amplitude z := by
  simp only [south, support, inverseDenominator, southSupport, denominator,
    complexPotential_apply, dampedSeedSchwartz_apply, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The actual formulas agree under the stereographic inversion transition. -/
theorem chart_overlap {z : ℂ} (hz : z ≠ 0) :
    south ((z⁻¹).re, (z⁻¹).im) = north z := by
  rw [south_eq_complex]
  exact support_chart_overlap complexPotential amplitude hz

/-- Every derivative of the correction vanishes at the missing pole. -/
theorem north_correction_flat (n : ℕ) :
    iteratedFDeriv ℝ n (northCorrection complexPotential) 0 = 0 :=
  northCorrection_iteratedFDeriv_zero _ n

theorem north_zero : north 0 = 1 := by
  simp [north, northSupport, northCorrection, kelvin_zero]

private theorem hessian_not_scalar (p : ℝ × ℝ) :
    ¬ (px (px dampedSeedSchwartz) p = py (py dampedSeedSchwartz) p ∧
      py (px dampedSeedSchwartz) p = 0) := by
  have hf : ContDiff ℝ ∞ (dampedSeedSchwartz : ℝ × ℝ → ℝ) := dampedSeedSchwartz.smooth ⊤
  have hx : px dampedSeedSchwartz =
      (fun q => deriv (fun t => dampedSeedSchwartz (t, q.2)) q.1) :=
    funext (fun q => (hasDerivAt_px hf q.1 q.2).deriv.symm)
  have hy : py dampedSeedSchwartz =
      (fun q => deriv (fun t => dampedSeedSchwartz (q.1, t)) q.2) :=
    funext (fun q => (hasDerivAt_py hf q.1 q.2).deriv.symm)
  have hxx := (hasDerivAt_px (contDiff_px hf) p.1 p.2).deriv
  have hyy := (hasDerivAt_py (contDiff_py hf) p.1 p.2).deriv
  have hxy := (hasDerivAt_py (contDiff_px hf) p.1 p.2).deriv
  conv_lhs at hxx => rw [hx]
  conv_lhs at hxy => rw [hx]
  conv_lhs at hyy => rw [hy]
  intro h
  have hc :
      deriv (deriv (fun t => dampedSeed t p.2)) p.1 =
        deriv (deriv (dampedSeed p.1)) p.2 ∧
      deriv (fun t => deriv (fun s => dampedSeed s t) p.1) p.2 = 0 := by
    simpa only [dampedSeedSchwartz_apply] using
      And.intro (hxx.trans (h.1.trans hyy.symm)) (hxy.trans h.2)
  exact dampedSeed_hessian_nowhere_scalar p.1 p.2 hc

/-- No finite chart point has a scalar radius matrix. -/
theorem south_radius_not_scalar (p : ℝ × ℝ) :
    ¬ (radiusXX south p = radiusYY south p ∧ radiusXY south p = 0) := by
  intro h
  exact hessian_not_scalar p ((radius_scalar_iff (dampedSeedSchwartz.smooth ⊤)
    amplitude_pos.ne' p).mp h)

/-- The radius matrix is uniformly positive at every finite chart point. -/
theorem south_radius_positive (p : ℝ × ℝ) (a b : ℝ) :
    (a ^ 2 + b ^ 2) / 2 ≤ radiusXX south p * a ^ 2 +
      2 * radiusXY south p * a * b + radiusYY south p * b ^ 2 :=
  radius_uniform_positive dampedSeedSchwartz p a b

#print axioms chart_overlap
#print axioms north_correction_flat
#print axioms south_radius_not_scalar
#print axioms south_radius_positive
end
end GaloisForLFunctions.HilbertMetric.Geometry.SchwartzBonnetCharts
