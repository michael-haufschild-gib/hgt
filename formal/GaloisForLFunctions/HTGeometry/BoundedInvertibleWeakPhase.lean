import GaloisForLFunctions.HTGeometry.BoundedInvertibleLogHardy
import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiWeakPhase
import GaloisForLFunctions.HTGeometry.SmirnovToeplitzKernel
import GaloisForLFunctions.HTGeometry.BoundedPhaseSmirnovToeplitz

/-!
# Weak phase of a bounded invertible analytic multiplier

The Hardy boundary of the normalized analytic logarithm supplies an actual real phase lift of the
multiplier's phase-reflection symbol.  Its Cayley pullback is `L²` for standard Cauchy measure, so
the lift has the exact little weak-`L¹` tail used in the Makarov--Poltoratski endpoint.
-/

open Complex Filter Metric Real Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem conj_mul_exp_div_self_eq_exp_phase
    {c w : ℂ} (hc : c ≠ 0) :
    (starRingEnd ℂ) (c * Complex.exp w) / (c * Complex.exp w) =
      Complex.exp (-2 * I * (((c.arg + w.im : ℝ) : ℂ))) := by
  have hcc : (starRingEnd ℂ) c ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hc
  have harg := exp_two_mul_I_mul_arg_eq_div_conj hc
  have hconjExp : (starRingEnd ℂ) (Complex.exp w) =
      Complex.exp ((starRingEnd ℂ) w) := by
    rw [← Complex.exp_conj]
  rw [map_mul, hconjExp]
  have hcphase : (starRingEnd ℂ) c / c =
      Complex.exp (-2 * I * (c.arg : ℂ)) := by
    rw [show (starRingEnd ℂ) c / c = (c / (starRingEnd ℂ) c)⁻¹ by
      field_simp]
    rw [← harg, ← Complex.exp_neg]
    congr 1
    ring
  rw [show (starRingEnd ℂ) c * Complex.exp ((starRingEnd ℂ) w) /
      (c * Complex.exp w) =
      ((starRingEnd ℂ) c / c) *
        (Complex.exp ((starRingEnd ℂ) w) / Complex.exp w) by
          field_simp]
  rw [hcphase, ← Complex.exp_sub, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Actual real phase lift of the phase-reflection symbol, obtained from the Hardy boundary of the
normalized analytic logarithm. -/
def BoundedInvertibleLog.linePhase {phi : DiskMultiplier}
    (L : BoundedInvertibleLog phi) (x : ℝ) : ℝ :=
  (phi.fn 0).arg +
    ((hardyDiskBoundary L.hardy : Circle → ℂ) (circleCayley x)).im

theorem BoundedInvertibleLog.lineBoundary_exp_ae
    {phi : DiskMultiplier} (L : BoundedInvertibleLog phi) :
    diskMultiplierLineBoundary phi =ᵐ[volume]
      fun x => phi.fn 0 * Complex.exp
        ((hardyDiskBoundary L.hardy : Circle → ℂ) (circleCayley x)) := by
  have hweighted := L.boundary_exp_ae.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hvolume := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweighted
  filter_upwards [diskMultiplierLineBoundary_ae phi, hvolume] with x hline hboundary
  rw [hline]
  simpa only [Function.comp_apply] using hboundary

/-- The actual phase-reflection symbol agrees a.e. with the exponential of the logarithmic phase
lift. -/
theorem BoundedInvertibleLog.phaseReflection_eq_exp_ae
    {phi : DiskMultiplier} (L : BoundedInvertibleLog phi) :
    diskMultiplierPhaseReflectionSymbol phi =ᵐ[volume]
      fun x => Complex.exp (-2 * I * ((L.linePhase x : ℝ) : ℂ)) := by
  filter_upwards [L.lineBoundary_exp_ae] with x hx
  have hne : diskMultiplierLineBoundary phi x ≠ 0 := by
    rw [hx]
    exact mul_ne_zero L.center_ne_zero (Complex.exp_ne_zero _)
  rw [diskMultiplierPhaseReflectionSymbol, if_neg hne, hx]
  exact conj_mul_exp_div_self_eq_exp_phase L.center_ne_zero

/-- The actual line phase of a bounded invertible multiplier belongs to `L²` for standard Cauchy
measure. -/
theorem BoundedInvertibleLog.memLp_linePhase
    {phi : DiskMultiplier} (L : BoundedInvertibleLog phi) :
    MemLp L.linePhase 2 (ProbabilityTheory.cauchyMeasure 0 1) := by
  let F : Lp ℂ 2 circleLebesgue := hardyDiskBoundary L.hardy
  have himCircle : MemLp (fun z : Circle => ((F : Circle → ℂ) z).im)
      2 circleLebesgue := by
    apply (Lp.memLp F).mono
    · exact Complex.continuous_im.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable F)
    · filter_upwards with z
      simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm ((F : Circle → ℂ) z)
  have himLine : MemLp
      (fun x : ℝ => ((F : Circle → ℂ) (circleCayley x)).im)
      2 (ProbabilityTheory.cauchyMeasure 0 1) := by
    simpa [Function.comp_def] using
      himCircle.comp_measurePreserving circleCayley_measurePreserving
  have hconst : MemLp (fun _x : ℝ => (phi.fn 0).arg)
      2 (ProbabilityTheory.cauchyMeasure 0 1) := by
    apply MemLp.of_bound measurable_const.aestronglyMeasurable |(phi.fn 0).arg|
    filter_upwards with x
    simp [Real.norm_eq_abs]
  have hadd := hconst.add himLine
  change MemLp ((fun _x : ℝ => (phi.fn 0).arg) +
      (fun x => ((F : Circle → ℂ) (circleCayley x)).im))
    2 (ProbabilityTheory.cauchyMeasure 0 1)
  exact hadd

/-- Exact Makarov--Poltoratski weak-phase witness for a bounded invertible multiplier's phase
reflection. -/
noncomputable def BoundedInvertibleLog.phaseReflectionWeakWitness
    {phi : DiskMultiplier} (L : BoundedInvertibleLog phi) :
    SmirnovToeplitzWeakPhaseWitness (fun x => -2 * L.linePhase x) where
  innerPhase := 0
  outerHilbertPhase := fun x => -2 * L.linePhase x
  innerPhase_monotone := monotone_const
  phase_balance := by intro x; simp
  outerHilbertPhase_weakL1LittleO := by
    have hmem := L.memLp_linePhase.const_mul (-2)
    have hint := hmem.integrable_norm_rpow (by norm_num) (by norm_num)
    apply poissonWeakL1LittleO_of_integrable_sq
    simpa [Real.norm_eq_abs] using hint

end GaloisForLFunctions.HTGeometry
