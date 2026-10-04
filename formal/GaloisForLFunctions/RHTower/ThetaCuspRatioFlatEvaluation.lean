import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFlatness
import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinitySlope

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology
open RHTower.ThetaCuspModularRatio


def actualBase (x : ℝ) : Coord → ℂ :=
  basePoint (((k x)⁻¹:ℝ):ℂ) ((kineticGap x:ℝ):ℂ)
    ((k x*(1-3*J x/u x):ℝ):ℂ)

def axisBase (x : ℝ) : Coord → ℂ := basePoint (((k x)⁻¹:ℝ):ℂ) 0 0

theorem actualBase_coord_tendsto (i : Coord) :
    Tendsto (fun x => actualBase x i) atTop (𝓝 0) := by
  have hc := Complex.continuous_ofReal.tendsto (0:ℝ)
  cases i
  · simpa [actualBase,basePoint,Function.comp_def] using hc.comp inverse_k_tendsto_zero
  · have hr : Tendsto kineticGap atTop (𝓝 0) := by
      simpa using kineticGap_superpolynomialDecay 0
    simpa [actualBase,basePoint,Function.comp_def] using hc.comp hr
  · have ht : Tendsto (fun x => k x*(1-3*J x/u x)) atTop (𝓝 0) := by
      simpa using compactifiedDeficit_superpolynomialDecay 0
    simpa [actualBase,basePoint,Function.comp_def] using hc.comp ht

theorem axisBase_coord_tendsto (i : Coord) :
    Tendsto (fun x => axisBase x i) atTop (𝓝 0) := by
  have hc := Complex.continuous_ofReal.tendsto (0:ℝ)
  cases i
  · simpa [axisBase,basePoint,Function.comp_def] using hc.comp inverse_k_tendsto_zero
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds

theorem axisBase_eval_tendsto (P : Poly) :
    Tendsto (fun x => eval (axisBase x) P) atTop (𝓝 (eval (basePoint 0 0 0) P)) := by
  have hb : Tendsto axisBase atTop (𝓝 (basePoint 0 0 0)) := by
    apply tendsto_pi_nhds.2
    intro i
    cases i <;> simpa only [basePoint] using axisBase_coord_tendsto _
  exact (GaloisForLFunctions.HTGeometry.contDiff_mvPolynomial_eval P).continuous.tendsto
    (basePoint 0 0 0) |>.comp hb

theorem coordinateDifference_flat (i : Coord) (n : ℕ) :
    Tendsto (fun x => (k x:ℂ)^n*(actualBase x i-axisBase x i)) atTop (𝓝 0) := by
  have hc := Complex.continuous_ofReal.tendsto (0:ℝ)
  cases i
  · simpa [actualBase,axisBase,basePoint,Function.comp_def] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0))
  · simpa [actualBase,axisBase,basePoint,Function.comp_def] using hc.comp (kineticGap_superpolynomialDecay n)
  · simpa [actualBase,axisBase,basePoint,Function.comp_def] using hc.comp (compactifiedDeficit_superpolynomialDecay n)

/-- Every polynomial source observable differs from its boundary axis by an all-order flat term. -/
theorem actual_axis_polynomial_flat (P : Poly) :
    Asymptotics.SuperpolynomialDecay atTop (fun x => (k x:ℂ))
      (fun x => eval (actualBase x) P-eval (axisBase x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro n
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0))
  | add p q hp hq =>
    intro n
    convert (hp n).add (hq n) using 1
    · funext x
      simp only [map_add]
      ring
    · simp
  | mul_X p i hp =>
    intro n
    have h1 := (hp n).mul (actualBase_coord_tendsto i)
    have h2 := (axisBase_eval_tendsto p).mul (coordinateDifference_flat i n)
    convert h1.add h2 using 1
    · funext x
      simp only [map_mul,eval_X]
      ring
    · simp

end
end HTGeometry.ThetaRatioInfinity
