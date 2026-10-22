import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioActualSlopeTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioScaledDriftFactor

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology
open RHTower.ThetaCuspModularRatio

def terminalBase (x : ℝ) : Coord → ℂ := basePoint 9 (k x:ℂ) (1/3)

-- Denominator clearing transfers compact flatness to the original source
-- coordinates, even though their kinetic coordinate is unbounded.
theorem actual_terminal_polynomial_flat (P : Poly) :
    Asymptotics.SuperpolynomialDecay atTop (fun x => (k x:ℂ))
      (fun x => eval (actualSquarePoint x) P-eval (terminalBase x) P) := by
  obtain ⟨m,Q,hQ⟩ := sourcePolynomial_regularization P
  intro n
  have hf := actual_axis_polynomial_flat Q (n+m)
  apply hf.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  have hk : (k x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [k_gt hx])
  have ha := hQ (k x:ℂ)⁻¹ (kineticGap x:ℂ)
    ((k x*(1-3*J x/u x):ℝ):ℂ) (inv_ne_zero hk)
  rw [actual_sourcePoint hx] at ha
  have ha' : ((k x:ℂ)⁻¹)^m*eval (actualSquarePoint x) P=
      eval (actualBase x) Q := by
    simpa only [actualBase,Complex.ofReal_inv] using ha
  have hz := hQ (k x:ℂ)⁻¹ 0 0 (inv_ne_zero hk)
  have hb : sourcePoint (k x:ℂ)⁻¹ 0 0=terminalBase x := by
    funext i
    cases i <;> simp [sourcePoint,terminalBase,basePoint]
  rw [hb] at hz
  have hz' : ((k x:ℂ)⁻¹)^m*eval (terminalBase x) P=
      eval (axisBase x) Q := by
    simpa only [axisBase,Complex.ofReal_inv] using hz
  rw [←ha',←hz',pow_add]
  have hm : (k x:ℂ)^m*((k x:ℂ)⁻¹)^m=1 := by
    rw [←mul_pow,mul_inv_cancel₀ hk,one_pow]
  calc
    _ = (k x:ℂ)^n*((k x:ℂ)^m*((k x:ℂ)⁻¹)^m)*
      (eval (actualSquarePoint x) P-eval (terminalBase x) P) := by ring
    _ = _ := by rw [hm,mul_one]

end
end HTGeometry.ThetaRatioInfinity
