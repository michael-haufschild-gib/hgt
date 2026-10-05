import GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderCoordinate
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Critical moving-shell phase correction

The exact phase error yields a scaled exponential difference. A global
unit-circle Lipschitz estimate retains the polynomial domination needed for
the first-order integral transfer.
-/

open Real Complex Set Filter Topology

namespace RHTower
noncomputable section

private theorem tendsto_scaled_comp {a z : ℕ → ℂ} {w d c : ℂ} {f : ℂ → ℂ}
    (hf : HasDerivAt f d w) (hz : Tendsto z atTop (𝓝 w))
    (ha : Tendsto (fun n => a n*(z n-w)) atTop (𝓝 c)) :
    Tendsto (fun n => a n*(f (z n)-f w)) atTop (𝓝 (d*c)) := by
  have hq := hf.continuousAt_div.tendsto.comp hz
  convert hq.mul ha using 1
  · funext n
    by_cases he : z n = w
    · simp [he]
    · simp [he]
      field_simp [sub_ne_zero.mpr he]
  · simp

theorem norm_thetaMovingUnitPhase_sub_le (x y : ℝ) :
    ‖Complex.exp (Complex.I*(y : ℂ))-Complex.exp (Complex.I*(x : ℂ))‖ ≤ |y-x| := by
  let f : ℝ → ℂ := fun t => Complex.exp (Complex.I*(t : ℂ))
  let f' : ℝ → ℂ := fun t => Complex.exp (Complex.I*(t : ℂ))*Complex.I
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    have hi : HasDerivAt (fun w : ℂ => Complex.I*w) Complex.I (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).const_mul Complex.I
    have hc := (Complex.hasDerivAt_exp (Complex.I*(t : ℂ))).comp (t : ℂ) hi
    simpa [f, f', Function.comp_def] using! hc.comp_ofReal
  have hb (t : ℝ) : ‖f' t‖ ≤ 1 := by simp [f', Complex.norm_exp]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ)) (x := x) (y := y)
    (fun t _ => (hf t).hasDerivWithinAt) (fun t _ => hb t) convex_univ
    (mem_univ x) (mem_univ y)
  simpa [f, Real.norm_eq_abs] using h

def thetaMovingShellCriticalPhase (n : ℕ) (s u : ℝ) : ℝ :=
  (2*Real.pi+s/thetaMovingShellScale n)*thetaMovingShellGammaPhase n u-Real.pi*u

theorem tendsto_thetaMovingShellCriticalPhase (s u : ℝ) :
    Tendsto (fun n => thetaMovingShellCriticalPhase n s u) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => s/thetaMovingShellScale n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_thetaMovingShellScale
  have h := ((hs.const_add (2*Real.pi)).mul (tendsto_thetaMovingShellGammaPhase u)).sub_const
    (Real.pi*u)
  convert h using 1
  · rfl
  · ring

theorem tendsto_thetaMovingShellCriticalExp_firstOrder (s : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => (thetaMovingShellScale n : ℂ)*
      (Complex.exp (Complex.I*(thetaMovingShellCriticalPhase n s u : ℂ))-1)) atTop
      (𝓝 (Complex.I*((-Real.pi*u^2/2+s*u/2 : ℝ) : ℂ))) := by
  have hz := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_thetaMovingShellCriticalPhase s u)
  have hd := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_thetaMovingShellCriticalPhase_firstOrder s hu)
  have hscaled : Tendsto (fun n => (thetaMovingShellScale n : ℂ)*
      (Complex.I*(thetaMovingShellCriticalPhase n s u : ℂ)-0)) atTop
      (𝓝 (Complex.I*((-Real.pi*u^2/2+s*u/2 : ℝ) : ℂ))) := by
    convert hd.const_mul Complex.I using 1
    · funext n
      simp only [thetaMovingShellCriticalPhase, Function.comp_def]
      push_cast
      ring
  have hzero : Tendsto (fun n => Complex.I*(thetaMovingShellCriticalPhase n s u : ℂ))
      atTop (𝓝 0) := by simpa [Function.comp_def] using hz.const_mul Complex.I
  simpa using tendsto_scaled_comp (Complex.hasDerivAt_exp 0) hzero hscaled

theorem norm_thetaMovingShellCriticalExp_firstOrder_le (n : ℕ) (s : ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖(thetaMovingShellScale n : ℂ)*
      (Complex.exp (Complex.I*(thetaMovingShellCriticalPhase n s u : ℂ))-1)‖ ≤
      Real.pi*u^2/2+|s| * u/2 := by
  have ha := thetaMovingShellScale_pos n
  have hunit : ‖Complex.exp (Complex.I*(thetaMovingShellCriticalPhase n s u : ℂ))-1‖ ≤
      |thetaMovingShellCriticalPhase n s u| := by
    simpa using norm_thetaMovingUnitPhase_sub_le 0 (thetaMovingShellCriticalPhase n s u)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.le]
  calc
    thetaMovingShellScale n*‖Complex.exp (Complex.I*(thetaMovingShellCriticalPhase n s u : ℂ))-1‖
        ≤ thetaMovingShellScale n*|thetaMovingShellCriticalPhase n s u| :=
      mul_le_mul_of_nonneg_left hunit ha.le
    _ = |thetaMovingShellScale n*thetaMovingShellCriticalPhase n s u| := by
      rw [abs_mul, abs_of_nonneg ha.le]
    _ ≤ Real.pi*u^2/2+|s| * u/2 := abs_thetaMovingShellCriticalPhase_firstOrder_le n s hu

private theorem thetaMovingShellCriticalExp_factor (n : ℕ) (s u : ℝ) :
    Complex.exp (Complex.I*((2*Real.pi+s/thetaMovingShellScale n : ℝ) : ℂ)*
      (thetaMovingShellGammaPhase n u : ℂ)) =
    Complex.exp (Complex.I*((Real.pi*u : ℝ) : ℂ))*
      Complex.exp (Complex.I*(thetaMovingShellCriticalPhase n s u : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  unfold thetaMovingShellCriticalPhase
  push_cast
  ring

theorem tendsto_thetaMovingShellCriticalFourierPhase_firstOrder (s : ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => (thetaMovingShellScale n : ℂ)*
      (Complex.exp (Complex.I*((2*Real.pi+s/thetaMovingShellScale n : ℝ) : ℂ)*
        (thetaMovingShellGammaPhase n u : ℂ))-
      Complex.exp (Complex.I*((Real.pi*u : ℝ) : ℂ)))) atTop
      (𝓝 (Complex.exp (Complex.I*((Real.pi*u : ℝ) : ℂ))*
        (Complex.I*((-Real.pi*u^2/2+s*u/2 : ℝ) : ℂ)))) := by
  convert (tendsto_thetaMovingShellCriticalExp_firstOrder s hu).const_mul
    (Complex.exp (Complex.I*((Real.pi*u : ℝ) : ℂ))) using 1
  funext n
  rw [thetaMovingShellCriticalExp_factor]
  ring

theorem norm_thetaMovingShellCriticalFourierPhase_firstOrder_le (n : ℕ) (s : ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖(thetaMovingShellScale n : ℂ)*
      (Complex.exp (Complex.I*((2*Real.pi+s/thetaMovingShellScale n : ℝ) : ℂ)*
        (thetaMovingShellGammaPhase n u : ℂ))-
      Complex.exp (Complex.I*((Real.pi*u : ℝ) : ℂ)))‖ ≤ Real.pi*u^2/2+|s| * u/2 := by
  have heq : (thetaMovingShellScale n : ℂ)*
      (Complex.exp (Complex.I*((2*Real.pi+s/thetaMovingShellScale n : ℝ) : ℂ)*
        (thetaMovingShellGammaPhase n u : ℂ))-
      Complex.exp (Complex.I*((Real.pi*u : ℝ) : ℂ))) =
    Complex.exp (Complex.I*((Real.pi*u : ℝ) : ℂ))*
      ((thetaMovingShellScale n : ℂ)*
        (Complex.exp (Complex.I*(thetaMovingShellCriticalPhase n s u : ℂ))-1)) := by
    rw [thetaMovingShellCriticalExp_factor]
    ring
  rw [heq, norm_mul]
  have hn : ‖Complex.exp (Complex.I*((Real.pi*u : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  rw [hn, one_mul]
  exact norm_thetaMovingShellCriticalExp_firstOrder_le n s hu

end
end RHTower
