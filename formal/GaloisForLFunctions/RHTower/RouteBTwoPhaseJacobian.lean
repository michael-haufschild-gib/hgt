/-
The two-phase map, its Jacobian, and the concrete transversal small-ball.

The map `Φ(w) = c + A·e^{i·w.re} + B·e^{i·w.im}` — two independent circle phases carried by the real
and imaginary parts of `w ∈ ℂ` — has real Jacobian determinant `A·B·sin(w.im − w.re)`.  So the two
phases are transversal (`|det| > 0`) exactly off the diagonal `w.im ≡ w.re (mod π)`, where the two
velocity vectors align.  On any region where `Φ` is injective and `|sin(w.im − w.re)| ≥ δ`, the
transversal small-ball law gives the genuine quadratic rate

    volume{ w ∈ region : ‖Φ w‖ ≤ t } ≤ π t² / (|A|·|B|·δ).

This fires `transversal_smallball` on a named pair: two independent phases already produce the `t²`
anti-concentration a single phase cannot.
-/
import GaloisForLFunctions.RHTower.RouteBTransversal

open Complex ContinuousLinearMap MeasureTheory

namespace RHTower
namespace Sublevel

/-- **The real determinant of `h ↦ u·h.re + v·h.im`.**  In the `{1, I}` real basis of `ℂ` this map
has matrix `[[u.re, v.re], [u.im, v.im]]`, so its determinant is `u.re·v.im − u.im·v.re`. -/
theorem smulRight_add_det (u v : ℂ) :
    (reCLM.smulRight u + imCLM.smulRight v).det = u.re * v.im - u.im * v.re := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.basisOneI]
  ring

/-- Fréchet derivative of a single amplitude-scaled circle phase `w ↦ A·e^{i·w.re}`. -/
theorem hasFDerivAt_phase_re (A : ℂ) (w : ℂ) :
    HasFDerivAt (fun z : ℂ => A * Complex.exp ((z.re : ℂ) * Complex.I))
      (reCLM.smulRight (A * Complex.I * Complex.exp ((w.re : ℂ) * Complex.I))) w := by
  have h1 : HasFDerivAt (fun z : ℂ => (z.re : ℂ) * Complex.I) (reCLM.smulRight Complex.I) w := by
    refine ((reCLM.smulRight Complex.I).hasFDerivAt (x := w)).congr_of_eventuallyEq ?_
    filter_upwards with z
    simp [ContinuousLinearMap.smulRight_apply, Complex.real_smul]
  refine ((h1.cexp).const_mul A).congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Complex.real_smul]
  ring

/-- Fréchet derivative of a single amplitude-scaled circle phase `w ↦ B·e^{i·w.im}`. -/
theorem hasFDerivAt_phase_im (B : ℂ) (w : ℂ) :
    HasFDerivAt (fun z : ℂ => B * Complex.exp ((z.im : ℂ) * Complex.I))
      (imCLM.smulRight (B * Complex.I * Complex.exp ((w.im : ℂ) * Complex.I))) w := by
  have h1 : HasFDerivAt (fun z : ℂ => (z.im : ℂ) * Complex.I) (imCLM.smulRight Complex.I) w := by
    refine ((imCLM.smulRight Complex.I).hasFDerivAt (x := w)).congr_of_eventuallyEq ?_
    filter_upwards with z
    simp [ContinuousLinearMap.smulRight_apply, Complex.real_smul]
  refine ((h1.cexp).const_mul B).congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Complex.real_smul]
  ring

/-- The two-phase map `Φ(w) = c + A·e^{i·w.re} + B·e^{i·w.im}`. -/
noncomputable def twoPhaseMap (A B : ℝ) (c : ℂ) (w : ℂ) : ℂ :=
  c + (A : ℂ) * Complex.exp ((w.re : ℂ) * Complex.I)
    + (B : ℂ) * Complex.exp ((w.im : ℂ) * Complex.I)

/-- The Fréchet derivative of the two-phase map. -/
noncomputable def twoPhaseDeriv (A B : ℝ) (w : ℂ) : ℂ →L[ℝ] ℂ :=
  reCLM.smulRight ((A : ℂ) * Complex.I * Complex.exp ((w.re : ℂ) * Complex.I))
    + imCLM.smulRight ((B : ℂ) * Complex.I * Complex.exp ((w.im : ℂ) * Complex.I))

theorem hasFDerivAt_twoPhaseMap (A B : ℝ) (c w : ℂ) :
    HasFDerivAt (twoPhaseMap A B c) (twoPhaseDeriv A B w) w := by
  refine (((hasFDerivAt_const c w).add (hasFDerivAt_phase_re (A : ℂ) w)).add
    (hasFDerivAt_phase_im (B : ℂ) w)).congr_fderiv ?_
  rw [twoPhaseDeriv, zero_add]

theorem continuous_twoPhaseMap (A B : ℝ) (c : ℂ) : Continuous (twoPhaseMap A B c) := by
  unfold twoPhaseMap
  fun_prop

/-- **The two-phase Jacobian determinant.**  `det Φ'(w) = A·B·sin(w.im − w.re)` — transversal exactly
off the diagonal `w.im ≡ w.re (mod π)`. -/
theorem twoPhaseDeriv_det (A B : ℝ) (w : ℂ) :
    (twoPhaseDeriv A B w).det = A * B * Real.sin (w.im - w.re) := by
  rw [twoPhaseDeriv, smulRight_add_det]
  simp only [Complex.exp_mul_I, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  rw [Real.sin_sub]
  ring

/-- **The concrete two-phase transversal small-ball.**  On a measurable region where the two-phase map
is injective and the two phases stay transversal (`|sin(w.im − w.re)| ≥ δ`), the level set at scale
`t` has area at most `π t² / (|A|·|B|·δ)` — the genuine quadratic anti-concentration of an independent
phase pair. -/
theorem twoPhase_transversal_smallball {A B δ t : ℝ} {c : ℂ} {region : Set ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hδ : 0 < δ) (hreg : MeasurableSet region)
    (hinj : Set.InjOn (twoPhaseMap A B c) region)
    (hsin : ∀ w ∈ region, δ ≤ |Real.sin (w.im - w.re)|) (ht : 0 ≤ t) :
    volume (region ∩ {w : ℂ | ‖twoPhaseMap A B c w‖ ≤ t})
      ≤ ENNReal.ofReal (Real.pi * t ^ 2 / (|A| * |B| * δ)) := by
  have hAB : (0 : ℝ) < |A| * |B| * δ := by
    have : (0 : ℝ) < |A| := abs_pos.mpr hA
    have : (0 : ℝ) < |B| := abs_pos.mpr hB
    positivity
  refine transversal_smallball (Φ' := twoPhaseDeriv A B) hreg
    (continuous_twoPhaseMap A B c).measurable
    (fun w _ => (hasFDerivAt_twoPhaseMap A B c w).hasFDerivWithinAt) hinj hAB ?_ ht
  intro w hw
  rw [twoPhaseDeriv_det, abs_mul, abs_mul]
  have hsinw := hsin w hw
  have hAB0 : (0 : ℝ) ≤ |A| * |B| := by positivity
  calc |A| * |B| * δ ≤ |A| * |B| * |Real.sin (w.im - w.re)| :=
        mul_le_mul_of_nonneg_left hsinw hAB0
    _ = |A| * |B| * |Real.sin (w.im - w.re)| := rfl

end Sublevel
end RHTower
