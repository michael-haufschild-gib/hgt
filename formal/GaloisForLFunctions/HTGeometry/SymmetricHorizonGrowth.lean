import GaloisForLFunctions.HTGeometry.HorizonGrowthCoefficient

/-! Two-sign energy estimates retain one original solution while crossing the imaginary frequency axis. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def symmetricHorizonGrowthCoefficient (w x y : ℂ) (A B : ℝ) : ℝ :=
  max (horizonGrowthCoefficient w x y A B) (horizonGrowthCoefficient (-w) x y A B)

/-- The symmetric bound varies continuously off zero frequency. -/
theorem symmetricHorizonGrowthCoefficient_continuousAt (w x y : ℂ) (A B : ℝ) (hw : w ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ × ℂ × ℝ × ℝ =>
      symmetricHorizonGrowthCoefficient p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (w,x,y,A,B) := by
  unfold symmetricHorizonGrowthCoefficient horizonGrowthCoefficient
  simp only [norm_neg,Complex.neg_re]
  fun_prop (disch := positivity)

/-- Both signs of the free frequency bound the same original forced solution.
Only the estimate changes sign; the response and original forcing remain fixed. -/
theorem forcedSecondOrder_horizon_bound_symmetric (w : ℂ) (hw : w ≠ 0)
    (U V p f : ℝ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hU : ∀ t < 0, HasDerivAt U (V t) t)
    (hV : ∀ t < 0, HasDerivAt V (w^2*U t+p t*U t-f t) t)
    (hp : ∀ t < 0, ‖p t‖ ≤ A*Real.exp (2*t))
    (hf : ∀ t < 0, ‖f t‖ ≤ B*Real.exp ((w.re+2)*t)) (t : ℝ) (ht : t < 0) :
    ‖U t‖ ≤ symmetricHorizonGrowthCoefficient w (U (-1)) (V (-1)) A B*Real.exp (-|w.re| *t) := by
  by_cases hwr : w.re ≤ 0
  · have h := forcedSecondOrder_horizon_bound_explicit w hw hwr U V p f A B hA hB hU hV hp hf t ht
    rw [abs_of_nonpos hwr,neg_neg]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hwr' : 0 < w.re := lt_of_not_ge hwr
    have hV' (r : ℝ) (hr : r < 0) : HasDerivAt V ((-w)^2*U r+p r*U r-f r) r := by
      simpa only [neg_sq] using hV r hr
    have hf' (r : ℝ) (hr : r < 0) : ‖f r‖ ≤ B*Real.exp (((-w).re+2)*r) := by
      apply (hf r hr).trans
      apply mul_le_mul_of_nonneg_left ?_ hB
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_right (by simp only [Complex.neg_re]; linarith) hr.le
    have h := forcedSecondOrder_horizon_bound_explicit (-w) (neg_ne_zero.mpr hw)
      (by simp only [Complex.neg_re]; linarith) U V p f A B hA hB hU hV' hp hf' t ht
    rw [abs_of_pos hwr']
    simpa only [Complex.neg_re,symmetricHorizonGrowthCoefficient] using h.trans
      (mul_le_mul_of_nonneg_right (le_max_right (horizonGrowthCoefficient w (U (-1)) (V (-1)) A B) _) (Real.exp_pos _).le)

end
end GaloisForLFunctions.HTGeometry
