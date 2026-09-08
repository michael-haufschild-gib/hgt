import GaloisForLFunctions.HTGeometry.ForcedSecondOrderHorizonBound

/-! An explicit, continuous frequency-dependent coefficient for the actual horizon energy bound. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The bound depends only on the frequency, one interior solution jet, and the two forcing bounds. -/
def horizonGrowthCoefficient (w x y : ℂ) (A B : ℝ) : ℝ :=
  let E := ‖(Real.exp w.re:ℂ)*(y+w*x)‖^2+‖(Real.exp w.re:ℂ)*(y-w*x)‖^2
  max ((E+1)*Real.exp ((4*(A/(2*‖w‖))+2*B)/2))
    ((E+1)*Real.exp (-4*w.re+4*(A/(2*‖w‖))+2*B))/(2*‖w‖)

theorem horizonGrowthCoefficient_nonneg (w x y : ℂ) (A B : ℝ) :
    0 ≤ horizonGrowthCoefficient w x y A B := by unfold horizonGrowthCoefficient; positivity

/-- The actual energy coefficient varies continuously wherever the frequency is nonzero. -/
theorem horizonGrowthCoefficient_continuousAt (w x y : ℂ) (A B : ℝ) (hw : w ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ × ℂ × ℝ × ℝ =>
      horizonGrowthCoefficient p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (w,x,y,A,B) := by
  unfold horizonGrowthCoefficient
  fun_prop (disch := positivity)

/-- The whole-half-line bound retains its exact interior data rather than an arbitrary existential constant. -/
theorem forcedSecondOrder_horizon_bound_explicit (w : ℂ) (hw : w ≠ 0) (hwr : w.re ≤ 0)
    (U V p f : ℝ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hU : ∀ t < 0, HasDerivAt U (V t) t)
    (hV : ∀ t < 0, HasDerivAt V (w^2*U t+p t*U t-f t) t)
    (hp : ∀ t < 0, ‖p t‖ ≤ A*Real.exp (2*t))
    (hf : ∀ t < 0, ‖f t‖ ≤ B*Real.exp ((w.re+2)*t)) (t : ℝ) (ht : t < 0) :
    ‖U t‖ ≤ horizonGrowthCoefficient w (U (-1)) (V (-1)) A B*Real.exp (w.re*t) := by
  let P := horizonDichotomyPlus w U V
  let M := horizonDichotomyMinus w U V
  let G := horizonDichotomyError w U p f
  have hd (r : ℝ) (hr : r < 0) := horizonDichotomy_hasDerivAt w U V p f r (hU r hr) (hV r hr)
  have hE := dichotomyEnergy_bound P M G w hwr (A/(2*‖w‖)) B (by positivity) hB
    (fun r hr => (hd r hr).1) (fun r hr => (hd r hr).2)
    (fun r hr => horizonDichotomy_error_bound w hw U V p f A B hA r (hp r hr) (hf r hr))
  have hN : ‖P t‖+‖M t‖ ≤ dichotomyEnergy P M t+1 := by
    dsimp [dichotomyEnergy]
    nlinarith [sq_nonneg (‖P t‖-1),sq_nonneg (‖M t‖-1)]
  have hn := (horizonDichotomy_solution_bound w hw U V t).trans
    (div_le_div_of_nonneg_right (hN.trans (hE t ht)) (by positivity))
  have hb : Real.exp (-w.re*t)*‖U t‖ ≤ horizonGrowthCoefficient w (U (-1)) (V (-1)) A B := by
    simpa only [horizonGrowthCoefficient,dichotomyEnergy,P,M,horizonDichotomyPlus,horizonDichotomyMinus,
      mul_neg_one,neg_neg] using hn
  have hex : Real.exp (w.re*t)*Real.exp (-w.re*t) = 1 := by
    rw [← Real.exp_add,show w.re*t+-w.re*t=0 by ring,Real.exp_zero]
  calc
    ‖U t‖ = Real.exp (w.re*t)*(Real.exp (-w.re*t)*‖U t‖) := by rw [← mul_assoc,hex,one_mul]
    _ ≤ Real.exp (w.re*t)*horizonGrowthCoefficient w (U (-1)) (V (-1)) A B :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := mul_comm _ _

end
end GaloisForLFunctions.HTGeometry
