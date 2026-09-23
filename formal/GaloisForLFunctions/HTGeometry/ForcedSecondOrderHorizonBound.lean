import GaloisForLFunctions.HTGeometry.ComplexDichotomyEnergy

/-! Whole-half-line growth of the actual complex forced second-order equation. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def horizonDichotomyPlus (w : ℂ) (U V : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-w.re*t):ℂ)*(V t+w*U t)
def horizonDichotomyMinus (w : ℂ) (U V : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-w.re*t):ℂ)*(V t-w*U t)
def horizonDichotomyError (w : ℂ) (U p f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-w.re*t):ℂ)*(p t*U t-f t)

/-- Actual free-mode channels of a forced second-order solution, with its original forcing retained. -/
theorem horizonDichotomy_hasDerivAt (w : ℂ) (U V p f : ℝ → ℂ) (t : ℝ)
    (hU : HasDerivAt U (V t) t) (hV : HasDerivAt V (w^(2 : ℕ)*U t+p t*U t-f t) t) :
    HasDerivAt (horizonDichotomyPlus w U V)
      ((w-(w.re:ℂ))*horizonDichotomyPlus w U V t+horizonDichotomyError w U p f t) t ∧
    HasDerivAt (horizonDichotomyMinus w U V)
      ((-w-(w.re:ℂ))*horizonDichotomyMinus w U V t+horizonDichotomyError w U p f t) t := by
  have hs := ((((hasDerivAt_id t).const_mul (-w.re)).exp).ofReal_comp)
  constructor
  · convert! hs.mul (hV.add (hU.const_mul w)) using 1
    dsimp [horizonDichotomyPlus,horizonDichotomyError]
    push_cast
    ring
  · convert! hs.mul (hV.sub (hU.const_mul w)) using 1
    dsimp [horizonDichotomyMinus,horizonDichotomyError]
    push_cast
    ring

/-- The actual solution is recovered from the two free-mode channels, with its exponential weight. -/
theorem horizonDichotomy_solution_bound (w : ℂ) (hw : w ≠ 0) (U V : ℝ → ℂ) (t : ℝ) :
    Real.exp (-w.re*t)*‖U t‖ ≤
      (‖horizonDichotomyPlus w U V t‖+‖horizonDichotomyMinus w U V t‖)/(2*‖w‖) := by
  have he : (Real.exp (-w.re*t):ℂ)*U t =
      (horizonDichotomyPlus w U V t-horizonDichotomyMinus w U V t)/(2*w) := by
    unfold horizonDichotomyPlus horizonDichotomyMinus
    field_simp [hw]
    ring
  have hn := congrArg norm he
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_div] at hn
  norm_num at hn
  rw [neg_mul,hn]
  exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by positivity)

/-- Exponentially decaying potential and forcing supply the exact integrable channel coupling. -/
theorem horizonDichotomy_error_bound (w : ℂ) (hw : w ≠ 0) (U V p f : ℝ → ℂ)
    (A B : ℝ) (hA : 0 ≤ A) (t : ℝ)
    (hp : ‖p t‖ ≤ A*Real.exp (2*t))
    (hf : ‖f t‖ ≤ B*Real.exp ((w.re+2)*t)) :
    ‖horizonDichotomyError w U p f t‖ ≤ Real.exp (2*t)*
      (A/(2*‖w‖)*(‖horizonDichotomyPlus w U V t‖+‖horizonDichotomyMinus w U V t‖)+B) := by
  have hu := horizonDichotomy_solution_bound w hw U V t
  have hs : Real.exp (-w.re*t)*Real.exp ((w.re+2)*t) = Real.exp (2*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : horizonDichotomyError w U p f t =
      p t*((Real.exp (-w.re*t):ℂ)*U t)-(Real.exp (-w.re*t):ℂ)*f t := by
    unfold horizonDichotomyError
    ring
  rw [he]
  calc
    _ ≤ ‖p t*((Real.exp (-w.re*t):ℂ)*U t)‖+‖(Real.exp (-w.re*t):ℂ)*f t‖ := norm_sub_le _ _
    _ = ‖p t‖*(Real.exp (-w.re*t)*‖U t‖)+Real.exp (-w.re*t)*‖f t‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    _ ≤ (A*Real.exp (2*t))*
        ((‖horizonDichotomyPlus w U V t‖+‖horizonDichotomyMinus w U V t‖)/(2*‖w‖))+
          Real.exp (-w.re*t)*(B*Real.exp ((w.re+2)*t)) := by
      exact add_le_add (mul_le_mul hp hu (by positivity) (by positivity))
        (mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le)
    _ = _ := by rw [mul_left_comm (Real.exp (-w.re*t)) B,hs]; ring

/-- A genuine forced second-order solution has the sharp free-frequency horizon growth bound.
The statement uses actual derivatives and derived decay bounds, with no endpoint condition. -/
theorem forcedSecondOrder_horizon_bound (w : ℂ) (hw : w ≠ 0) (hwr : w.re ≤ 0)
    (U V p f : ℝ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hU : ∀ t < 0, HasDerivAt U (V t) t)
    (hV : ∀ t < 0, HasDerivAt V (w^(2 : ℕ)*U t+p t*U t-f t) t)
    (hp : ∀ t < 0, ‖p t‖ ≤ A*Real.exp (2*t))
    (hf : ∀ t < 0, ‖f t‖ ≤ B*Real.exp ((w.re+2)*t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0, ‖U t‖ ≤ C*Real.exp (w.re*t) := by
  let P := horizonDichotomyPlus w U V
  let M := horizonDichotomyMinus w U V
  let G := horizonDichotomyError w U p f
  have hd (t : ℝ) (ht : t < 0) := horizonDichotomy_hasDerivAt w U V p f t (hU t ht) (hV t ht)
  have hE := dichotomyEnergy_bound P M G w hwr (A/(2*‖w‖)) B (by positivity) hB
    (fun t ht => (hd t ht).1) (fun t ht => (hd t ht).2)
    (fun t ht => horizonDichotomy_error_bound w hw U V p f A B hA t (hp t ht) (hf t ht))
  let D := max ((dichotomyEnergy P M (-1)+1)*Real.exp ((4*(A/(2*‖w‖))+2*B)/2))
    ((dichotomyEnergy P M (-1)+1)*Real.exp (-4*w.re+4*(A/(2*‖w‖))+2*B))
  have hD : 0 ≤ D := by dsimp [D,dichotomyEnergy]; positivity
  have hwN : 0 < 2*‖w‖ := mul_pos (by norm_num) (norm_pos_iff.mpr hw)
  refine ⟨D/(2*‖w‖),div_nonneg hD hwN.le,fun t ht => ?_⟩
  have hN : ‖P t‖+‖M t‖ ≤ dichotomyEnergy P M t+1 := by
    dsimp [dichotomyEnergy]
    nlinarith [sq_nonneg (‖P t‖-1),sq_nonneg (‖M t‖-1),sq_nonneg ‖P t‖,sq_nonneg ‖M t‖]
  have hn : Real.exp (-w.re*t)*‖U t‖ ≤ D/(2*‖w‖) :=
    (horizonDichotomy_solution_bound w hw U V t).trans
      (div_le_div_of_nonneg_right (hN.trans (hE t ht)) hwN.le)
  have he := mul_le_mul_of_nonneg_left hn (Real.exp_pos (w.re*t)).le
  have hex : Real.exp (w.re*t)*Real.exp (-w.re*t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  calc
    ‖U t‖ = Real.exp (w.re*t)*(Real.exp (-w.re*t)*‖U t‖) := by
      rw [← mul_assoc,hex,one_mul]
    _ ≤ Real.exp (w.re*t)*(D/(2*‖w‖)) := he
    _ = D/(2*‖w‖)*Real.exp (w.re*t) := mul_comm _ _

end
end GaloisForLFunctions.HTGeometry
