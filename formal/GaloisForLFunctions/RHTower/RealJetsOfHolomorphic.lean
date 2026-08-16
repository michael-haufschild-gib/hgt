import GaloisForLFunctions.RHTower.ComplexLaplaceHolomorphy

/-!
# Real jets of a holomorphic function on a disc

A function holomorphic on a complex ball centred at a real point restricts to a smooth real function
on the corresponding real interval, and its real jets are the restrictions of its complex jets.  The
induction is local: at each stage the previous identity holds on a whole real neighbourhood, so the
derivative may be taken through it.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

theorem analyticAt_iteratedDeriv_complex {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (k : ℕ) :
    AnalyticAt ℂ (iteratedDeriv k f) x := by
  induction k generalizing f with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ k ih =>
    have h : AnalyticAt ℂ (deriv f) x := hf.deriv
    have := ih h
    refine this.congr ?_
    filter_upwards with z
    rw [iteratedDeriv_succ']

theorem mem_ball_ofReal {a δ x : ℝ} (h : |x - a| < δ) :
    ((x : ℂ)) ∈ Metric.ball ((a : ℂ)) δ := by
  rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  exact h

/-- **The real jets are the complex jets.** -/
theorem iteratedDeriv_ofReal_comp {F : ℂ → ℂ} {a δ : ℝ}
    (hF : ∀ z ∈ Metric.ball ((a : ℂ)) δ, AnalyticAt ℂ F z) (k : ℕ) :
    ∀ x : ℝ, |x - a| < δ →
      iteratedDeriv k (fun t : ℝ => F (t : ℂ)) x = iteratedDeriv k F ((x : ℂ)) := by
  induction k with
  | zero => intro x _; simp [iteratedDeriv_zero]
  | succ k ih =>
    intro x hx
    have hxball : ((x : ℂ)) ∈ Metric.ball ((a : ℂ)) δ := mem_ball_ofReal hx
    have hopen : {y : ℝ | |y - a| < δ} ∈ nhds x := by
      have : {y : ℝ | |y - a| < δ} = Metric.ball a δ := by
        ext y
        rw [Metric.mem_ball, Real.dist_eq]
        rfl
      rw [this]
      refine Metric.isOpen_ball.mem_nhds ?_
      rw [Metric.mem_ball, Real.dist_eq]
      exact hx
    have hEq : iteratedDeriv k (fun t : ℝ => F (t : ℂ))
        =ᶠ[nhds x] fun y : ℝ => iteratedDeriv k F ((y : ℂ)) := by
      filter_upwards [hopen] with y hy
      exact ih y hy
    have hd : HasDerivAt (fun t : ℝ => (iteratedDeriv k F) (t : ℂ))
        (deriv (iteratedDeriv k F) ((x : ℂ))) x :=
      HasDerivAt.comp_ofReal
        (analyticAt_iteratedDeriv_complex (hF _ hxball) k).differentiableAt.hasDerivAt
    rw [iteratedDeriv_succ, hEq.deriv_eq, hd.deriv, iteratedDeriv_succ]

end GaloisForLFunctions.RHTower
