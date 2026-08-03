import GaloisForLFunctions.RHTower.Sieve.DirichletKernelPairing

/-!
# Integrating a linear weight against a phase

`t e^{itL}` has the explicit antiderivative

`t e^{itL}/(iL) - e^{itL}/(iL)²`,

so any kernel that is piecewise linear — the triangular (Fejér) weight `1 - |t|/T` in particular —
integrates against a phase in closed form.  Together with the constant case of
`SymmetricPhaseIntegral.lean` this computes the transform of every piecewise-linear kernel, which is
what a smoothed short-interval argument needs: the sharp kernel `2 sin(TL)/L` decays only like
`|L|^{-1}` and its tail is not absolutely summable, whereas the triangular one decays like `|L|^{-2}`.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- The antiderivative of `t e^{itL}`. -/
noncomputable def linPhaseAnti (L : ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) / ((L : ℂ) * Complex.I)
    - Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) / ((L : ℂ) * Complex.I) ^ 2

/-- **The antiderivative of a linear weight against a phase.** -/
theorem hasDerivAt_linPhaseAnti (L : ℝ) (hL : L ≠ 0) (t : ℝ) :
    HasDerivAt (linPhaseAnti L)
      ((t : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)) t := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hne : ((L : ℂ) * Complex.I) ≠ 0 := mul_ne_zero hL' Complex.I_ne_zero
  have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) ((1 : ℝ) : ℂ) t := (hasDerivAt_id t).ofReal_comp
  have hE := hasDerivAt_exp_phase L t
  have hprod := hid.mul hE
  have h1 := hprod.div_const ((L : ℂ) * Complex.I)
  have h2 := hE.div_const (((L : ℂ) * Complex.I) ^ 2)
  have hd := h1.sub h2
  have hval : (((1 : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)
        + (t : ℂ) * (Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * ((L : ℂ) * Complex.I)))
          / ((L : ℂ) * Complex.I)
        - Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * ((L : ℂ) * Complex.I)
          / ((L : ℂ) * Complex.I) ^ 2
      = (t : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) := by
    field_simp
    ring
  rw [hval] at hd
  exact hd

/-- The linear weight is interval-integrable against a phase. -/
theorem intervalIntegrable_linPhase (L : ℝ) (A B : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => (t : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)) volume A B := by
  refine Continuous.intervalIntegrable ?_ A B
  fun_prop

/-- **The integral of a linear weight against a phase.** -/
theorem integral_linPhase (L : ℝ) (hL : L ≠ 0) (A B : ℝ) :
    (∫ t in A..B, (t : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
      = linPhaseAnti L B - linPhaseAnti L A :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_linPhaseAnti L hL t) (intervalIntegrable_linPhase L A B)

end RHTower.Sieve
