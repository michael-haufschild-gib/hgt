/-
# The closed-loop fundamental theorem for the logarithmic derivative

`exp(∫ₐᵇ g'/g) = g(b)/g(a)` for `g : ℝ → ℂ` everywhere differentiable, nonzero, with continuous
derivative. On a closed loop (`g a = g b`) this gives `exp(∮ d log g) = 1` — the analytic FTC input the
Böttcher cover non-square argument isolates as a hypothesis (`Bottcher.not_square_of_period_ftc`'s
`hftc : exp ph = 1`): for the single-valued square-root germ `h` along the cover loop, `g = h∘γ` is
globally smooth and nonzero, `ph = ∫ g'/g`, and the loop being closed forces `exp ph = 1`.

Proof: `ψ(t) = g(t)·exp(−∫ₐᵗ g'/g)` has identically-zero derivative (`g' − g·(g'/g) = 0`), hence is
constant; `ψ(a) = g(a)` and `ψ(b) = g(b)·exp(−∫ₐᵇ)` give the identity.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

open Complex intervalIntegral

namespace ClosedLoopFTC

/-- **Closed-loop FTC for the logarithmic derivative.** `exp(∫ₐᵇ g'/g) = g(b)/g(a)`. -/
theorem exp_integral_logDeriv {g g' : ℝ → ℂ} (a b : ℝ)
    (hg : ∀ t, g t ≠ 0) (hderiv : ∀ t, HasDerivAt g (g' t) t) (hcont' : Continuous g') :
    Complex.exp (∫ t in a..b, g' t / g t) = g b / g a := by
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hLcont : Continuous (fun t => g' t / g t) := hcont'.div hgcont hg
  set G : ℝ → ℂ := fun t => ∫ s in a..t, g' s / g s with hGdef
  have hGderiv : ∀ t, HasDerivAt G (g' t / g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hLcont.intervalIntegrable a t)
      (hLcont.stronglyMeasurableAtFilter _ _) hLcont.continuousAt
  set ψ : ℝ → ℂ := fun t => g t * Complex.exp (-G t) with hψdef
  have hψderiv : ∀ t, HasDerivAt ψ 0 t := by
    intro t
    have hexp : HasDerivAt (fun u => Complex.exp (-G u))
        (Complex.exp (-G t) * (-(g' t / g t))) t := ((hGderiv t).neg).cexp
    have hmul := (hderiv t).mul hexp
    have hgt : g t ≠ 0 := hg t
    have hzero : g' t * Complex.exp (-G t) + g t * (Complex.exp (-G t) * (-(g' t / g t))) = 0 := by
      field_simp
      ring
    rw [hzero] at hmul
    exact hmul
  have hψdiff : Differentiable ℝ ψ := fun t => (hψderiv t).differentiableAt
  have hconst : ψ b = ψ a :=
    is_const_of_deriv_eq_zero hψdiff (fun t => (hψderiv t).deriv) b a
  have hGa : G a = 0 := by simp [hGdef]
  have hψa : ψ a = g a := by simp [hψdef, hGa]
  rw [hψa] at hconst
  -- hconst : ψ b = g a, i.e. (defeq) g b * exp(-G b) = g a
  have e1 : g b * (Complex.exp (G b))⁻¹ = g a := by rw [← Complex.exp_neg]; exact hconst
  have hexpne : Complex.exp (G b) ≠ 0 := Complex.exp_ne_zero _
  show Complex.exp (G b) = g b / g a
  rw [eq_div_iff (hg a)]
  field_simp at e1
  linear_combination -e1

/-- **Closed-loop corollary.** On a closed loop (`g a = g b`), `exp(∫ₐᵇ g'/g) = 1`. This discharges the
`hftc : exp ph = 1` hypothesis of `Bottcher.not_square_of_period_ftc` for the single-valued cover germ. -/
theorem exp_integral_logDeriv_closed {g g' : ℝ → ℂ} (a b : ℝ)
    (hg : ∀ t, g t ≠ 0) (hderiv : ∀ t, HasDerivAt g (g' t) t) (hcont' : Continuous g')
    (hclosed : g a = g b) :
    Complex.exp (∫ t in a..b, g' t / g t) = 1 := by
  rw [exp_integral_logDeriv a b hg hderiv hcont', hclosed, div_self (hg b)]

end ClosedLoopFTC
