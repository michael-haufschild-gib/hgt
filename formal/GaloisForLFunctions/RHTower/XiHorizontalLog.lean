import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.RHTower.XiRectangleFold

/-!
# A continuous logarithm of `xi` along a horizontal line

On a horizontal line free of zeros the integral

`Λ(x) = log xi(x₀ + iT) + ∫_{x₀}^{x} (xi'/xi)(u + iT) du`

is a continuous logarithm of `x ↦ xi(x + iT)`: the product `xi(x+iT)e^{−Λ(x)}` has vanishing
derivative and value `1` at `x₀`.  Taking real parts turns this into the modulus formula

`log‖xi(x+iT)‖ = log‖xi(x₀+iT)‖ + Re ∫_{x₀}^{x} (xi'/xi)(u+iT) du`,

which is how a lower bound for `|xi|` — and then for `|ζ|` — is read off the partial fraction.
This mirrors the corpus's `ZetaHorizontalArgument` for `ζ`, but for the entire completed zeta the
line need only avoid the divisor.

## Main results

* `exp_xiHorizontalLog`
* `log_norm_xi_horizontal`
-/

open Complex Set MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

theorem continuous_xi_horizontal (T : ℝ) :
    Continuous fun x : ℝ => xi ((x : ℂ) + (T : ℂ) * I) := by
  have hpath : Continuous fun x : ℝ => ((x : ℂ) + (T : ℂ) * I) := by fun_prop
  exact xi_differentiable.continuous.comp hpath

theorem continuous_deriv_xi : Continuous (deriv xi) := by
  have hdiff : Differentiable ℂ (deriv xi) := fun z =>
    ((xi_analyticOnNhd_univ.deriv) z (Set.mem_univ z)).differentiableAt
  exact hdiff.continuous

/-- The continuous logarithm of `xi` along the horizontal line at height `T`, anchored at `x₀`. -/
def xiHorizontalLog (T x₀ x : ℝ) : ℂ :=
  Complex.log (xi ((x₀ : ℂ) + (T : ℂ) * I))
    + ∫ u in x₀..x, logDeriv xi ((u : ℂ) + (T : ℂ) * I)

theorem hasDerivAt_xiHorizontalLog {T : ℝ}
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) (x₀ x : ℝ) :
    HasDerivAt (xiHorizontalLog T x₀) (logDeriv xi ((x : ℂ) + (T : ℂ) * I)) x := by
  have hc := continuous_logDeriv_xi_horizontal hne
  have hint := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable x₀ x) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact HasDerivAt.const_add (Complex.log (xi ((x₀ : ℂ) + (T : ℂ) * I))) hint

theorem exp_xiHorizontalLog {T : ℝ}
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) (x₀ x : ℝ) :
    Complex.exp (xiHorizontalLog T x₀ x) = xi ((x : ℂ) + (T : ℂ) * I) := by
  set G : ℝ → ℂ := fun u => xi ((u : ℂ) + (T : ℂ) * I)
      * Complex.exp (-xiHorizontalLog T x₀ u) with hG
  have hpath : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ) + (T : ℂ) * I) 1 u := by
    intro u
    have h := (Complex.ofRealCLM.hasDerivAt (x := u)).add_const ((T : ℂ) * I)
    simpa using h
  have hxi : ∀ u : ℝ, HasDerivAt (fun v : ℝ => xi ((v : ℂ) + (T : ℂ) * I))
      (deriv xi ((u : ℂ) + (T : ℂ) * I)) u := by
    intro u
    have hz : HasDerivAt xi (deriv xi ((u : ℂ) + (T : ℂ) * I)) ((u : ℂ) + (T : ℂ) * I) :=
      (xi_differentiable _).hasDerivAt
    have h := (hz.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u (hpath u)
    simpa [Function.comp_def] using h
  have hderiv : ∀ u : ℝ, HasDerivAt G 0 u := by
    intro u
    have h1 := hxi u
    have h2 : HasDerivAt (fun v : ℝ => Complex.exp (-xiHorizontalLog T x₀ v))
        (Complex.exp (-xiHorizontalLog T x₀ u)
          * (-logDeriv xi ((u : ℂ) + (T : ℂ) * I))) u :=
      ((hasDerivAt_xiHorizontalLog hne x₀ u).neg).cexp
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    have hzne : xi ((u : ℂ) + (T : ℂ) * I) ≠ 0 := hne u
    rw [logDeriv_apply]
    field_simp
    ring
  have hdiff : Differentiable ℝ G := fun u => (hderiv u).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun u => (hderiv u).deriv) x x₀
  have hval0 : G x₀ = 1 := by
    rw [hG]
    simp only [xiHorizontalLog, intervalIntegral.integral_same, add_zero]
    rw [Complex.exp_neg, Complex.exp_log (hne x₀)]
    field_simp
    exact div_self (hne x₀)
  rw [hval0] at hconst
  have hGx : xi ((x : ℂ) + (T : ℂ) * I) * Complex.exp (-xiHorizontalLog T x₀ x) = 1 := hconst
  rw [Complex.exp_neg] at hGx
  field_simp at hGx
  exact hGx.symm

/-- **The modulus formula.**  The logarithm of `‖xi‖` moves along a zero-free horizontal segment by
the real part of the integral of the logarithmic derivative. -/
theorem log_norm_xi_horizontal {T : ℝ}
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) (x₀ x : ℝ) :
    Real.log ‖xi ((x : ℂ) + (T : ℂ) * I)‖
      = Real.log ‖xi ((x₀ : ℂ) + (T : ℂ) * I)‖
        + (∫ u in x₀..x, logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re := by
  have hexp := exp_xiHorizontalLog hne x₀ x
  have hnorm : ‖xi ((x : ℂ) + (T : ℂ) * I)‖ = Real.exp ((xiHorizontalLog T x₀ x).re) := by
    rw [← hexp, Complex.norm_exp]
  rw [hnorm, Real.log_exp, xiHorizontalLog, Complex.add_re, Complex.log_re]

end RHTower

end
