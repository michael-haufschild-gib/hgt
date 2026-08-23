import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivLineBound
import GaloisForLFunctions.RHTower.Sieve.PerronVerticalSide

/-!
# Continuity of the Perron integrand on a line right of the critical line

Under the Riemann hypothesis `ζ` has no zero there and the pole is to the right, so the integrand is
continuous along the whole line — the hypothesis the vertical-side estimate needs.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **Continuity of the Perron integrand on a shifted line.** -/
theorem continuous_perron_integrand_line (hRH : RiemannHypothesis) {x σ : ℝ} (hx : 0 < x)
    (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1) :
    Continuous fun t : ℝ =>
      (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hne1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    rw [hcon] at hre
    simp only [Complex.one_re] at hre
    linarith
  have hne0 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro hcon
    rw [hcon] at hre
    simp only [Complex.zero_re] at hre
    linarith
  have hzne : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_rh hRH (by rw [hre]; linarith) hne1
  have hinner : ContinuousAt (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)) t := by fun_prop
  have hout : ContinuousAt
      (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
      ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
        ((σ : ℂ) + (t : ℂ) * Complex.I) :=
      (differentiableAt_deriv_riemannZeta hne1).neg.div
        (differentiableAt_riemannZeta hne1) hzne
    have h2 : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s)
        ((σ : ℂ) + (t : ℂ) * Complex.I) :=
      (differentiableAt_id.const_cpow (Or.inl hxne)).div differentiableAt_id hne0
    exact (h1.mul h2).continuousAt
  have hcomp : ContinuousAt
      ((fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
        ∘ (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I))) t :=
    ContinuousAt.comp
      (g := fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
      (f := fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)) hout hinner
  exact hcomp

end

end RHTower.Sieve
