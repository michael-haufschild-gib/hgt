import GaloisForLFunctions.HTGeometry.GammaLogIntegrandDerivatives
import GaloisForLFunctions.HTGeometry.GammaVerticalDecay
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Gamma decays faster than any polynomial on every vertical line

In logarithmic coordinates `Γ(σ+it)` is the Fourier transform of `e^{σu−e^u}` evaluated at
`−t/2π`.  That integrand is smooth and every one of its derivatives is integrable, so the Fourier
transform of the `N`-th derivative is `(2πix)^N` times the Fourier transform of the integrand; by
Riemann–Lebesgue the left side vanishes at infinity.

Hence `t^N · Γ(σ+it) → 0` for every `N` and every `σ > 0`: the exponential valuation direction of the
Gamma field holds on *every* vertical line of the right half plane, not only on the half-integer lines
where two-sided modulus bounds are available.
-/

open MeasureTheory Filter Set Real

namespace GaloisForLFunctions

/-- Iterated derivatives commute with the real-to-complex embedding. -/
theorem iteratedDeriv_ofReal_comp {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (n : ℕ) :
    iteratedDeriv n (fun u : ℝ => ((g u : ℝ) : ℂ))
      = fun u : ℝ => ((iteratedDeriv n g u : ℝ) : ℂ) := by
  induction n with
  | zero =>
      funext u
      simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext u
      rw [iteratedDeriv_succ]
      have hd : HasDerivAt (iteratedDeriv n g) (deriv (iteratedDeriv n g) u) u := by
        have := hg.differentiable_iteratedDeriv n (by exact compareOfLessAndEq_eq_lt.mp rfl)
        exact (this u).hasDerivAt
      exact hd.ofReal_comp.deriv

/-- The complexified log-coordinate Gamma integrand. -/
noncomputable def expShiftC (σ : ℝ) (u : ℝ) : ℂ := ((expShift σ 0 u : ℝ) : ℂ)

theorem contDiff_expShiftC (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (expShiftC σ) := by
  have h := contDiff_expShift σ
  exact Complex.ofRealCLM.contDiff.comp h

theorem integrable_iteratedDeriv_expShiftC {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Integrable (iteratedDeriv n (expShiftC σ)) := by
  have hfun : iteratedDeriv n (expShiftC σ)
      = fun u : ℝ => ((iteratedDeriv n (expShift σ 0) u : ℝ) : ℂ) :=
    iteratedDeriv_ofReal_comp (contDiff_expShift σ) n
  rw [hfun]
  exact (integrable_iteratedDeriv_expShift hσ n).ofReal

/-- The Fourier transform of the log-coordinate integrand is `Γ` on the vertical line. -/
theorem fourier_expShiftC {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    FourierTransform.fourier (expShiftC σ) (-t / (2 * Real.pi))
      = Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  rw [Real.fourier_real_eq, Gamma_vertical_eq_fourier hσ t]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (Real.fourierChar (-(u * (-t / (2 * Real.pi)))) : Circle) • expShiftC σ u
    = Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * ((Real.exp (σ * u - Real.exp u) : ℝ) : ℂ)
  have hval : expShiftC σ u = ((Real.exp (σ * u - Real.exp u) : ℝ) : ℂ) := by
    rw [expShiftC, expShift]
    norm_num
  rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, hval]
  congr 2
  push_cast
  field_simp

/-- **`Γ` decays faster than any polynomial on every vertical line in the right half plane.** -/
theorem tendsto_pow_mul_Gamma_vertical {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ N * Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hfd := Real.fourier_iteratedDeriv (f := expShiftC σ) (N := (⊤ : ℕ∞)) (n := N)
    (contDiff_expShiftC σ) (fun n _ => integrable_iteratedDeriv_expShiftC hσ n) le_top
  have hRL := Real.tendsto_integral_exp_smul_cocompact (f := iteratedDeriv N (expShiftC σ))
  have hshift : Tendsto (fun t : ℝ => -t / (2 * Real.pi)) atTop atBot := by
    have hpi : 0 < 2 * Real.pi := by positivity
    have h1 : Tendsto (fun t : ℝ => -t) atTop atBot := tendsto_neg_atTop_atBot
    simp only [div_eq_mul_inv]
    exact h1.atBot_mul_const (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)
  have hco : Tendsto (fun t : ℝ => -t / (2 * Real.pi)) atTop (cocompact ℝ) :=
    hshift.mono_right (le_trans le_sup_left (le_of_eq cocompact_eq_atBot_atTop.symm))
  have hcomp := hRL.comp hco
  have hkey : Tendsto (fun t : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I * ((-t / (2 * Real.pi) : ℝ) : ℂ)) ^ N
        • Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
    refine hcomp.congr fun t => ?_
    have h1 : (∫ v : ℝ, (Real.fourierChar (-(v * (-t / (2 * Real.pi)))) : Circle)
        • iteratedDeriv N (expShiftC σ) v)
        = FourierTransform.fourier (iteratedDeriv N (expShiftC σ)) (-t / (2 * Real.pi)) := by
      rw [Real.fourier_real_eq]
    rw [Function.comp_apply, h1, hfd]
    simp only []
    rw [fourier_expShiftC hσ t]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ t : ℝ, ‖(t : ℂ) ^ N * Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖(2 * (Real.pi : ℂ) * Complex.I * ((-t / (2 * Real.pi) : ℝ) : ℂ)) ^ N
        • Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    intro t
    have hfac : (2 * (Real.pi : ℂ) * Complex.I * ((-t / (2 * Real.pi) : ℝ) : ℂ))
        = -Complex.I * (t : ℂ) := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
    rw [hfac, smul_eq_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_mul]
    simp
  refine Filter.Tendsto.congr (fun t => (hnorm t).symm) ?_
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  exact hkey

end GaloisForLFunctions
