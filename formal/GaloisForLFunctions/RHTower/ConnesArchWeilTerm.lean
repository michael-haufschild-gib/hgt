import GaloisForLFunctions.RHTower.DigammaIntegralRepresentation
import GaloisForLFunctions.RHTower.ArchimedeanGammaModule

/-!
# The archimedean local Weil term

Appendix II of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

At the real place the local Weil term is `∫'_{ℝ^*} f(u)|1-u|^{-1} d^*u`.  In the logarithmic
coordinate `u = e^t` with `d^*u = dt` and the half-density normalization `f(u) = u^{1/2} g(u)`
the kernel becomes

  `e^{t/2}|1 - e^t|^{-1} = (2 sinh(t/2))^{-1}`,

symmetric under `t ↦ -t` and singular like `1/t` at the origin.  Against the one-sided power test
`g(e^t) = e^{-(s-1/2)t}`, regularized by Gauss's counterterm `e^{-t}/t`, the local term is exactly
the digamma function, and in the completed normalization it is `2·(Γ_ℝ'/Γ_ℝ)(s) + log π`.
This is the archimedean factor of the explicit formula, the exact analogue of the local Euler
factor `(p^s-1)^{-1}` at a finite place.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The archimedean Weil kernel in logarithmic coordinates. -/
def connesArchWeilKernel (t : ℝ) : ℝ := (2 * Real.sinh (t / 2))⁻¹

/-- **The kernel is the half-density Weil kernel.**  `(2 sinh(t/2))^{-1} = e^{t/2}|1-e^t|^{-1}`. -/
theorem connesArchWeilKernel_eq_weil {t : ℝ} (ht : 0 < t) :
    connesArchWeilKernel t = Real.exp (t / 2) / |1 - Real.exp t| := by
  have hexp : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : (1 : ℝ) < Real.exp t := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr ht
  have habs : |1 - Real.exp t| = Real.exp t - 1 := by
    rw [abs_of_nonpos (by linarith)]; ring
  have hsinh : 2 * Real.sinh (t / 2) = Real.exp (t / 2) - Real.exp (-(t / 2)) := by
    rw [Real.sinh_eq]; ring
  have hpos : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  have hne : Real.exp (t / 2) - Real.exp (-(t / 2)) ≠ 0 := by
    have : Real.exp (-(t / 2)) < Real.exp (t / 2) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hsq : Real.exp (t / 2) ^ 2 - 1 ≠ 0 := by
    have he : Real.exp (t / 2) ^ 2 = Real.exp t := by rw [sq, ← Real.exp_add]; ring_nf
    rw [he]; linarith
  rw [connesArchWeilKernel, hsinh, habs, eq_div_iff (by linarith)]
  rw [Real.exp_neg, hexp]
  field_simp

/-- The regularized archimedean Weil integrand: the Weil kernel against the one-sided power test,
with Gauss's counterterm `e^{-t}/t` removing the logarithmic singularity at the origin. -/
def connesArchWeilIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  ((Real.exp (-t) / t : ℝ) : ℂ)
    - Complex.exp (-(s - 1 / 2) * (t : ℂ)) * ((connesArchWeilKernel t : ℝ) : ℂ)

theorem connesArchWeilKernel_ofReal {t : ℝ} (ht : 0 < t) :
    ((connesArchWeilKernel t : ℝ) : ℂ)
      = Complex.exp (-(t : ℂ) / 2) / (1 - Complex.exp (-(t : ℂ))) := by
  have hsinh : 2 * Real.sinh (t / 2) = Real.exp (t / 2) - Real.exp (-(t / 2)) := by
    rw [Real.sinh_eq]; ring
  have hne : Real.exp (t / 2) - Real.exp (-(t / 2)) ≠ 0 := by
    have : Real.exp (-(t / 2)) < Real.exp (t / 2) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hden : (1 : ℂ) - Complex.exp (-(t : ℂ)) ≠ 0 :=
    _root_.RHTower.one_sub_exp_neg_ofReal_ne_zero ht
  have hneC : (Complex.exp ((t : ℂ) / 2) - Complex.exp (-((t : ℂ) / 2))) ≠ 0 := by
    have h := Complex.ofReal_ne_zero.mpr hne
    push_cast at h
    exact h
  have e1 : -(t : ℂ) / 2 + (t : ℂ) / 2 = 0 := by ring
  have e2 : -(t : ℂ) / 2 + -((t : ℂ) / 2) = -(t : ℂ) := by ring
  rw [connesArchWeilKernel, hsinh]
  push_cast
  rw [eq_div_iff hden, inv_mul_eq_div, div_eq_iff hneC, mul_sub,
    ← Complex.exp_add, ← Complex.exp_add, e1, e2, Complex.exp_zero]

theorem connesArchWeilIntegrand_eq (s : ℂ) {t : ℝ} (ht : 0 < t) :
    connesArchWeilIntegrand s t = _root_.RHTower.digammaGaussIntegrand s t := by
  rw [connesArchWeilIntegrand, _root_.RHTower.digammaGaussIntegrand,
    connesArchWeilKernel_ofReal ht]
  congr 1
  rw [← mul_div_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- **The archimedean local Weil term is the digamma function.**  For `Re s > 0`,
`∫_0^∞ ( e^{-t}/t - e^{-(s-1/2)t}(2 sinh(t/2))^{-1} ) dt = ψ(s)`. -/
theorem connes_archWeil_eq_digamma {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Ioi (0 : ℝ), connesArchWeilIntegrand s t = Complex.digamma s := by
  rw [_root_.RHTower.digamma_eq_integral_gauss hs]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => connesArchWeilIntegrand_eq s ht

theorem connes_archWeil_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (connesArchWeilIntegrand s) (Ioi (0 : ℝ)) volume := by
  refine (_root_.RHTower.integrableOn_digammaGaussIntegrand hs).congr_fun ?_ measurableSet_Ioi
  intro t ht
  exact (connesArchWeilIntegrand_eq s ht).symm

/-- **The archimedean local Weil term in the completed normalization.**  For `Re s > 0`,
`∫_0^∞ ( e^{-t}/t - e^{-(s/2-1/2)t}(2 sinh(t/2))^{-1} ) dt = 2·(Γ_ℝ'/Γ_ℝ)(s) + log π`, the
archimedean factor of the explicit formula. -/
theorem connes_archWeil_eq_logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Ioi (0 : ℝ), connesArchWeilIntegrand (s / 2) t
      = 2 * logDeriv Complex.Gammaℝ s + ((Real.log Real.pi : ℝ) : ℂ) := by
  have hhalf : 0 < (s / 2).re := by
    rw [show s / 2 = (2 : ℝ)⁻¹ * s by push_cast; ring]
    simpa using hs
  rw [connes_archWeil_eq_digamma hhalf, logDeriv_Gammaℝ hs, gammaRealLogConnection]
  ring

end

end GaloisForLFunctions.RHTower
