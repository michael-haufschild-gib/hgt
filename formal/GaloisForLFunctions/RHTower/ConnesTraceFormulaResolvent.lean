import GaloisForLFunctions.RHTower.ConnesWeilPrimeSide
import GaloisForLFunctions.RHTower.ConnesArchWeilTerm
import GaloisForLFunctions.RHTower.XiGuinandWeilExplicitFormula
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure

/-!
# Connes' trace formula equals Weil's explicit formula on the resolvent test algebra

Theorem 6 and Appendix II of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes' geometric side is a sum over the places of `ℚ` of local principal-value Weil integrals.
For the regularized Cauchy test `w ↦ w^{-1} - (w - z)^{-1}` at a real abscissa `σ > 1` all three
ingredients are now available in closed form:

* the finite places contribute `∑_p log p · (p^σ - 1)^{-1}`, the von Mangoldt Dirichlet series;
* the archimedean place contributes `(∫_0^∞ (e^{-t}/t - e^{-(σ/2-1/2)t}(2 sinh(t/2))^{-1}) dt
  - log π)/2 = (Γ_ℝ'/Γ_ℝ)(σ)`;
* the two poles of the completed zeta contribute `1/σ + 1/(σ-1)`.

Their combination is exactly the source functional of the corpus's Guinand--Weil explicit formula,
so the spectral sum over the centred Xi divisor equals `-i` times the sum of the local Weil terms.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **Connes' geometric side at a real abscissa.**  The sum over the finite places of the local
Weil terms, minus the polar contributions of the completed zeta, minus the archimedean local
term. -/
def connesGeometricSide (σ : ℝ) : ℂ :=
  (∑' p : Nat.Primes, (Real.log (((p : ℕ) : ℝ)) : ℂ) * connesLocalWeilTerm p (σ : ℂ))
    - 1 / (σ : ℂ) - 1 / ((σ : ℂ) - 1)
    - ((∫ t in Ioi (0 : ℝ), connesArchWeilIntegrand ((σ : ℂ) / 2) t)
        - ((Real.log Real.pi : ℝ) : ℂ)) / 2

theorem connesGeometricSide_eq {σ : ℝ} (hσ : 1 < σ) :
    connesGeometricSide σ
      = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)
        - logDeriv _root_.RHTower.archFactor (σ : ℂ) := by
  have hre : 1 < ((σ : ℝ) : ℂ).re := by simpa using hσ
  have hrepos : 0 < ((σ : ℝ) : ℂ).re := by simpa using lt_trans zero_lt_one hσ
  have h0 : ((σ : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h] at hrepos
    simp at hrepos
  have h1 : ((σ : ℝ) : ℂ) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
  have hpole : ∀ m : ℕ, ((σ : ℝ) : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have := congrArg Complex.re hm
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.natCast_re] at this
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    norm_num at this
    linarith
  have harch : ((∫ t in Ioi (0 : ℝ), connesArchWeilIntegrand ((σ : ℂ) / 2) t)
      - ((Real.log Real.pi : ℝ) : ℂ)) / 2 = gammaRealLogConnection ((σ : ℝ) : ℂ) := by
    rw [connes_archWeil_eq_logDeriv_Gammaℝ hrepos, logDeriv_Gammaℝ hrepos]
    ring
  have hprime : (∑' p : Nat.Primes, (Real.log (((p : ℕ) : ℝ)) : ℂ) *
      connesLocalWeilTerm p (σ : ℂ))
      = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((σ : ℝ) : ℂ) := by
    rw [connes_weil_primeSide hσ, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre]
  rw [connesGeometricSide, hprime, harch,
    _root_.RHTower.logDeriv_archFactor_closed_off_poles hpole h0 h1]
  ring

/-- **Connes' trace formula on the resolvent test algebra.**  For a real abscissa `σ > 1`, with
`z` the centred coordinate of `σ`, the sum of the regularized Cauchy kernel over the
multiplicity-exact centred Xi divisor is `-i` times Connes' geometric side: the sum over the
places of `ℚ` of the local Weil terms. -/
theorem connes_traceFormula_resolvent {σ : ℝ} (hσ : 1 < σ) :
    (∑' q : _root_.RHTower.XiZeroCopy,
        _root_.RHTower.xiCauchyRegularizedKernel (-(((σ : ℝ) : ℂ) - 1 / 2) * Complex.I)
          (_root_.RHTower.xiSpectralPoint q))
      = -Complex.I * connesGeometricSide σ := by
  set z : ℂ := -(((σ : ℝ) : ℂ) - 1 / 2) * Complex.I with hz
  have hcoord : (1 : ℂ) / 2 + z * Complex.I = ((σ : ℝ) : ℂ) := by
    have hsq : (-(((σ : ℝ) : ℂ) - 1 / 2) * Complex.I) * Complex.I
        = -(((σ : ℝ) : ℂ) - 1 / 2) * (Complex.I * Complex.I) := by ring
    rw [hz, hsq, Complex.I_mul_I]
    ring
  have hre : 1 < ((1 : ℂ) / 2 + z * Complex.I).re := by
    rw [hcoord]
    simpa using hσ
  rw [_root_.RHTower.xiGuinandWeilExplicitFormula_single
      (_root_.RHTower.XiExplicitAdmissible_of_one_lt_re hre),
    ← _root_.RHTower.primeArchSourceRelativeTrace_eq_continued hre,
    _root_.RHTower.primeArchSourceRelativeTrace, hcoord, connesGeometricSide_eq hσ]

end

end GaloisForLFunctions.RHTower
