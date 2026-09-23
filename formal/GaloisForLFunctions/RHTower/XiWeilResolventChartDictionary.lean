import GaloisForLFunctions.RHTower.XiResolventTraceHankelCriterion
import GaloisForLFunctions.RHTower.XiWeilResolventSource
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# The dictionary between the Weil-polarization and resolvent-Hankel charts

The corpus carries two positivity programmes on the same divisor: the Weil polarization on
test functions and the resolvent-trace Hankel tower on shifted squared spectral points.  This
module identifies their base levels exactly: at an imaginary Cauchy parameter the Weil pair
summand is the resolvent coordinate at the squared shift,

`(α − (−it))⁻¹ · conj((ᾱ − (−it))⁻¹) = (α² + t²)⁻¹`,

so the diagonal Weil value of the Cauchy test at `−it` **is** the zeroth resolvent moment at
shift `t²`.  Three consequences transfer across the dictionary, all unconditional:

* `xiWeilPolarization_cauchyTest_re_pos` — the diagonal Weil value of every imaginary-parameter
  Cauchy test is strictly positive: the first strictly positive family of Weil diagonals beyond
  the divisor-even sector, powered by the formalized height gap (`xiSpectralSq_re_pos`) and the
  nonempty divisor.
* `xiWeilPolarization_cauchyTest_eq_logDeriv` — the same diagonal is the Euler-ray response
  `logDeriv xi (1/2 + t) / t`.
* `xiWeilPolarization_cauchyTest_eq_arithmetic` — for `t > 1/2` it is the explicit
  polar/archimedean/von-Mangoldt expression: a Weil diagonal evaluated in prime terms.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The pair-term dictionary**: at an imaginary Cauchy parameter the Weil pair summand is the
resolvent coordinate at the squared shift. -/
theorem xiWeilCauchyTest_pair_term_eq_resolventPoint (t : ℝ) (q : XiZeroCopy) :
    xiWeilCauchyTest (-(t : ℂ) * Complex.I) (xiSpectralPoint q) *
      xiWeilSharp (xiWeilCauchyTest (-(t : ℂ) * Complex.I)) (xiSpectralPoint q) =
    xiResolventPoint (t ^ (2 : ℕ)) q := by
  rw [xiWeilSharp_cauchy]
  have hconj : (starRingEnd ℂ) (-(t : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
    rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj, xiWeilCauchyTest, xiWeilCauchyTest, xiResolventPoint, ← mul_inv]
  congr 1
  push_cast
  linear_combination (-(t : ℂ) ^ (2 : ℕ)) * Complex.I_sq

/-- **The diagonal dictionary**: the Weil diagonal of the imaginary-parameter Cauchy test is
the zeroth resolvent moment at the squared shift. -/
theorem xiWeilPolarization_cauchyTest_eq_resolventMoment (t : ℝ) :
    xiWeilPolarization (xiWeilCauchyTest (-(t : ℂ) * Complex.I))
        (xiWeilCauchyTest (-(t : ℂ) * Complex.I)) =
      xiResolventMoment 0 (t ^ (2 : ℕ)) := by
  rw [xiWeilPolarization, xiResolventMoment]
  exact tsum_congr fun q => by
    rw [pow_one, xiWeilCauchyTest_pair_term_eq_resolventPoint]

/-- Each resolvent coordinate has strictly positive real part at nonnegative shift. -/
theorem xiResolventPoint_re_pos {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    0 < (xiResolventPoint X q).re := by
  rw [xiResolventPoint, Complex.inv_re]
  apply div_pos (xiSpectralSq_add_ofReal_re_pos hX q)
  exact Complex.normSq_pos.mpr (xiSpectralSq_add_ofReal_ne_zero hX q)

/-- **The first strictly positive family of Weil diagonals.**  The diagonal Weil value of every
imaginary-parameter Cauchy test is strictly positive, unconditionally: every divisor copy
contributes positively through the formalized height gap, and the divisor is nonempty. -/
theorem xiWeilPolarization_cauchyTest_re_pos (t : ℝ) :
    0 < (xiWeilPolarization (xiWeilCauchyTest (-(t : ℂ) * Complex.I))
        (xiWeilCauchyTest (-(t : ℂ) * Complex.I))).re := by
  rw [xiWeilPolarization_cauchyTest_eq_resolventMoment, xiResolventMoment]
  have hX : (0 : ℝ) ≤ t ^ (2 : ℕ) := sq_nonneg t
  have hsum : Summable (fun q : XiZeroCopy => xiResolventPoint (t ^ (2 : ℕ)) q ^ (0 + 1)) := by
    refine (summable_xiResolventPoint hX).congr fun q => ?_
    rw [pow_one]
  rw [Complex.re_tsum hsum]
  have hre : ∀ q : XiZeroCopy, 0 < (xiResolventPoint (t ^ (2 : ℕ)) q ^ (0 + 1)).re := by
    intro q
    rw [pow_one]
    exact xiResolventPoint_re_pos hX q
  have hsumre : Summable (fun q : XiZeroCopy =>
      (xiResolventPoint (t ^ (2 : ℕ)) q ^ (0 + 1)).re) := by
    simpa only [Function.comp_apply] using!
      hsum.map Complex.reCLM Complex.reCLM.continuous
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy
  calc (0 : ℝ) < (xiResolventPoint (t ^ (2 : ℕ)) q₀ ^ (0 + 1)).re := hre q₀
    _ ≤ ∑' q : XiZeroCopy, (xiResolventPoint (t ^ (2 : ℕ)) q ^ (0 + 1)).re :=
        hsumre.le_tsum q₀ fun q _ => (hre q).le

/-- The Weil diagonal of the imaginary-parameter Cauchy test is the Euler-ray response of the
completed zeta. -/
theorem xiWeilPolarization_cauchyTest_eq_logDeriv {t : ℝ} (ht : 0 < t) :
    xiWeilPolarization (xiWeilCauchyTest (-(t : ℂ) * Complex.I))
        (xiWeilCauchyTest (-(t : ℂ) * Complex.I)) =
      logDeriv xi ((1 / 2 : ℂ) + (t : ℂ)) / (t : ℂ) := by
  rw [xiWeilPolarization_cauchyTest_eq_resolventMoment,
    xiResolventMoment_zero_eq_logDeriv ht]

/-- The Euler-ray response is strictly positive in real part on the whole ray: a classical
inequality obtained here from the Weil-chart positivity. -/
theorem logDeriv_xi_div_re_pos {t : ℝ} (ht : 0 < t) :
    0 < (logDeriv xi ((1 / 2 : ℂ) + (t : ℂ)) / (t : ℂ)).re := by
  rw [← xiWeilPolarization_cauchyTest_eq_logDeriv ht]
  exact xiWeilPolarization_cauchyTest_re_pos t

/-- **The arithmetic Weil diagonal.**  For `t > 1/2` the diagonal Weil value of the
imaginary-parameter Cauchy test is the explicit polar/archimedean/von-Mangoldt expression: a
strictly positive Weil diagonal evaluated in prime terms. -/
theorem xiWeilPolarization_cauchyTest_eq_arithmetic {t : ℝ} (ht : 1 / 2 < t) :
    xiWeilPolarization (xiWeilCauchyTest (-(t : ℂ) * Complex.I))
        (xiWeilCauchyTest (-(t : ℂ) * Complex.I)) =
      (((1 / 2 : ℂ) + (t : ℂ))⁻¹ + ((1 / 2 : ℂ) + (t : ℂ) - 1)⁻¹ +
        logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ)) -
        LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((1 / 2 : ℂ) + (t : ℂ))) / (t : ℂ) := by
  have htpos : (0 : ℝ) < t := by linarith
  rw [xiWeilPolarization_cauchyTest_eq_logDeriv htpos]
  congr 1
  have hre : 1 < ((1 / 2 : ℂ) + (t : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]
    have h12 : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    rw [h12]
    linarith
  have hζ : riemannZeta ((1 / 2 : ℂ) + (t : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hre
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hlogζ : logDeriv riemannZeta ((1 / 2 : ℂ) + (t : ℂ)) =
      -LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        ((1 / 2 : ℂ) + (t : ℂ)) := by
    rw [logDeriv_apply, hL]
    ring
  rw [logDeriv_xi_split hre, hlogζ]
  ring

end

end RHTower
