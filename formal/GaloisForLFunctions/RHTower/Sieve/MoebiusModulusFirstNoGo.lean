import GaloisForLFunctions.RHTower.Sieve.CharacterDistanceGrowth
import GaloisForLFunctions.RHTower.Sieve.CesaroKernelVertical
import GaloisForLFunctions.RHTower.Sieve.CesaroKernelPrimitives
import GaloisForLFunctions.RHTower.Sieve.HalaszIntegralBound
import GaloisForLFunctions.RHTower.Sieve.EulerBoundLSeries
import GaloisForLFunctions.RHTower.MobiusEvenIndexPositiveRecurrence

/-!
# The modulus-first family cannot save anything for Möbius

Every route that passes from a contour integral to a bound of the shape

`‖∑_{n ≤ N} μ(n)log(x/n)‖ ≤ (arithmetic error) + (1/2π)·A`,   `A ≥ ∫_{|t| ≤ T} ‖L(μ,σ+it)x^s/s²‖ dt`,

replaces the integral of a complex-valued function by the integral of its modulus, and that step alone
caps the outcome.  On the segment `1/2 ≤ |t| ≤ 1` the pole bound gives `‖ζ(σ+it)‖ ≤ 7`, so
`‖L(μ,σ+it)‖ = ‖ζ(σ+it)‖⁻¹ ≥ 1/7`, while the kernel is at least `x^σ/5`.  Hence

`A ≥ x^σ/70`

for every `1 < σ ≤ 2`, `T ≥ 1` and `x > 0`: the analytic term of any such route is `≍ x^σ`, which at
`x = N` is the trivial size of the sum itself.  No choice of analytic estimate inside the family can
give `o(N)`, so the cancellation in `∑ μ(n)` is inaccessible to it — it lives in the phase of the
integrand, which the modulus discards.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **`ζ` is bounded by `7` on the unit segment above the 1-line.** -/
theorem norm_riemannZeta_le_seven {s : ℂ} (hσ1 : 1 ≤ s.re) (hσ2 : s.re ≤ 2)
    (ht1 : 1 / 2 ≤ |s.im|) (ht2 : |s.im| ≤ 1) : ‖riemannZeta s‖ ≤ 7 := by
  have ht0 : (0 : ℝ) < |s.im| := by linarith
  have hne : s.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht1
    linarith
  have hbound := norm_riemannZeta_le_inv_abs_im hσ1 hσ2 (by linarith) hne
  have hinv : 1 / |s.im| ≤ 2 := by
    rw [div_le_iff₀ ht0]
    linarith
  linarith

/-- **The Möbius series is bounded below on the unit segment above the 1-line.**  Its product with
`ζ` is `1`, and `ζ` is bounded there. -/
theorem inv_seven_le_norm_LSeries_moebiusCoeffC {s : ℂ} (hσ1 : 1 < s.re) (hσ2 : s.re ≤ 2)
    (ht1 : 1 / 2 ≤ |s.im|) (ht2 : |s.im| ≤ 1) :
    1 / 7 ≤ ‖LSeries moebiusCoeffC s‖ := by
  have hprod : riemannZeta s * LSeries moebiusCoeffC s = 1 := by
    have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hσ1
    rwa [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hσ1] at h
  have hnorm : ‖riemannZeta s‖ * ‖LSeries moebiusCoeffC s‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  have hζ := norm_riemannZeta_le_seven hσ1.le hσ2 ht1 ht2
  have hL0 : (0 : ℝ) ≤ ‖LSeries moebiusCoeffC s‖ := norm_nonneg _
  nlinarith [hnorm, hζ, hL0]

/-- The Möbius series is continuous on every vertical line right of `1`. -/
theorem continuous_LSeries_moebiusCoeffC_line {σ : ℝ} (hσ : 1 < σ) :
    Continuous fun t : ℝ => LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have heq : (fun t : ℝ => LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I))
      = fun t : ℝ => ∑' n : ℕ, twistedSummand moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I) n := by
    funext t
    exact LSeries_eq_tsum_twistedSummand (line_ne_zero hσ0 t)
  rw [heq]
  exact continuous_tsum_twistedSummand norm_moebiusCoeff_le_one hσ

/-- **The modulus-first integral for Möbius is at least `x^σ/70`.**  A lower bound on a segment of
length `1/2` where both the series and the kernel are bounded below. -/
theorem norm_cesaro_integral_moebiusCoeffC_lower {σ x T : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hx : 0 < x) (hT : 1 ≤ T) :
    x ^ σ / 70 ≤ ∫ t in (-T)..T,
      ‖LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I)
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖ := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  set F : ℝ → ℝ := fun t =>
    ‖LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2)
    with hF
  have hLc : Continuous fun t : ℝ => LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_moebiusCoeffC_line hσ1
  have hKc : Continuous fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := by
    have hKeq : (fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2)
        = fun t : ℝ => x ^ σ * (1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) := by
      funext t
      rw [mul_one_div]
    rw [hKeq]
    exact continuous_const.mul (continuous_inv_normSq_line hσ0)
  have hFc : Continuous F := hLc.norm.mul hKc
  have hFnn : ∀ t : ℝ, 0 ≤ F t := fun t =>
    mul_nonneg (norm_nonneg _) (div_nonneg hxσ.le (by positivity))
  -- the integrand is bounded below on the segment
  have hlow : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, x ^ σ / 35 ≤ F t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have habs : |t| = t := abs_of_pos (by linarith [ht.1])
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    have him : ((σ : ℂ) + (t : ℝ) * I).im = t := by simp
    have hL : 1 / 7 ≤ ‖LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I)‖ := by
      refine inv_seven_le_norm_LSeries_moebiusCoeffC (by rw [hre]; exact hσ1)
        (by rw [hre]; exact hσ2) ?_ ?_
      · rw [him, habs]; exact ht.1
      · rw [him, habs]; exact ht.2
    have hden : ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 ≤ 5 := by
      rw [normSq_line]
      nlinarith [ht.1, ht.2, hσ1, hσ2]
    have hker : x ^ σ / 5 ≤ x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := by
      refine div_le_div_of_nonneg_left hxσ.le ?_ hden
      have hpos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := by
        have := line_ne_zero hσ0 t
        positivity
      exact hpos
    have hLnn : (0 : ℝ) ≤ ‖LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I)‖ := norm_nonneg _
    have hknn : (0 : ℝ) ≤ x ^ σ / 5 := by positivity
    calc x ^ σ / 35 = (1 / 7) * (x ^ σ / 5) := by ring
      _ ≤ ‖LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / 5) :=
          mul_le_mul_of_nonneg_right hL hknn
      _ ≤ F t := mul_le_mul_of_nonneg_left hker hLnn
  -- integrate the lower bound on the segment
  have hseg := intervalIntegral.integral_mono_on (a := (1 / 2 : ℝ)) (b := 1) (by norm_num)
    ((continuous_const (y := x ^ σ / 35)).intervalIntegrable (μ := volume) _ _)
    (hFc.intervalIntegrable (μ := volume) _ _) hlow
  rw [intervalIntegral.integral_const, smul_eq_mul] at hseg
  have hval : ((1 : ℝ) - 1 / 2) * (x ^ σ / 35) = x ^ σ / 70 := by ring
  rw [hval] at hseg
  -- extend to the whole range
  have hmono : (∫ t in (1 / 2 : ℝ)..1, F t) ≤ ∫ t in (-T)..T, F t := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by norm_num) hT ?_
      (hFc.intervalIntegrable (μ := volume) _ _)
    filter_upwards with t
    exact hFnn t
  have hcongr : (∫ t in (-T)..T,
        ‖LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖)
      = ∫ t in (-T)..T, F t :=
    intervalIntegral.integral_congr fun t _ => norm_cesaro_integrand hx _ σ t
  rw [hcongr]
  linarith [hseg, hmono]

/-- **The no-go.**  Any bound for the modulus of the Cesàro integral of the Möbius series is at least
`x^σ/70`, so no route of that shape can produce a saving. -/
theorem le_of_norm_cesaro_integral_moebiusCoeffC_le {σ x T A : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hx : 0 < x) (hT : 1 ≤ T)
    (hA : (∫ t in (-T)..T,
        ‖LSeries moebiusCoeffC ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖) ≤ A) :
    x ^ σ / 70 ≤ A :=
  le_trans (norm_cesaro_integral_moebiusCoeffC_lower hσ1 hσ2 hx hT) hA

end RHTower.Sieve
end
