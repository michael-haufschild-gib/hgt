import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerCombTailConvergenceCriterion
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanMellinIntegral
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailPrimeMellinSymbol
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceMellinIntegral
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZeroPairing

/-!
# Power combs converge to their zero-side Mellin pairing

The prime-error and reference Mellin integrals cancel their zeta terms.
Together with the archimedean digamma value, the remaining expression is
`2 ξ'/ξ(1-a)/(1-2a)`, the reflected pairing of the power-tail Mellin factors.
Convergence of all these literal combs is equivalent to RH.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg)

/-- Below the actual zero-width boundary, the arithmetic Mellin limit
equals the reflected zero pairing without an assumed analytic input. -/
theorem powerTailCombMellinIntegral_eq_zeroPairing_of_add_width_lt_half
    {a : ℝ} (ha : 0 < a) (haw : a + zetaZeroWidth < 1 / 2) :
    (powerTailCombMellinIntegral a : ℂ) = powerTailZeroPairing a := by
  have ha2 : a < 1 / 2 := by linarith only [haw, zetaZeroWidth_nonneg]
  have ha1 : a < 1 := by linarith only [ha2]
  have hθ : 1 - 2 * (a : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) - 2 * a ≠ 0 by linarith only [ha2])
  have hθ' : 1 - (a : ℂ) * 2 ≠ 0 := by simpa only [mul_comm] using hθ
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hs0 : 1 - (a : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) - a ≠ 0 by linarith only [ha1])
  have hs1 : 1 - (a : ℂ) ≠ 1 := by
    intro h
    exact ha0 (by linear_combination -h)
  have hre : 0 < (1 - (a : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [ha1]
  have hζ : riemannZeta (1 - (a : ℂ)) ≠ 0 := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
      RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo
        (show 0 < 1 - a by linarith only [ha2]) (show 1 - a < 1 by linarith only [ha])
  have hxi := ArithmeticCorrespondencePositivity.logDeriv_xi_eq_add hre hs1 hζ
  have hpoles : ∀ n : ℕ, (1 - (a : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n h
    have hh := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hh
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [ha1, hh, hn]
  rw [BohrGeneratorAxis.logDeriv_GammaR _ hpoles] at hxi
  conv_rhs at hxi => rw [logDeriv_apply]
  have hprime := mul_primePowerMellinIntegral_eq_of_add_width_lt_half ha haw
  have href := mul_referencePowerMellinIntegral_eq ha ha2
  have harch := ofReal_powerTailArchimedeanRowLimit ha ha1
  have hsplit : (1 - 2 * (a : ℂ)) * (powerTailCombMellinIntegral a : ℂ) =
      (powerTailArchimedeanRowLimit a : ℂ) -
        2 * ((1 - 2 * (a : ℂ)) *
          ((∫ t in Set.Ioc (0 : ℝ) 1,
            arithmeticPowerProfile (2 * a) (powerTailPrimeDeviation a) t : ℝ) : ℂ)) -
        2 * ((1 - 2 * (a : ℂ)) *
          ((∫ t in Set.Ioc (0 : ℝ) 1, powerTailReferenceProfile a t : ℝ) : ℂ)) := by
    rw [powerTailCombMellinIntegral]
    push_cast
    field_simp [hθ, hθ']
  rw [hprime, href, harch] at hsplit
  have hmain : (1 - 2 * (a : ℂ)) * (powerTailCombMellinIntegral a : ℂ) =
      2 * logDeriv _root_.RHTower.xi (1 - (a : ℂ)) := by
    rw [hsplit, hxi]
    have hsub : 1 - (a : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp [ha0, hs0, hsub, hζ]
    ring
  apply (mul_left_cancel₀ hθ)
  rw [powerTailZeroPairing_eq_logDeriv ha2, hmain]
  field_simp [hθ, hθ']

/-- The literal power comb converges to its zero pairing throughout the
strict range determined by the actual zero width. -/
theorem tendsto_powerCombTail_zeroPairing_of_add_width_lt_half
    {a : ℝ} (ha : 0 < a) (haw : a + zetaZeroWidth < 1 / 2) :
    Tendsto (fun N => (powerCombTail a N : ℂ)) atTop (𝓝 (powerTailZeroPairing a)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_powerCombTail_of_add_width_lt_half ha haw)
  rw [powerTailCombMellinIntegral_eq_zeroPairing_of_add_width_lt_half ha haw] at h
  exact h.congr fun N => rfl

/-- Under RH the arithmetic Mellin value equals the zero pairing for every
positive subcritical power. -/
theorem powerTailCombMellinIntegral_eq_zeroPairing (hRH : RiemannHypothesis)
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    (powerTailCombMellinIntegral a : ℂ) = powerTailZeroPairing a := by
  apply powerTailCombMellinIntegral_eq_zeroPairing_of_add_width_lt_half ha
  rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH, add_zero]
  exact ha2

/-- Under RH the normalized literal power comb converges to its Mellin pairing
summed over all zeros with multiplicity. -/
theorem tendsto_powerCombTail_zeroPairing (hRH : RiemannHypothesis)
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    Tendsto (fun N => (powerCombTail a N : ℂ)) atTop (𝓝 (powerTailZeroPairing a)) := by
  apply tendsto_powerCombTail_zeroPairing_of_add_width_lt_half ha
  rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH, add_zero]
  exact ha2

/-- The zero-side Mellin limits of all positive subcritical power combs
characterize RH without an additional analytic premise. -/
theorem riemannHypothesis_iff_powerCombTails_tendsto_zeroPairings :
    RiemannHypothesis ↔ ∀ a : ℝ, 0 < a → a < 1 / 2 →
      Tendsto (fun N => (powerCombTail a N : ℂ)) atTop (𝓝 (powerTailZeroPairing a)) := by
  constructor
  · exact fun hRH a ha ha2 => tendsto_powerCombTail_zeroPairing hRH ha ha2
  · intro h
    apply riemannHypothesis_of_all_powerCombTails_converge
    intro a ha ha2
    refine ⟨(powerTailZeroPairing a).re, ?_⟩
    have hr := Complex.continuous_re.continuousAt.tendsto.comp (h a ha ha2)
    exact hr.congr fun N => by simp only [Function.comp_apply, Complex.ofReal_re]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
