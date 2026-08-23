import GaloisForLFunctions.RHTower.XiWeilHardyFiberDeflatedCentralBand

/-!
# Positive-frequency Hardy-fiber Poisson criterion

The fixed-fiber Poisson margin is already unconditional on `|Re z| ≤ 4`.  The source trace obeys
the exact involution `z ↦ -conj z`, while ordinary conjugation of a Xi divisor point sends its
centered coordinate `α` to `-conj α`, preserves multiplicity, and transports its Poisson kernel
without loss.

Consequently one need not prove a whole-strip inequality.  For any critical Xi fiber `ρ`, RH is
equivalent to its positive-frequency Poisson margin above four.  Indeed that positive margin first
implies the ordinary positive-tail source sign; the existing source reflection and the preceding
unconditional central theorem then discharge every other frequency.  A symmetric two-channel
assembly with the Schwarz-conjugate fiber is also recorded, but is not needed for the sharp
criterion.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The remaining positive-frequency quantitative source obligation for one fixed Xi fiber. -/
def FixedFiberPrimeGammaPositiveHighPoissonMargin (ρ : XiDivisorSupport) : Prop :=
  ∀ z : ℂ, 4 < z.re → 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
      ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
          Complex.normSq (xiSpectralPointSupport ρ - z) ≤
        -(continuedPrimeArchSourceRelativeTrace z).im

/-- Ordinary conjugation preserves the multiplicity-weighted Poisson floor after applying the
source reflection `z ↦ -conj z`. -/
theorem fixedFiberPoissonFloor_zeroConj_negConj
    (ρ : XiDivisorSupport) (z : ℂ) :
    ((xiZeroCopyFiber (xiZeroConjEquiv ρ)).card : ℝ) *
          (-(starRingEnd ℂ) z).im /
        Complex.normSq
          (xiSpectralPointSupport (xiZeroConjEquiv ρ) -
            (-(starRingEnd ℂ) z)) =
      ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
        Complex.normSq (xiSpectralPointSupport ρ - z) := by
  have hcard :
      (xiZeroCopyFiber (xiZeroConjEquiv ρ)).card =
        (xiZeroCopyFiber ρ).card := by
    rw [card_xiZeroCopyFiber, card_xiZeroCopyFiber]
    change Int.toNat ((MeromorphicOn.divisor xi Set.univ)
      ((starRingEnd ℂ) (ρ : ℂ))) =
        Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))
    rw [xi_divisor_conj]
  have hden :
      Complex.normSq
          (-(starRingEnd ℂ) (xiSpectralPointSupport ρ) -
            (-(starRingEnd ℂ) z)) =
        Complex.normSq (xiSpectralPointSupport ρ - z) := by
    rw [show
      -(starRingEnd ℂ) (xiSpectralPointSupport ρ) -
          (-(starRingEnd ℂ) z) =
        -(starRingEnd ℂ) (xiSpectralPointSupport ρ - z) by
      rw [map_sub]
      ring]
    rw [Complex.normSq_neg, Complex.normSq_conj]
  rw [hcard, xiSpectralPointSupport_zeroConj]
  unfold xiCenteredNegConj
  rw [hden]
  simp

/-- Two positive-frequency channels recover the global Poisson margin: the original critical
fiber pays the positive tail and its Schwarz conjugate pays the reflected negative tail. -/
theorem fixedFiberPrimeGammaPoissonMargin_of_positiveHigh_self_and_zeroConj
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (hpositive : FixedFiberPrimeGammaPositiveHighPoissonMargin ρ)
    (hpositiveConj :
      FixedFiberPrimeGammaPositiveHighPoissonMargin (xiZeroConjEquiv ρ)) :
    FixedFiberPrimeGammaPoissonMargin ρ := by
  intro z hzIm hzHalf hzeta
  by_cases hzCentral : |z.re| ≤ 4
  · exact fixedCriticalFiber_primeGammaPoissonMargin_four
      ρ hρ z hzIm hzHalf hzCentral
  by_cases hzPositive : 4 < z.re
  · exact hpositive z hzPositive hzIm hzHalf hzeta
  · have hzNegative : z.re < -4 := by
      apply lt_of_not_ge
      intro hminus
      apply hzCentral
      rw [abs_le]
      exact ⟨hminus, le_of_not_gt hzPositive⟩
    let w : ℂ := -(starRingEnd ℂ) z
    have hwRe : 4 < w.re := by
      dsimp only [w]
      simp only [Complex.neg_re, Complex.conj_re]
      linarith
    have hwIm : 0 < w.im := by
      dsimp only [w]
      simp only [Complex.neg_im, Complex.conj_im, neg_neg]
      exact hzIm
    have hwHalf : w.im < 1 / 2 := by
      dsimp only [w]
      simp only [Complex.neg_im, Complex.conj_im, neg_neg]
      exact hzHalf
    have hreflect :=
      continuedPrimeArchSourceRelativeTrace_neg_conj_im z hzIm hzHalf hzeta
    have hwMargin :=
      hpositiveConj w hwRe hwIm hwHalf (by simpa only [w] using hreflect.1)
    rw [show w = -(starRingEnd ℂ) z by rfl,
      fixedFiberPoissonFloor_zeroConj_negConj ρ z, hreflect.2] at hwMargin
    exact hwMargin

/-- A positive-frequency Poisson margin implies the ordinary positive-frequency source sign: the
deleted critical atom has nonnegative upper-half-plane Poisson mass. -/
theorem continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_of_fixedFiberMargin
    (ρ : XiDivisorSupport)
    (hmargin : FixedFiberPrimeGammaPositiveHighPoissonMargin ρ) :
    ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz := by
  intro z hzIm hzHalf hzRe hzeta
  have hz := hmargin z hzRe hzIm hzHalf hzeta
  have hfloor : 0 ≤ ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
      Complex.normSq (xiSpectralPointSupport ρ - z) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hzIm.le)
      (Complex.normSq_nonneg _)
  linarith

/-- Sharp ultraviolet reduction: for one fixed critical fiber, its quantitative Poisson margin
only on positive frequencies above four is exactly RH. -/
theorem riemannHypothesis_iff_fixedCriticalFiber_positiveHighPoissonMargin
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    RiemannHypothesis ↔ FixedFiberPrimeGammaPositiveHighPoissonMargin ρ := by
  constructor
  · intro hRH z _hzRe hzIm hzHalf hzeta
    exact ((riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMargin
      ρ hρ).mp hRH) z hzIm hzHalf hzeta
  · intro hmargin
    exact riemannHypothesis_of_continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz
      (continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_of_fixedFiberMargin
        ρ hmargin)

/-- Symmetric two-channel corollary: retaining both ordinary-conjugate Poisson margins also gives
an exact positive-frequency criterion. -/
theorem riemannHypothesis_iff_fixedCriticalFiber_positiveHighPoissonMargins
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    RiemannHypothesis ↔
      FixedFiberPrimeGammaPositiveHighPoissonMargin ρ ∧
        FixedFiberPrimeGammaPositiveHighPoissonMargin (xiZeroConjEquiv ρ) := by
  have hρConj : ((xiZeroConjEquiv ρ : XiDivisorSupport) : ℂ).re = 1 / 2 := by
    change ((starRingEnd ℂ) (ρ : ℂ)).re = 1 / 2
    simpa only [Complex.conj_re] using hρ
  constructor
  · intro hRH
    have hfull :=
      (riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMargin ρ hρ).mp hRH
    have hfullConj :=
      (riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMargin
        (xiZeroConjEquiv ρ) hρConj).mp hRH
    exact ⟨
      fun z _hzRe hzIm hzHalf hzeta => hfull z hzIm hzHalf hzeta,
      fun z _hzRe hzIm hzHalf hzeta => hfullConj z hzIm hzHalf hzeta⟩
  · rintro ⟨hpositive, hpositiveConj⟩
    apply (riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMargin ρ hρ).mpr
    exact fixedFiberPrimeGammaPoissonMargin_of_positiveHigh_self_and_zeroConj
      ρ hρ hpositive hpositiveConj

/-- Hardy supplies an unconditional pair of critical fibers for the two-channel positive-frequency
criterion. -/
theorem exists_hardyCriticalFiber_positiveHighPoissonMargins_criterion :
    ∃ ρ : XiDivisorSupport,
      (ρ : ℂ).re = 1 / 2 ∧
        (RiemannHypothesis ↔
          FixedFiberPrimeGammaPositiveHighPoissonMargin ρ ∧
            FixedFiberPrimeGammaPositiveHighPoissonMargin (xiZeroConjEquiv ρ)) := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  exact ⟨ρ, hρ,
    riemannHypothesis_iff_fixedCriticalFiber_positiveHighPoissonMargins ρ hρ⟩

/-- Hardy supplies one unconditional critical fiber for the sharp one-channel positive-frequency
Poisson-margin criterion. -/
theorem exists_hardyCriticalFiber_positiveHighPoissonMargin_criterion :
    ∃ ρ : XiDivisorSupport,
      (ρ : ℂ).re = 1 / 2 ∧
        (RiemannHypothesis ↔
          FixedFiberPrimeGammaPositiveHighPoissonMargin ρ) := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  exact ⟨ρ, hρ,
    riemannHypothesis_iff_fixedCriticalFiber_positiveHighPoissonMargin ρ hρ⟩

end

end RHTower
