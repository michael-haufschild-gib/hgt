import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.JointAncestryRealAmplitudeDetection
import GaloisForLFunctions.RHTower.JointAncestryUndressedPositivity

/-!
# Arithmetic receivers produce the asymptotic abscissa law

RH is "zeros approach the line" plus the *asymptotic abscissa law*
(`riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`): for every `h ≥ 0`, finitely
many zeros right of `½ + h` forces none.  Height-local receivers read the first half at large
heights.  This module shows that the corpus's sparse arithmetic receivers produce the second half
unconditionally.

* **A non-attained supremum gives the law** (`asymptoticAbscissaLaw_of_not_attained`,
  `asymptoticAbscissaLaw_of_not_attainedTop`, `asymptoticAbscissaLaw_of_not_attainedTopExcess`).
  A finite nonempty set of zeros right of `½ + h` has a zero of maximal real part, and that zero
  attains the supremum of all real parts (respectively of all excesses `|β − ½|`).
* **Producers.**  Each of the following implies the asymptotic abscissa law:
  - lags `Φ(m log b)` bounded above along one geometric progression
    (`asymptoticAbscissaLaw_of_pow_integerLag_bddAbove`);
  - lags bounded above on a logarithmically dense set of integers
    (`asymptoticAbscissaLaw_of_logDense_integerLag_bddAbove`);
  - nonnegative twisted plateau Weil energies (`asymptoticAbscissaLaw_of_twistedPlateau_nonneg`);
  - real-amplitude joint-ancestry positivity at level one above some `X`
    (`asymptoticAbscissaLaw_of_jasRealPositiveAbove`);
  - dressed joint-ancestry positivity at some level `σ ≤ 1`, through its "RH or off-line chain"
    dichotomy (`asymptoticAbscissaLaw_of_offLine_chain`, `asymptoticAbscissaLaw_of_jasDressedPSD`).

So RH splits into two halves read by two different receiver classes: zeros approaching the line
(height-local, large-height receivers: Hadamard positivity, Gaussian central gap, cosine levels,
subtracted lags) and the asymptotic abscissa law (sparse arithmetic samples and twisted Weil
energies, through the exclusion of an attained top).
-/

open Complex Set

namespace RHTower

noncomputable section

open BacklundConverse LindelofSparse

/-- **A non-attained supremum of real parts gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_not_attained
    (h : ∀ q₀ : XiZeroCopy, ∃ q : XiZeroCopy, (q₀.1 : ℂ).re < (q.1 : ℂ).re) :
    AsymptoticAbscissaLaw := by
  intro b _ hF q₀
  by_contra hlt
  push Not at hlt
  obtain ⟨q₁, hq₁F, hmax⟩ := hF.exists_maximalFor (fun q => (q.1 : ℂ).re) _ ⟨q₀, hlt⟩
  obtain ⟨q, hq⟩ := h q₁
  have hq₁ : 1 / 2 + b < (q₁.1 : ℂ).re := hq₁F
  have hqF : q ∈ {q : XiZeroCopy | 1 / 2 + b < (q.1 : ℂ).re} := by
    simp only [mem_setOf_eq]; linarith
  exact absurd (hmax hqF hq.le) (not_le.mpr hq)

/-- **The absence of an attained top above the line gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_not_attainedTop
    (h : ¬ ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀) : AsymptoticAbscissaLaw := by
  intro b hb hF q₀
  by_contra hlt
  push Not at hlt
  obtain ⟨q₁, hq₁F, hmax⟩ := hF.exists_maximalFor (fun q => (q.1 : ℂ).re) _ ⟨q₀, hlt⟩
  have hq₁ : 1 / 2 + b < (q₁.1 : ℂ).re := hq₁F
  refine h ⟨(q₁.1 : ℂ).re, by linarith, ⟨q₁, rfl⟩, fun q => ?_⟩
  by_cases hq : q ∈ {q : XiZeroCopy | 1 / 2 + b < (q.1 : ℂ).re}
  · by_contra hgt
    push Not at hgt
    exact absurd (hmax hq hgt.le) (not_le.mpr hgt)
  · simp only [mem_setOf_eq, not_lt] at hq
    linarith

/-- **The absence of an attained top excess gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_not_attainedTopExcess (h : ¬ AttainedTopExcess) :
    AsymptoticAbscissaLaw := by
  intro b hb hF q₀
  by_contra hlt
  push Not at hlt
  have hEfin : {q : XiZeroCopy | b < |(xiSpectralPoint q).im|}.Finite :=
    finite_abs_spectral_im_gt_of_finite_re_gt hF
  have hq₀E : q₀ ∈ {q : XiZeroCopy | b < |(xiSpectralPoint q).im|} := by
    simp only [mem_setOf_eq]
    rw [spectral_im_eq, abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  obtain ⟨q₁, hq₁E, hmax⟩ :=
    hEfin.exists_maximalFor (fun q => |(xiSpectralPoint q).im|) _ ⟨q₀, hq₀E⟩
  have hq₁ : b < |(xiSpectralPoint q₁).im| := hq₁E
  refine h ⟨|(xiSpectralPoint q₁).im|, by linarith, q₁, rfl, fun q => ?_⟩
  by_cases hq : q ∈ {q : XiZeroCopy | b < |(xiSpectralPoint q).im|}
  · by_contra hgt
    push Not at hgt
    exact absurd (hmax hq hgt.le) (not_le.mpr hgt)
  · simp only [mem_setOf_eq, not_lt] at hq
    linarith

/-- RH gives the asymptotic abscissa law. -/
theorem asymptoticAbscissaLaw_of_riemannHypothesis (hRH : RiemannHypothesis) :
    AsymptoticAbscissaLaw :=
  (riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mp hRH).2

/-- **Bounded lags along one geometric progression produce the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_pow_integerLag_bddAbove {b : ℕ} (hb : 2 ≤ b) {M : ℝ}
    (hM : ∀ m : ℕ, integerLag (b ^ m) ≤ M) : AsymptoticAbscissaLaw := by
  rcases riemannHypothesis_or_not_attained_of_forall_le hb hM with hRH | h
  · exact asymptoticAbscissaLaw_of_riemannHypothesis hRH
  · exact asymptoticAbscissaLaw_of_not_attained h

/-- **Bounded lags on a logarithmically dense set produce the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_logDense_integerLag_bddAbove {N : Set ℕ}
    (hN : ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ L : ℝ, X ≤ L → ∃ n ∈ N, |Real.log n - L| ≤ δ)
    {M : ℝ} (hM : ∀ n ∈ N, integerLag n ≤ M) : AsymptoticAbscissaLaw := by
  rcases riemannHypothesis_or_not_attained_of_logDense_bddAbove hN hM with hRH | h
  · exact asymptoticAbscissaLaw_of_riemannHypothesis hRH
  · exact asymptoticAbscissaLaw_of_not_attainedTop h

/-- **Nonnegative twisted plateau Weil energies produce the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_twistedPlateau_nonneg
    (h : ∀ γ : ℝ, ∀ a : ℝ, ∀ ha0 : 0 ≤ a, 1 / 2 ≤ a →
      0 ≤ (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ)
            (twistedOddTest (plateauProfile a ha0) γ)).re) :
    AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_not_attainedTopExcess (not_attainedTopExcess_of_twistedPlateau_nonneg h)

/-- **Real-amplitude joint-ancestry positivity at level one produces the asymptotic abscissa
law.**  An attained largest distance `δ ∈ (0, ½)` lies below the level `1 < 1 + δ`, where the
edge of the prime range detects it (`not_jasRealPositiveAbove_of_maximal_offLine`). -/
theorem asymptoticAbscissaLaw_of_jasRealPositiveAbove {X : ℕ} (h : JasRealPositiveAbove X 1) :
    AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_not_attainedTopExcess ?_
  rintro ⟨Θ, hΘ, q₀, hq₀, hall⟩
  have hdist : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = |(xiSpectralPoint q).im| := by
    intro q; rw [spectral_im_eq, abs_sub_comm]
  have hoff : (q₀.1 : ℂ).re ≠ 1 / 2 := by
    intro hre
    have := hdist q₀
    rw [hre, sub_self, abs_zero, hq₀] at this
    linarith
  have hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := by
    intro q; rw [hdist q, hdist q₀, hq₀]; exact hall q
  have hlt : |(q₀.1 : ℂ).re - 1 / 2| < 1 := by
    rw [hdist q₀]; linarith [abs_spectral_im_lt_half q₀]
  have hpos : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  exact not_jasRealPositiveAbove_of_maximal_offLine q₀ hoff hmax hlt (by linarith) X h

/-- **An off-line chain gives the asymptotic abscissa law.**  If every off-line zero is strictly
exceeded in distance from the line by another zero, a finite nonempty set of zeros at distance
`> h` has no farthest element, which is impossible. -/
theorem asymptoticAbscissaLaw_of_offLine_chain
    (h : ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
      ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2|) :
    AsymptoticAbscissaLaw := by
  intro b hb hF q₀
  by_contra hlt
  push Not at hlt
  have hdist : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = |(xiSpectralPoint q).im| := by
    intro q; rw [spectral_im_eq, abs_sub_comm]
  set E : Set XiZeroCopy := {q | b < |(xiSpectralPoint q).im|} with hE
  have hEfin : E.Finite := finite_abs_spectral_im_gt_of_finite_re_gt hF
  have hq₀E : q₀ ∈ E := by
    simp only [hE, mem_setOf_eq]; rw [← hdist, abs_of_pos (by linarith)]; linarith
  obtain ⟨q₁, hq₁E, hmax⟩ :=
    hEfin.exists_maximalFor (fun q => |(xiSpectralPoint q).im|) E ⟨q₀, hq₀E⟩
  have hq₁ : b < |(xiSpectralPoint q₁).im| := hq₁E
  have hoff : (q₁.1 : ℂ).re ≠ 1 / 2 := by
    intro hre
    have := hdist q₁
    rw [hre, sub_self, abs_zero] at this
    linarith
  obtain ⟨q, hq⟩ := h q₁ hoff
  rw [hdist, hdist] at hq
  have hqE : q ∈ E := by simp only [hE, mem_setOf_eq]; linarith
  exact absurd (hmax hqE hq.le) (not_le.mpr hq)

/-- **Dressed joint-ancestry positivity at a level `σ ≤ 1` produces the asymptotic abscissa
law.** -/
theorem asymptoticAbscissaLaw_of_jasDressedPSD {σ : ℝ} (hσ : σ ≤ 1) (h : JasDressedPSD σ) :
    AsymptoticAbscissaLaw := by
  rcases riemannHypothesis_or_offLine_chain_of_jasDressedPSD hσ h with hRH | hc
  · exact asymptoticAbscissaLaw_of_riemannHypothesis hRH
  · exact asymptoticAbscissaLaw_of_offLine_chain hc

end

end RHTower
