import GaloisForLFunctions.ArithmeticElectrostatics.TheStabilityLawAtAtomicResolution
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCovariantCountertermIsTheAnomaly

/-!
# The matched stability law

AES proves the stability law at atomic resolution: the Markov form `M = archForm − primeSum` of an
atomic test (bumps of width `w` at the points `log n`, `n ≤ N`) is nonnegative once the archimedean
Lévy gain `e^{−1/2} log(δ_N/(2w))` beats the prime counterterm (`markovEnergy_atomicTest_ge`). It
uses the Schur bound `2 log N + O(1)`. With the covariant counterterm `log N + O(1)` of
`TheCovariantCountertermIsTheAnomaly` the same argument gives the matched law.

* **The matched stability law, quantitative form** (`markovEnergy_atomicTest_ge_matched`):
  `M(f) ≥ (2θ′(0) + e^{−1/2} log(δ_N/(2w)) − log N − log 4 − 4) ∫ f²`.
* **The matched width** (`matchedAtomicGain_nonneg`, `markovEnergy_atomicTest_nonneg_matched`):
  `M(f) ≥ 0` for every width `w ≤ (δ_N/4) exp(−e^{1/2}(log N + log 4 + 4 + 2|θ′(0)|))`. The power of
  `N` in the admissible width is halved: `δ_N N^{−e^{1/2}}` instead of `δ_N N^{−2e^{1/2}}`.

The remaining gap to the atomic spacing `δ_N ≍ 1/N` is the constant `e^{−1/2}` of the Lévy gain: a
gain `log(1/w)` with constant one would match the covariant counterterm at width `N^{−O(1)}` with
exponent one, and the matched stability law at width `c/N` asks for the archimedean place to pay with
the shifts beyond the atomic spacing as well.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticEffectivityTheory

variable {g : ℝ → ℝ} {w : ℝ}

/-- **The matched stability law, quantitative form**: with the covariant counterterm,
`M(f) ≥ (2θ′(0) + e^{−1/2} log(δ_N/(2w)) − log N − log 4 − 4) ∫ f²`. -/
theorem markovEnergy_atomicTest_ge_matched (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 4) (x : ℕ → ℝ) :
    (2 * gammaHardyPhaseRate 0 + Real.exp (-(1 / 2)) * Real.log (atomSpacing N / 2 / w) -
        (Real.log N + (Real.log 4 + 4))) * ∫ u, atomicTest N x g u ^ 2 ≤
      markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  have hδ := atomSpacing_pos hN
  have hw' : w < atomSpacing N := by linarith
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_atomicTest hg hgc hgsupp hw' x]
  have hlevy := levyEnergy_atomicTest_ge hg hgsupp hN hw0 hw x
  have hsq := integral_atomicTest_sq hg hgc hgsupp hw' x
  have hW := atomicWeilForm_le_log N x
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hprime : (∫ u, g u ^ 2) * atomicWeilForm N x ≤
      (Real.log N + (Real.log 4 + 4)) * ∫ u, atomicTest N x g u ^ 2 := by
    rw [hsq]
    calc (∫ u, g u ^ 2) * atomicWeilForm N x
        ≤ (∫ u, g u ^ 2) * ((Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) :=
          mul_le_mul_of_nonneg_left hW hG
      _ = _ := by ring
  nlinarith

/-- The **matched atomic width** `(δ_N/4) exp(−e^{1/2}(log N + log 4 + 4 + 2|θ′(0)|))`. -/
def matchedAtomicWidth (N : ℕ) : ℝ :=
  atomSpacing N / 4 *
    Real.exp (-(Real.exp (1 / 2) * (Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0|)))

theorem matchedAtomicWidth_pos {N : ℕ} (hN : 1 ≤ N) : 0 < matchedAtomicWidth N :=
  mul_pos (by linarith [atomSpacing_pos hN]) (Real.exp_pos _)

/-- `atomicWidth N ≤ matchedAtomicWidth N`: the matched width is larger. -/
theorem atomicWidth_le_matchedAtomicWidth (N : ℕ) : atomicWidth N ≤ matchedAtomicWidth N := by
  unfold atomicWidth matchedAtomicWidth
  have hlog := Real.log_natCast_nonneg N
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_
  · have : 0 ≤ Real.exp (1 / 2) * Real.log N := mul_nonneg (Real.exp_pos _).le hlog
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [atomSpacing]
    · linarith [atomSpacing_pos hN]

/-- **The matched gain beats the covariant counterterm** at every width
`0 < w ≤ matchedAtomicWidth N`. -/
theorem matchedAtomicGain_nonneg {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ matchedAtomicWidth N) :
    w ≤ atomSpacing N / 4 ∧ 0 ≤ 2 * gammaHardyPhaseRate 0 + Real.exp (-(1 / 2)) *
      Real.log (atomSpacing N / 2 / w) - (Real.log N + (Real.log 4 + 4)) := by
  have hδ := atomSpacing_pos hN
  set X := Real.exp (1 / 2) * (Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0|)
  have hX : 0 ≤ X := by
    have := Real.log_natCast_nonneg N
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hexp : Real.exp (-X) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨hw.trans (by rw [matchedAtomicWidth]; nlinarith [Real.exp_pos (-X)]), ?_⟩
  have hlog : X ≤ Real.log (atomSpacing N / 2 / w) := by
    have hle : atomSpacing N / 2 / matchedAtomicWidth N ≤ atomSpacing N / 2 / w :=
      div_le_div_of_nonneg_left (by positivity) hw0 hw
    have hval : atomSpacing N / 2 / matchedAtomicWidth N = 2 * Real.exp X := by
      rw [matchedAtomicWidth, Real.exp_neg]
      field_simp
      ring
    have h2 : X ≤ Real.log (2 * Real.exp X) := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos X).ne', Real.log_exp]
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
    exact h2.trans (Real.log_le_log (by positivity) (hval ▸ hle))
  have he : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : Real.exp (-(1 / 2)) * X ≤ Real.exp (-(1 / 2)) * Real.log (atomSpacing N / 2 / w) :=
    mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
  have h4 : Real.exp (-(1 / 2)) * X =
      Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0| := by
    simp only [X]; rw [← mul_assoc, he, one_mul]
  linarith [neg_abs_le (gammaHardyPhaseRate 0)]

/-- **The matched stability law**: every atomic test of width at most `matchedAtomicWidth N` at the
points `log n`, `n ≤ N`, has nonnegative Markov form. -/
theorem markovEnergy_atomicTest_nonneg_matched (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ matchedAtomicWidth N) (x : ℕ → ℝ) :
    0 ≤ markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  obtain ⟨hw4, hcoef⟩ := matchedAtomicGain_nonneg hN hw0 hw
  have h := markovEnergy_atomicTest_ge_matched hg hgc hgsupp hN hw0 hw4 x
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg hcoef hint) h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
