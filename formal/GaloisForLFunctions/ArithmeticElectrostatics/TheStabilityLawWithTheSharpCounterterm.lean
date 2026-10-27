import GaloisForLFunctions.ArithmeticElectrostatics.TheGaugeIsInvisibleAtAtomicResolution
import GaloisForLFunctions.ArithmeticElectrostatics.TheWeilFormAtAtomicResolution
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCovariantCountertermIsTheAnomaly

/-!
# The stability law with the sharp counterterm

The stability law at atomic resolution (`TheStabilityLawAtAtomicResolution`) pays the prime form with
the Schur bound `2 log N + O(1)`. The covariant counterterm is `log N + O(1)` exactly: Schur's test
with the pole vector `u_n = n^{−1/2}` gives `P_N(x) ≤ (log N + log 4 + 4)|x|²`
(RAPT `atomicWeilForm_le_log`), and the pole vector attains it, `P_N(u) ≥ (log N − log 8 − 4)|u|²`
(RAPT `atomicWeilForm_poleVector_ge`). This file runs the stability law on the sharp counterterm.

* **The width at a counterterm** (`widthAt`, `gain_nonneg_of_le_widthAt`): the Lévy gain
  `e^{−1/2} log(δ_N/(2w))` beats `κ − 2θ′(0)` for every width
  `w ≤ widthAt N κ = (δ_N/4) exp(−e^{1/2}(κ + 2|θ′(0)|))`.
* **The sharp stability law** (`markovEnergy_atomicTest_ge_sharp`, `markovEnergy_atomicTest_nonneg_sharp`):
  `M(f) ≥ (2θ′(0) + e^{−1/2} log(δ_N/(2w)) − log N − log 4 − 4) ∫ f²`, so `M ≥ 0` at every width
  `w ≤ sharpAtomicWidth N`, which is `δ_N N^{−e^{1/2}}` up to a constant — the exponent of
  `atomicWidth N` halved.
* **The counterterm is sharp** (`primeSum_poleTest_ge`, `archForm_poleTest_ge`): on the pole test
  `Σ n^{−1/2} g(u − log n)` the prime sum is at least `(log N − log 8 − 4) ∫ f²`; the archimedean
  place must supply `log N + O(1)` per unit mass, and supplies it below `sharpAtomicWidth N`.
* **For every sign twin, and with the pole** (`twinMarkovEnergy_atomicTest_nonneg_sharp`,
  `re_W_add_sinh_sq_nonneg_sharp`): the same width serves every sign twin (the prime forms are gauge
  conjugate), and Weil's form plus the rank-one counterterm `2S²` is nonnegative there.

The exponent `e^{1/2}` comes from the Lévy density on shifts below the spacing; reaching the spacing
`cδ_N` needs the archimedean cross kernel of overlapping shifts, which this file does not use.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.ArithmeticElectrostatics

open ArithmeticEffectivityTheory RenormalizedArithmeticPotentialTheory Zeta23

variable {g : ℝ → ℝ} {w : ℝ}

/-- The **width at counterterm `κ`**: `(δ_N/4) exp(−e^{1/2}(κ + 2|θ′(0)|))`. -/
def widthAt (N : ℕ) (κ : ℝ) : ℝ :=
  atomSpacing N / 4 * Real.exp (-(Real.exp (1 / 2) * (κ + 2 * |gammaHardyPhaseRate 0|)))

theorem widthAt_pos {N : ℕ} (hN : 1 ≤ N) (κ : ℝ) : 0 < widthAt N κ :=
  mul_pos (by linarith [atomSpacing_pos hN]) (Real.exp_pos _)

/-- **The Lévy gain beats a counterterm `κ ≥ 0`** at every width `0 < w ≤ widthAt N κ`. -/
theorem gain_nonneg_of_le_widthAt {N : ℕ} (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 ≤ κ) (hw0 : 0 < w)
    (hw : w ≤ widthAt N κ) :
    w ≤ atomSpacing N / 4 ∧
      0 ≤ 2 * gammaHardyPhaseRate 0 + Real.exp (-(1 / 2)) * Real.log (atomSpacing N / 2 / w) - κ := by
  have hδ := atomSpacing_pos hN
  set X := Real.exp (1 / 2) * (κ + 2 * |gammaHardyPhaseRate 0|)
  have hX : 0 ≤ X := by positivity
  have hexp : Real.exp (-X) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨hw.trans (by rw [widthAt]; nlinarith [Real.exp_pos (-X)]), ?_⟩
  have hlog : X ≤ Real.log (atomSpacing N / 2 / w) := by
    have hle : atomSpacing N / 2 / widthAt N κ ≤ atomSpacing N / 2 / w :=
      div_le_div_of_nonneg_left (by positivity) hw0 hw
    have hval : atomSpacing N / 2 / widthAt N κ = 2 * Real.exp X := by
      rw [widthAt, Real.exp_neg]
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
  have h4 : Real.exp (-(1 / 2)) * X = κ + 2 * |gammaHardyPhaseRate 0| := by
    simp only [X]; rw [← mul_assoc, he, one_mul]
  linarith [neg_abs_le (gammaHardyPhaseRate 0)]

/-- The sharp counterterm `log N + log 4 + 4`. -/
theorem sharpCounterterm_nonneg (N : ℕ) : 0 ≤ Real.log N + (Real.log 4 + 4) := by
  have := Real.log_natCast_nonneg N
  have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

/-- The **sharp atomic width** `widthAt N (log N + log 4 + 4)`. -/
def sharpAtomicWidth (N : ℕ) : ℝ := widthAt N (Real.log N + (Real.log 4 + 4))

/-- **The sharp stability law, quantitative form**:
`M(f) ≥ (2θ′(0) + e^{−1/2} log(δ_N/(2w)) − log N − log 4 − 4) ∫ f²`. -/
theorem markovEnergy_atomicTest_ge_sharp (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 4) (x : ℕ → ℝ) :
    (2 * gammaHardyPhaseRate 0 + Real.exp (-(1 / 2)) * Real.log (atomSpacing N / 2 / w) -
        (Real.log N + (Real.log 4 + 4))) * ∫ u, atomicTest N x g u ^ 2 ≤
      markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos hN]
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

/-- **The sharp stability law**: every atomic test of width at most `sharpAtomicWidth N` has
nonnegative Markov form. -/
theorem markovEnergy_atomicTest_nonneg_sharp (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ sharpAtomicWidth N) (x : ℕ → ℝ) :
    0 ≤ markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  obtain ⟨hw4, hcoef⟩ := gain_nonneg_of_le_widthAt hN (sharpCounterterm_nonneg N) hw0 hw
  have h := markovEnergy_atomicTest_ge_sharp hg hgc hgsupp hN hw0 hw4 x
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg hcoef hint) h

/-- **The counterterm is sharp**: on the pole test the prime sum is at least
`(log N − log 8 − 4) ∫ f²`. -/
theorem primeSum_poleTest_ge (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N) :
    (Real.log N - (Real.log 8 + 4)) * ∫ u, atomicTest N poleVector g u ^ 2 ≤
      primeSum (atomicTest N poleVector g) := by
  rw [primeSum_atomicTest hg hgc hgsupp hw, integral_atomicTest_sq hg hgc hgsupp hw]
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have h := mul_le_mul_of_nonneg_left (atomicWeilForm_poleVector_ge N) hG
  linarith

/-- **The archimedean place pays `log N + O(1)`**: below `sharpAtomicWidth N` the archimedean form
of the pole test is at least `(log N − log 8 − 4) ∫ f²`. -/
theorem archForm_poleTest_ge (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ sharpAtomicWidth N) :
    (Real.log N - (Real.log 8 + 4)) * ∫ u, atomicTest N poleVector g u ^ 2 ≤
      archForm (atomicTest N poleVector g) := by
  have hw4 := (gain_nonneg_of_le_widthAt hN (sharpCounterterm_nonneg N) hw0 hw).1
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos hN]
  have hM := markovEnergy_atomicTest_nonneg_sharp hg hgc hgsupp hN hw0 hw poleVector
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum (contDiff_atomicTest hg N _)
    (hasCompactSupport_atomicTest hgsupp N _)] at hM
  linarith [primeSum_poleTest_ge hg hgc hgsupp hw']

/-- **The sharp stability law for every sign twin.** -/
theorem twinMarkovEnergy_atomicTest_nonneg_sharp {ω : ArithmeticFunction ℝ}
    (hω : ∀ a b, ω (a * b) = ω a * ω b) (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) (hw : w ≤ sharpAtomicWidth N) (x : ℕ → ℝ) :
    0 ≤ archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g) := by
  obtain ⟨hw4, hcoef⟩ := gain_nonneg_of_le_widthAt hN (sharpCounterterm_nonneg N) hw0 hw
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos hN]
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [archForm_eq_levyEnergy hf hfc, (twistedPrimeSum_atomicTest hω hsign hg hgc hgsupp hw' x).2]
  have hlevy := levyEnergy_atomicTest_ge hg hgsupp hN hw0 hw4 x
  have hsq := integral_atomicTest_sq hg hgc hgsupp hw' x
  have hW := (twistedAtomicWeilForm_le_iff hω hsign N _).mpr (atomicWeilForm_le_log N) x
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hprime : (∫ u, g u ^ 2) * twistedAtomicWeilForm ω N x ≤
      (Real.log N + (Real.log 4 + 4)) * ∫ u, atomicTest N x g u ^ 2 := by
    rw [hsq]
    calc (∫ u, g u ^ 2) * twistedAtomicWeilForm ω N x
        ≤ (∫ u, g u ^ 2) * ((Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) :=
          mul_le_mul_of_nonneg_left hW hG
      _ = _ := by ring
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  nlinarith [mul_nonneg hcoef hint]

/-- **Weil's form with the rank-one counterterm at the sharp width**: `Re W(f) + 2S(f)² ≥ 0`. -/
theorem re_W_add_sinh_sq_nonneg_sharp (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ sharpAtomicWidth N) (x : ℕ → ℝ) :
    0 ≤ (zetaZeroConfig.W (fun u => (atomicTest N x g u : ℂ))
        fun u => (atomicTest N x g u : ℂ)).re + 2 * sinhHalfMoment (atomicTest N x g) ^ 2 := by
  rw [re_W_atomicTest_eq hg hgsupp N x]
  have hM := markovEnergy_atomicTest_nonneg_sharp hg hgc hgsupp hN hw0 hw x
  nlinarith [sq_nonneg (coshHalfMoment (atomicTest N x g))]

end GaloisForLFunctions.ArithmeticElectrostatics
