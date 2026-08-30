import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureTranslatedThreeCenterReceiver
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSafeShiftRobinPlemelj

/-!
# Translated source-only HCF Plemelj covariance

The HCF height lattice may move by an arbitrary real phase, including a phase depending on the
canonical height.  This module performs the pole--Gamma--von-Mangoldt/Plemelj replacement at that
moving lattice.  Every covariance below is defined from source evaluations before scalarization;
the exact corrected off-line budget appears only in comparison theorems.

The safe-half-plane von-Mangoldt estimate is uniform in the real center.  Consequently, for every
phase sequence, the translated corrected budget differs from the translated source covariance by
`o(N)` whenever lattice cardinality is `o(N)`.  Thus translation or phase averaging introduces no
new leading arithmetic debt.
-/

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Signed von-Mangoldt channel on a real-translated finite height lattice. -/
def criticalFeatureTranslatedVonMangoldtLatticeBudget
    (theta : ℝ) (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, 2 *
    (-LSeries (LSeries.logMul
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
          (criticalFeatureEulerVMArchPoint ((k : ℝ) + theta)) -
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (criticalFeatureEulerVMArchPoint ((k : ℝ) + theta))).re

/-- Rational-boundary and Gamma channel on a real-translated finite height lattice. -/
def criticalFeatureTranslatedPoleGammaLatticeBudget
    (theta : ℝ) (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, 2 *
    (logDeriv archFactor
          (criticalFeatureEulerVMArchPoint ((k : ℝ) + theta)) -
      deriv (logDeriv archFactor)
          (criticalFeatureEulerVMArchPoint ((k : ℝ) + theta))).re

/-- Raw safe Euler jet on the translated lattice. -/
def criticalFeatureTranslatedPoleGammaVMLatticeBudget
    (theta : ℝ) (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, criticalFeaturePoleGammaVMJet ((k : ℝ) + theta)

theorem criticalFeatureTranslatedPoleGammaVMLatticeBudget_eq_channels
    (theta : ℝ) (K : Finset ℤ) :
    criticalFeatureTranslatedPoleGammaVMLatticeBudget theta K =
      criticalFeatureTranslatedVonMangoldtLatticeBudget theta K +
        criticalFeatureTranslatedPoleGammaLatticeBudget theta K := by
  rw [criticalFeatureTranslatedPoleGammaVMLatticeBudget,
    criticalFeatureTranslatedVonMangoldtLatticeBudget,
    criticalFeatureTranslatedPoleGammaLatticeBudget, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [criticalFeaturePoleGammaVMJet_eq_explicit]
  simp only [sub_re, add_re, neg_re]
  ring

/-- Compact, source-only corrected budget at a translated lattice. -/
def criticalFeatureTranslatedSourcePlemeljCorrectedLatticeBudget
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) : ℝ :=
  ∑ k ∈ K,
    (criticalFeaturePoleGammaVMJet ((k : ℝ) + theta) -
      limUnder (𝓝[>] (0 : ℝ))
        (criticalFeatureCompactPoleGammaObservable ((k : ℝ) + theta) cutoff))

/-- Translated pole--Gamma covariance before the compact cutoff is exhausted. -/
def criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) : ℝ :=
  criticalFeatureTranslatedPoleGammaLatticeBudget theta K -
    ∑ k ∈ K,
      limUnder (𝓝[>] (0 : ℝ))
        (criticalFeatureCompactPoleGammaObservable ((k : ℝ) + theta) cutoff)

/-- Infinite translated covariance.  Definition is pole--Gamma source-only. -/
def criticalFeatureTranslatedPoleGammaPlemeljCovariance
    (theta : ℝ) (K : Finset ℤ) : ℝ :=
  limUnder atTop
    (criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff theta K)

theorem criticalFeatureTranslatedSourcePlemeljCorrectedLatticeBudget_eq_channels
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) :
    criticalFeatureTranslatedSourcePlemeljCorrectedLatticeBudget theta K cutoff =
      criticalFeatureTranslatedVonMangoldtLatticeBudget theta K +
        criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff theta K cutoff := by
  rw [criticalFeatureTranslatedSourcePlemeljCorrectedLatticeBudget,
    criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff,
    Finset.sum_sub_distrib]
  change criticalFeatureTranslatedPoleGammaVMLatticeBudget theta K -
      (∑ k ∈ K, limUnder (𝓝[>] (0 : ℝ))
        (criticalFeatureCompactPoleGammaObservable ((k : ℝ) + theta) cutoff)) = _
  rw [criticalFeatureTranslatedPoleGammaVMLatticeBudget_eq_channels]
  ring

/-- Source-only translated compact budgets converge to the exact translated corrected budget. -/
theorem tendsto_criticalFeatureTranslatedSourcePlemeljCorrectedLatticeBudget
    (theta : ℝ) (K : Finset ℤ) :
    Tendsto
      (criticalFeatureTranslatedSourcePlemeljCorrectedLatticeBudget theta K)
      atTop
      (𝓝 (criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget theta K)) := by
  have hterm (k : ℤ) : Tendsto
      (fun cutoff : ℕ =>
        criticalFeaturePoleGammaVMJet ((k : ℝ) + theta) -
          limUnder (𝓝[>] (0 : ℝ))
            (criticalFeatureCompactPoleGammaObservable
              ((k : ℝ) + theta) cutoff))
      atTop
      (𝓝 (criticalFeaturePoleGammaVMJet ((k : ℝ) + theta) -
        criticalLineCriticalFeatureEnergyTrace ((k : ℝ) + theta))) :=
    tendsto_const_nhds.sub
      (tendsto_iterated_criticalFeaturePoleGammaTrace ((k : ℝ) + theta))
  have hsum := tendsto_finsetSum K (fun k _hk => hterm k)
  rw [criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget]
  change Tendsto
    (fun cutoff : ℕ => ∑ k ∈ K,
      (criticalFeaturePoleGammaVMJet ((k : ℝ) + theta) -
        limUnder (𝓝[>] (0 : ℝ))
          (criticalFeatureCompactPoleGammaObservable
            ((k : ℝ) + theta) cutoff)))
    atTop
    (𝓝 (∑ k ∈ K, criticalFeaturePrimeGammaOffLineExcess ((k : ℝ) + theta)))
  convert hsum using 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [criticalFeaturePrimeGammaOffLineExcess,
    re_criticalFeaturePrimeGammaSourceDiagonal_eq_poleGammaVMJet]

/-- Cutoff translated covariances converge to corrected budget minus translated prime channel. -/
theorem tendsto_criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff
    (theta : ℝ) (K : Finset ℤ) :
    Tendsto
      (criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff theta K)
      atTop
      (𝓝 (criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget theta K -
        criticalFeatureTranslatedVonMangoldtLatticeBudget theta K)) := by
  have h :=
    (tendsto_criticalFeatureTranslatedSourcePlemeljCorrectedLatticeBudget theta K).sub_const
      (criticalFeatureTranslatedVonMangoldtLatticeBudget theta K)
  apply h.congr'
  filter_upwards with cutoff
  rw [criticalFeatureTranslatedSourcePlemeljCorrectedLatticeBudget_eq_channels]
  ring

/-- Exact moving-lattice pre-divisor identity. -/
theorem criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget_eq_sourceCovariance_add_vm
    (theta : ℝ) (K : Finset ℤ) :
    criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget theta K =
      criticalFeatureTranslatedPoleGammaPlemeljCovariance theta K +
        criticalFeatureTranslatedVonMangoldtLatticeBudget theta K := by
  have hlim :=
    (tendsto_criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff theta K).limUnder_eq
  rw [criticalFeatureTranslatedPoleGammaPlemeljCovariance, hlim]
  ring

/-- Uniform translated prime-channel bound. -/
theorem abs_criticalFeatureTranslatedVonMangoldtLatticeBudget_le
    (theta : ℝ) (K : Finset ℤ) :
    |criticalFeatureTranslatedVonMangoldtLatticeBudget theta K| ≤
      (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) := by
  rw [criticalFeatureTranslatedVonMangoldtLatticeBudget]
  calc
    |∑ k ∈ K, 2 *
        (-LSeries (LSeries.logMul
            (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
            (criticalFeatureEulerVMArchPoint ((k : ℝ) + theta)) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint ((k : ℝ) + theta))).re| ≤
        ∑ k ∈ K, |2 *
          (-LSeries (LSeries.logMul
              (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
              (criticalFeatureEulerVMArchPoint ((k : ℝ) + theta)) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint ((k : ℝ) + theta))).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ K, 2 * criticalFeatureVonMangoldtUniformConstant := by
      gcongr with k hk
      exact abs_criticalFeatureVonMangoldtLattice_summand_le ((k : ℝ) + theta)
    _ = (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) := by simp

theorem tendsto_criticalFeatureTranslatedVonMangoldtLatticeBudget_div_of_card_div
    (theta : ℕ → ℝ) (K : ℕ → Finset ℤ) (N : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hcard : Tendsto (fun n => ((K n).card : ℝ) / N n) atTop (𝓝 0)) :
    Tendsto
      (fun n => criticalFeatureTranslatedVonMangoldtLatticeBudget (theta n) (K n) / N n)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmajor : Tendsto
      (fun n => ((K n).card : ℝ) / N n *
        (2 * criticalFeatureVonMangoldtUniformConstant)) atTop (𝓝 0) := by
    simpa using hcard.mul_const (2 * criticalFeatureVonMangoldtUniformConstant)
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hmajor
  filter_upwards [hN] with n hn
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
  calc
    |criticalFeatureTranslatedVonMangoldtLatticeBudget (theta n) (K n)| / N n ≤
        ((K n).card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) / N n :=
      div_le_div_of_nonneg_right
        (abs_criticalFeatureTranslatedVonMangoldtLatticeBudget_le (theta n) (K n)) hn.le
    _ = ((K n).card : ℝ) / N n *
        (2 * criticalFeatureVonMangoldtUniformConstant) := by ring

/-- For every moving phase, corrected budget minus translated source covariance is `o(N)`. -/
theorem tendsto_translatedCorrectedBudget_sub_sourceCovariance_div
    (theta : ℕ → ℝ) (K : ℕ → Finset ℤ) (N : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hcard : Tendsto (fun n => ((K n).card : ℝ) / N n) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget (theta n) (K n) -
          criticalFeatureTranslatedPoleGammaPlemeljCovariance (theta n) (K n)) / N n)
      atTop (𝓝 0) := by
  have hvm :=
    tendsto_criticalFeatureTranslatedVonMangoldtLatticeBudget_div_of_card_div
      theta K N hN hcard
  convert hvm using 1
  funext n
  rw [criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget_eq_sourceCovariance_add_vm]
  ring

/-- Canonical specialization: arbitrary height-dependent translation preserves the pre-divisor
`o(N)` replacement. -/
theorem tendsto_canonicalTranslatedCorrectedBudget_sub_sourceCovariance_div
    (theta : ℕ → ℝ) :
    Tendsto
      (fun n =>
        (criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget (theta n)
            (criticalFeatureCanonicalLatticeWindow n) -
          criticalFeatureTranslatedPoleGammaPlemeljCovariance (theta n)
            (criticalFeatureCanonicalLatticeWindow n)) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) :=
  tendsto_translatedCorrectedBudget_sub_sourceCovariance_div
    theta criticalFeatureCanonicalLatticeWindow criticalFeatureCanonicalZeroCount
    eventually_criticalFeatureCanonicalZeroCount_pos
    tendsto_card_criticalFeatureCanonicalLatticeWindow_div_zeroCount

/-- Any canonical asymptotic ceiling transfers across an `o(N)` perturbation. -/
theorem criticalFeatureCanonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
    {B C : ℕ → ℝ} {c : ℝ}
    (hdiff : Tendsto
      (fun n => (B n - C n) / criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0)) :
    CriticalFeatureCanonicalAsymptoticUpper B c ↔
      CriticalFeatureCanonicalAsymptoticUpper C c := by
  have htransfer (X Y : ℕ → ℝ)
      (hXY : Tendsto
        (fun n => (X n - Y n) / criticalFeatureCanonicalZeroCount n)
        atTop (𝓝 0))
      (hY : CriticalFeatureCanonicalAsymptoticUpper Y c) :
      CriticalFeatureCanonicalAsymptoticUpper X c := by
    intro eps heps
    have hY' := hY (eps / 2) (by linarith)
    have herr : ∀ᶠ n : ℕ in atTop,
        (X n - Y n) / criticalFeatureCanonicalZeroCount n < eps / 2 :=
      (tendsto_order.1 hXY).2 _ (by linarith)
    filter_upwards [hY', herr, eventually_criticalFeatureCanonicalZeroCount_pos]
      with n hYn heren hN
    have hdiffn : X n - Y n <
        (eps / 2) * criticalFeatureCanonicalZeroCount n :=
      (div_lt_iff₀ hN).mp heren
    nlinarith
  constructor
  · intro hB
    apply htransfer C B
    · have hneg := hdiff.neg
      simp only [neg_zero] at hneg
      convert hneg using 1
      funext n
      ring
    · exact hB
  · exact htransfer B C hdiff

/-- Exact canonical moving-phase source gate, valid at every ceiling constant. -/
theorem canonical_translatedCorrectedBudget_ceiling_iff_sourceCovariance_ceiling
    (theta : ℕ → ℝ) (c : ℝ) :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget (theta n)
          (criticalFeatureCanonicalLatticeWindow n)) c ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeatureTranslatedPoleGammaPlemeljCovariance (theta n)
          (criticalFeatureCanonicalLatticeWindow n)) c :=
  criticalFeatureCanonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
    (tendsto_canonicalTranslatedCorrectedBudget_sub_sourceCovariance_div theta)

end

end RHTower
