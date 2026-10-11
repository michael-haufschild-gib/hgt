import GaloisForLFunctions.RHTower.PaperPrimePowerDefect
import GaloisForLFunctions.HTGeometry.PaperDiagonalCluster

/-!
# Compact-ideal separation of the literal DR and PBM coefficient operators

The common pole subtraction is compact. The difference of the two regularized rows has
operator norm and essential norm exactly `1/2`, witnessed by the escaping prime squares.
Applying the proven TraceCone ideal weight gives infinite cost for this difference, unchanged
by every compact correction. This is an arithmetic invariant, not a convergence producer.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Filter
open scoped Topology ENNReal

abbrev PaperPrimeCoefficientSpace := lp (fun _ : ℕ => ℂ) 2

/-- The literal logarithmic coefficient multiplier before pole subtraction. -/
def paperLogZetaRawOperator : PaperPrimeCoefficientSpace →L[ℂ] PaperPrimeCoefficientSpace :=
  lpDiagonalCLM (fun n => (paperLogZetaRawCoeff n : ℂ)) zero_le_one
    (fun n => by simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperLogZetaRawCoeff_bounds n).1] using (paperLogZetaRawCoeff_bounds n).2)

/-- The literal prime indicator multiplier. -/
def paperPrimeIndicatorOperator : PaperPrimeCoefficientSpace →L[ℂ] PaperPrimeCoefficientSpace :=
  lpDiagonalCLM (fun n => (paperPrimeIndicatorCoeff n : ℂ)) zero_le_one
    (fun n => by simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperPrimeIndicatorCoeff_bounds n).1] using (paperPrimeIndicatorCoeff_bounds n).2)

/-- The common, compact pole subtraction operator. -/
def paperPrimePoleOperator : PaperPrimeCoefficientSpace →L[ℂ] PaperPrimeCoefficientSpace :=
  paperConvergentDiagonal (fun n => (paperPrimePoleCoeff n : ℂ))
    (Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_paperPrimePoleCoeff)

def paperLogZetaRegOperator := paperLogZetaRawOperator - paperPrimePoleOperator

def paperPrimeRegOperator := paperPrimeIndicatorOperator - paperPrimePoleOperator

@[simp] theorem paperLogZetaRegOperator_apply (f : PaperPrimeCoefficientSpace) (n : ℕ) :
    paperLogZetaRegOperator f n = (logZetaRegCoeff n : ℂ) * f n := by
  simp only [paperLogZetaRegOperator, sub_apply, lp.coeFn_sub, Pi.sub_apply,
    paperLogZetaRawOperator, lpDiagonalCLM_apply, paperPrimePoleOperator,
    paperConvergentDiagonal_apply, logZetaRegCoeff_eq_raw_sub_pole, Complex.ofReal_sub]
  ring

@[simp] theorem paperPrimeRegOperator_apply (f : PaperPrimeCoefficientSpace) (n : ℕ) :
    paperPrimeRegOperator f n = (primeRegCoeff n : ℂ) * f n := by
  simp only [paperPrimeRegOperator, sub_apply, lp.coeFn_sub, Pi.sub_apply,
    paperPrimeIndicatorOperator, lpDiagonalCLM_apply, paperPrimePoleOperator,
    paperConvergentDiagonal_apply, primeRegCoeff_eq_indicator_sub_pole, Complex.ofReal_sub]
  ring

theorem paperPrimePoleOperator_compact : IsCompactOperator paperPrimePoleOperator :=
  (paperConvergentDiagonal_compact_iff _ _).2 (by simp)

/-- The raw logarithmic multiplier has essential norm one on the prime layer. -/
theorem compactIdealDistance_paperLogZetaRawOperator :
    compactIdealDistance paperLogZetaRawOperator = 1 := by
  apply le_antisymm
  · have h := compactIdealDistance_le paperLogZetaRawOperator 0 isCompactOperator_zero
    simp only [sub_zero] at h
    exact h.trans (norm_lpDiagonalCLM_le _ _ _)
  · have hv : Tendsto (fun n => (paperLogZetaRawCoeff (paperPrimePowerIndex 0 n) : ℂ))
        atTop (𝓝 (1 : ℂ)) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)) using 1
      funext n
      have h := paperLogZetaRawCoeff_primePower ⟨_, Nat.prime_nth_prime n⟩ 0
      simpa [paperPrimePowerIndex] using congrArg Complex.ofReal h
    have h := paperDiagonalCluster_le_compactIdealDistance
      (fun n => (paperLogZetaRawCoeff n : ℂ)) zero_le_one
      (fun n => by simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (paperLogZetaRawCoeff_bounds n).1] using (paperLogZetaRawCoeff_bounds n).2)
      (paperPrimePowerIndex 0) (tendsto_paperPrimePowerIndex 0) hv
    simpa only [norm_one, paperLogZetaRawOperator] using h

/-- The prime indicator has essential norm one. -/
theorem compactIdealDistance_paperPrimeIndicatorOperator :
    compactIdealDistance paperPrimeIndicatorOperator = 1 := by
  apply le_antisymm
  · have h := compactIdealDistance_le paperPrimeIndicatorOperator 0 isCompactOperator_zero
    simp only [sub_zero] at h
    exact h.trans (norm_lpDiagonalCLM_le _ _ _)
  · have hv : Tendsto (fun n => (paperPrimeIndicatorCoeff (paperPrimePowerIndex 0 n) : ℂ))
        atTop (𝓝 (1 : ℂ)) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)) using 1
      funext n
      have h := paperPrimeIndicatorCoeff_primePower ⟨_, Nat.prime_nth_prime n⟩ 0
      simpa [paperPrimePowerIndex] using congrArg Complex.ofReal h
    have h := paperDiagonalCluster_le_compactIdealDistance
      (fun n => (paperPrimeIndicatorCoeff n : ℂ)) zero_le_one
      (fun n => by simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (paperPrimeIndicatorCoeff_bounds n).1] using (paperPrimeIndicatorCoeff_bounds n).2)
      (paperPrimePowerIndex 0) (tendsto_paperPrimePowerIndex 0) hv
    simpa only [norm_one, paperPrimeIndicatorOperator] using h

/-- The compact pole subtraction leaves the logarithmic quotient norm unchanged. -/
theorem compactIdealDistance_paperLogZetaRegOperator :
    compactIdealDistance paperLogZetaRegOperator = 1 := by
  exact (paperCompactIdealDistance_sub_compact paperLogZetaRawOperator
    ⟨paperPrimePoleOperator, paperPrimePoleOperator_compact⟩).trans
      compactIdealDistance_paperLogZetaRawOperator

/-- The regularized prime operator also has essential norm one. -/
theorem compactIdealDistance_paperPrimeRegOperator :
    compactIdealDistance paperPrimeRegOperator = 1 := by
  exact (paperCompactIdealDistance_sub_compact paperPrimeIndicatorOperator
    ⟨paperPrimePoleOperator, paperPrimePoleOperator_compact⟩).trans
      compactIdealDistance_paperPrimeIndicatorOperator

/-- Infinite paper cost for the literal logarithmic row. -/
theorem paperLogZetaRegOperator_traceCost :
    compactOperatorTraceCost PaperPrimeCoefficientSpace paperLogZetaRegOperator = ∞ := by
  apply (compactOperatorTraceCost_eq_top_iff _).2
  intro h
  have hz := compactIdealDistance_eq_zero_of_isCompactOperator paperLogZetaRegOperator h
  rw [compactIdealDistance_paperLogZetaRegOperator] at hz
  exact one_ne_zero hz

/-- Infinite paper cost for the literal prime row. -/
theorem paperPrimeRegOperator_traceCost :
    compactOperatorTraceCost PaperPrimeCoefficientSpace paperPrimeRegOperator = ∞ := by
  apply (compactOperatorTraceCost_eq_top_iff _).2
  intro h
  have hz := compactIdealDistance_eq_zero_of_isCompactOperator paperPrimeRegOperator h
  rw [compactIdealDistance_paperPrimeRegOperator] at hz
  exact one_ne_zero hz

private theorem defect_norm_bound (n : ℕ) : ‖(logPrimePowerDefect n : ℂ)‖ ≤ 1 / 2 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (logPrimePowerDefect_bounds n).1] using (logPrimePowerDefect_bounds n).2

/-- Exact full-row identity; no coordinates have been dropped. -/
theorem paperPrimeRegOperator_difference :
    paperLogZetaRegOperator - paperPrimeRegOperator =
      lpDiagonalCLM (fun n => (logPrimePowerDefect n : ℂ))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) defect_norm_bound := by
  apply ContinuousLinearMap.ext
  intro f
  ext n
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, paperLogZetaRegOperator_apply,
    paperPrimeRegOperator_apply, lpDiagonalCLM_apply,
    ← logZetaRegCoeff_sub_primeRegCoeff, Complex.ofReal_sub]
  ring

/-- Prime-square vectors force a sharp lower bound against every compact correction. -/
theorem paperPrimeRegOperator_gap_le_norm_sub_compact
    (K : compactOperatorStarAlgebra PaperPrimeCoefficientSpace) :
    1 / 2 ≤ ‖paperLogZetaRegOperator - paperPrimeRegOperator - K.1‖ := by
  rw [paperPrimeRegOperator_difference]
  have hlim : Tendsto (fun n => (logPrimePowerDefect (paperPrimePowerIndex 1 n) : ℂ))
      atTop (𝓝 (1 / 2 : ℂ)) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℂ)) atTop (𝓝 (1 / 2))) using 1
    funext n
    have h := logPrimePowerDefect_primePower ⟨_, Nat.prime_nth_prime n⟩ 0
    simpa [paperPrimePowerIndex] using congrArg Complex.ofReal h
  have h := paperDiagonalCluster_le_norm_sub_compact _ (by norm_num) defect_norm_bound
    (paperPrimePowerIndex 1) (tendsto_paperPrimePowerIndex 1) hlim K
  simpa using h

/-- The exact operator gap already occurs on each prime square. -/
theorem norm_paperPrimeRegOperator_difference :
    ‖paperLogZetaRegOperator - paperPrimeRegOperator‖ = 1 / 2 := by
  apply le_antisymm
  · rw [paperPrimeRegOperator_difference]
    exact norm_lpDiagonalCLM_le _ _ _
  · simpa using paperPrimeRegOperator_gap_le_norm_sub_compact ⟨0, isCompactOperator_zero⟩

/-- The same gap survives in the quotient by all compact operators. -/
theorem compactIdealDistance_paperPrimeRegOperator_difference :
    compactIdealDistance (paperLogZetaRegOperator - paperPrimeRegOperator) = 1 / 2 := by
  apply le_antisymm
  · simpa [norm_paperPrimeRegOperator_difference] using
      compactIdealDistance_le (paperLogZetaRegOperator - paperPrimeRegOperator) 0
        isCompactOperator_zero
  · exact le_compactIdealDistance _ _ fun K hK =>
      paperPrimeRegOperator_gap_le_norm_sub_compact ⟨K, hK⟩

theorem paperPrimeRegOperator_difference_not_compact :
    ¬ IsCompactOperator (paperLogZetaRegOperator - paperPrimeRegOperator) := by
  intro h
  have hbound := paperPrimeRegOperator_gap_le_norm_sub_compact
    ⟨paperLogZetaRegOperator - paperPrimeRegOperator, h⟩
  simp only [sub_self, norm_zero] at hbound
  norm_num at hbound

/-- Proven TraceCone weight applied to the native arithmetic defect. -/
theorem paperPrimeRegOperator_difference_traceCost :
    compactOperatorTraceCost PaperPrimeCoefficientSpace
      (paperLogZetaRegOperator - paperPrimeRegOperator) = ∞ :=
  (compactOperatorTraceCost_eq_top_iff _).2 paperPrimeRegOperator_difference_not_compact

/-- Compact repairs, even those mixing arithmetic coordinates, cannot erase this cost. -/
theorem paperPrimeRegOperator_difference_traceCost_add_compact
    (K : compactOperatorStarAlgebra PaperPrimeCoefficientSpace) :
    compactOperatorTraceCost PaperPrimeCoefficientSpace
      (paperLogZetaRegOperator - paperPrimeRegOperator + K.1) = ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperPrimeRegOperator_difference_traceCost]

/-- Both RH convergence receivers agree, while their actual coefficient operators remain
separated by a positive exact compact-quotient distance. -/
theorem paperPrimeRegularized_abscissa_and_operator_gap :
    (ConvergesRightOf logZetaRegCoeff (1 / 2) ↔ ConvergesRightOf primeRegCoeff (1 / 2)) ∧
      compactIdealDistance (paperLogZetaRegOperator - paperPrimeRegOperator) = 1 / 2 :=
  ⟨riemannHypothesis_iff_logZetaRegCoeff_converges.symm.trans
    riemannHypothesis_iff_primeRegCoeff_converges,
    compactIdealDistance_paperPrimeRegOperator_difference⟩

end
end RHTower
