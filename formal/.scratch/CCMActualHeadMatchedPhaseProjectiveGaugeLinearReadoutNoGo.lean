import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

open Filter Topology

noncomputable section
namespace RHTower

/-- Projective half-density restricted to the canonical increasing prime enumeration. -/
def ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge (k : ℕ) : ℝ :=
  ccmActualHeadMatchedPhaseProjectiveGauge (nthPrimeSubtype k : ℕ)

theorem ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge_pos (k : ℕ) :
    0 < ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge k := by
  unfold ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge
  rw [ccmActualHeadMatchedPhaseProjectiveGauge]
  apply Real.sqrt_pos.2
  exact div_pos
    (sq_pos_of_pos (criticalMellinAtomWeight_pos
      (nthPrimeSubtype k).prop.isPrimePow))
    (Real.exp_pos _)

/-- The source-selected carrier gauge remains square-summable on canonical prime labels. -/
theorem summable_sq_ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge :
    Summable (fun k : ℕ =>
      ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge k ^ 2) := by
  have hinj : Function.Injective (fun k : ℕ => (nthPrimeSubtype k : ℕ)) :=
    nthPrimeSubtype_strictMono.injective
  have h :=
    summable_criticalMellinAtomWeight_sq_div_exp_half_log.comp_injective hinj
  apply h.congr
  intro k
  simp only [Function.comp_apply]
  exact (ccmActualHeadMatchedPhaseProjectiveGauge_sq
    (nthPrimeSubtype k : ℕ)).symm

private theorem not_summable_sq_and_inv_sq
    (g : ℕ → ℝ) (hg : ∀ k, g k ≠ 0) :
    ¬ (Summable (fun k => g k ^ 2) ∧
      Summable (fun k => (g k)⁻¹ ^ 2)) := by
  rintro ⟨hgSq, hgInvSq⟩
  have hprod : Tendsto
      (fun k => g k ^ 2 * (g k)⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using hgSq.tendsto_atTop_zero.mul hgInvSq.tendsto_atTop_zero
  have hone : (fun k => g k ^ 2 * (g k)⁻¹ ^ 2) =
      (fun _ => (1 : ℝ)) := by
    funext k
    field_simp [hg k]
  rw [hone] at hprod
  have hzeroOne : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hprod tendsto_const_nhds
  exact zero_ne_one hzeroOne

/-- Reciprocal coordinates needed to undo the projective gauge are not square-summable, even on
the canonical ordinary-prime subsequence. -/
theorem not_summable_inv_sq_ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge :
    ¬ Summable (fun k : ℕ =>
      (ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge k)⁻¹ ^ 2) := by
  intro hdual
  exact not_summable_sq_and_inv_sq
    ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge
    (fun k => (ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge_pos k).ne')
    ⟨summable_sq_ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge, hdual⟩

/-- Cofinal norm cost of the exact inverse-gauge readout. -/
def ccmActualHeadMatchedPhaseNthPrimeProjectiveDualCost (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge k)⁻¹ ^ 2

/-- Exact linearization of all atomwise projective ratios has divergent cofinal graph norm. -/
theorem tendsto_ccmActualHeadMatchedPhaseNthPrimeProjectiveDualCost_atTop :
    Tendsto ccmActualHeadMatchedPhaseNthPrimeProjectiveDualCost atTop atTop := by
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k => sq_nonneg
      (ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge k)⁻¹)).mp
        not_summable_inv_sq_ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge

/-- A coefficient sequence linearizes the projective source readout when it cancels the
source-selected gauge at every canonical prime coordinate. -/
def LinearizesCCMActualHeadMatchedPhaseNthPrimeProjectiveReadout
    (v : ℕ → ℝ) : Prop :=
  ∀ k, v k * ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge k = 1

/-- No square-summable linear test vector can recover all atomwise projective source coordinates.
Thus the summable positive carrier cannot be converted into a cofinal linear FU reporter without
paying an unbounded singular graph norm. -/
theorem not_exists_squareSummable_linearizes_ccmActualHeadMatchedPhaseNthPrimeProjectiveReadout :
    ¬ ∃ v : ℕ → ℝ,
      Summable (fun k => v k ^ 2) ∧
        LinearizesCCMActualHeadMatchedPhaseNthPrimeProjectiveReadout v := by
  rintro ⟨v, hv, hlinear⟩
  apply not_summable_inv_sq_ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge
  apply hv.congr
  intro k
  have hvk : v k =
      (ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge k)⁻¹ :=
    (mul_eq_one_iff_eq_inv₀
      (ccmActualHeadMatchedPhaseNthPrimeProjectiveGauge_pos k).ne').mp
        (hlinear k)
  rw [hvk]

end RHTower
