/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael
-/
import GaloisForLFunctions.RHTower.SuzukiHlogCompactEmbedding

/-!
# CCM compact embedding for every divergent Fourier weight

This is the general compactness statement proved inside Connes--Consani--Moscovici (2025),
Theorem 3.6.  A positive increasing Fourier weight tending to infinity makes its weighted unit
ball on any bounded interval precompact in `L²`.  Suzuki's `1 + log⁺ |ξ|` proposition is the
distinguished specialization formalized in `SuzukiHlogCompactEmbedding`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal InnerProduct Topology

set_option maxHeartbeats 1000000

namespace RHTower

/-- Source data `ρ : [0,∞) → [1,∞)`, represented on `ℝ` and constrained on `Ici 0`. -/
structure CCMFourierWeight where
  value : ℝ → ℝ
  one_le_of_nonneg : ∀ {u : ℝ}, 0 ≤ u → 1 ≤ value u
  monotoneOn_nonneg : MonotoneOn value (Set.Ici 0)
  tendsto_atTop : Tendsto value atTop atTop

/-- The exact weighted Fourier density from the CCM compactness argument. -/
def ccmFourierWeightDensity (ρ : CCMFourierWeight) (f : SoninL2) (ξ : ℝ) : ℝ :=
  ρ.value |ξ| * ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2

def ccmFourierWeightMoment (ρ : CCMFourierWeight) (f : SoninL2) : ℝ :=
  ∫ ξ : ℝ, ccmFourierWeightDensity ρ f ξ

/-- Weighted unit ball on a bounded interval, realized by zero extension to `L²(ℝ)`. -/
def ccmFourierWeightUnitBall (ρ : CCMFourierWeight) (I : SuzukiBoundedInterval) : Set SoninL2 :=
  {f | indicatorCutoff I.carrier measurableSet_Icc f = f ∧
    Integrable (ccmFourierWeightDensity ρ f) ∧ ccmFourierWeightMoment ρ f ≤ 1}

theorem ccmFourierWeightDensity_nonneg
    (ρ : CCMFourierWeight) (f : SoninL2) (ξ : ℝ) :
    0 ≤ ccmFourierWeightDensity ρ f ξ := by
  exact mul_nonneg ((ρ.one_le_of_nonneg (abs_nonneg ξ)).trans' zero_le_one) (sq_nonneg _)

theorem norm_le_one_of_mem_ccmFourierWeightUnitBall
    (ρ : CCMFourierWeight) (I : SuzukiBoundedInterval) {f : SoninL2}
    (hf : f ∈ ccmFourierWeightUnitBall ρ I) : ‖f‖ ≤ 1 := by
  have hplain : Integrable
      (fun ξ : ℝ => ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hpoint : ∀ ξ : ℝ,
      ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2 ≤ ccmFourierWeightDensity ρ f ξ := by
    intro ξ
    unfold ccmFourierWeightDensity
    nlinarith [ρ.one_le_of_nonneg (abs_nonneg ξ),
      sq_nonneg ‖(fourierUnitary f : ℝ → ℂ) ξ‖]
  have hintegral :
      (∫ ξ : ℝ, ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2) ≤
        ccmFourierWeightMoment ρ f :=
    integral_mono hplain hf.2.1 hpoint
  have hnormsq : ‖f‖ ^ 2 ≤ 1 := by
    calc
      ‖f‖ ^ 2 = ‖fourierUnitary f‖ ^ 2 := by rw [fourierUnitary.norm_map]
      _ = ∫ ξ : ℝ, ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2 :=
        norm_sq_eq_integral (fourierUnitary f)
      _ ≤ ccmFourierWeightMoment ρ f := hintegral
      _ ≤ 1 := hf.2.2
  nlinarith [norm_nonneg f]

/-- Divergence supplies a positive cutoff beyond which the weight exceeds any prescribed level. -/
theorem CCMFourierWeight.exists_pos_lt_value (ρ : CCMFourierWeight) (A : ℝ) :
    ∃ R : ℝ, 0 < R ∧ A < ρ.value R := by
  obtain ⟨R, hvalue, hR⟩ :=
    ((ρ.tendsto_atTop.eventually_gt_atTop A).and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨R, hR, hvalue⟩

theorem le_ccmFourierWeight_of_mem_tail
    (ρ : CCMFourierWeight) {A R ξ : ℝ} (hR : 0 < R)
    (hAR : A < ρ.value R) (hξ : ξ ∈ (centralInterval R)ᶜ) :
    A ≤ ρ.value |ξ| := by
  have habs : R < |ξ| := by
    have hnot : ¬|ξ| ≤ R := by
      intro h
      exact hξ (by
        rw [centralInterval, Set.mem_Icc]
        exact abs_le.mp h)
    exact lt_of_not_ge hnot
  have hmono : ρ.value R ≤ ρ.value |ξ| :=
    ρ.monotoneOn_nonneg hR.le (abs_nonneg ξ) habs.le
  exact hAR.le.trans hmono

theorem mul_norm_sq_sub_fourierCutoff_le_ccmFourierWeightMoment
    (ρ : CCMFourierWeight) (I : SuzukiBoundedInterval) {f : SoninL2}
    (hf : f ∈ ccmFourierWeightUnitBall ρ I) {A R : ℝ}
    (hR : 0 < R) (hAR : A < ρ.value R) :
    A * ‖f - fourierCutoff (centralInterval R)
      (measurableSet_centralInterval R) f‖ ^ 2 ≤ ccmFourierWeightMoment ρ f := by
  rw [norm_sq_sub_fourierCutoff_central_eq_tailIntegral, ← integral_const_mul]
  have hplain : Integrable
      (fun ξ : ℝ => ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hleft : Integrable (fun ξ : ℝ =>
      A * (centralInterval R)ᶜ.indicator
        (fun η : ℝ => ‖(fourierUnitary f : ℝ → ℂ) η‖ ^ 2) ξ) :=
    (hplain.indicator (measurableSet_centralInterval R).compl).const_mul A
  refine integral_mono hleft hf.2.1 ?_
  intro ξ
  change A * (centralInterval R)ᶜ.indicator
      (fun η : ℝ => ‖(fourierUnitary f : ℝ → ℂ) η‖ ^ 2) ξ ≤
    ccmFourierWeightDensity ρ f ξ
  by_cases hξ : ξ ∈ (centralInterval R)ᶜ
  · rw [Set.indicator_of_mem hξ]
    unfold ccmFourierWeightDensity
    exact mul_le_mul_of_nonneg_right
      (le_ccmFourierWeight_of_mem_tail ρ hR hAR hξ) (sq_nonneg _)
  · rw [Set.indicator_of_notMem hξ]
    simpa using ccmFourierWeightDensity_nonneg ρ f ξ

/-- Uniform Fourier-tail estimate for the general CCM weighted unit ball. -/
theorem exists_fourierCutoff_tail_lt_of_mem_ccmFourierWeightUnitBall
    (ρ : CCMFourierWeight) (I : SuzukiBoundedInterval) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ f ∈ ccmFourierWeightUnitBall ρ I,
      ‖f - fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f‖ < ε := by
  let A : ℝ := (4 / ε) ^ 2
  obtain ⟨R, hR, hAR⟩ := ρ.exists_pos_lt_value A
  refine ⟨R, hR, ?_⟩
  intro f hf
  let n : ℝ := ‖f - fourierCutoff (centralInterval R)
    (measurableSet_centralInterval R) f‖
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hmul : A * n ^ 2 ≤ 1 := by
    calc
      A * n ^ 2 ≤ ccmFourierWeightMoment ρ f :=
        mul_norm_sq_sub_fourierCutoff_le_ccmFourierWeightMoment ρ I hf hR hAR
      _ ≤ 1 := hf.2.2
  have hn_sq' : n ^ 2 ≤ 1 / A := by
    rw [le_div_iff₀ hA]
    simpa [mul_comm] using hmul
  have hrecip : 1 / A = (ε / 4) ^ 2 := by
    dsimp [A]
    field_simp [ne_of_gt hε]
  have hn : n ≤ ε / 4 := by
    have hn_sq : n ^ 2 ≤ (ε / 4) ^ 2 := hn_sq'.trans_eq hrecip
    nlinarith [norm_nonneg (f - fourierCutoff (centralInterval R)
      (measurableSet_centralInterval R) f)]
  change n < ε
  nlinarith

/-- CCM (2025), general compact embedding theorem for every divergent increasing Fourier weight. -/
theorem totallyBounded_ccmFourierWeightUnitBall
    (ρ : CCMFourierWeight) (I : SuzukiBoundedInterval) :
    TotallyBounded (ccmFourierWeightUnitBall ρ I) := by
  apply totallyBounded_of_centralSupport_of_uniformFourierTail
    ⟨I.centralRadius, I.centralRadius_pos⟩
  · intro f hf
    exact norm_le_one_of_mem_ccmFourierWeightUnitBall ρ I hf
  · intro f hf
    exact indicatorCutoff_centralRadius_eq_self_of_interval_eq_self I hf.1
  · intro ε hε
    exact exists_fourierCutoff_tail_lt_of_mem_ccmFourierWeightUnitBall ρ I hε

/-- Closed compact form of the general CCM compact embedding theorem. -/
theorem isCompact_closure_ccmFourierWeightUnitBall
    (ρ : CCMFourierWeight) (I : SuzukiBoundedInterval) :
    IsCompact (closure (ccmFourierWeightUnitBall ρ I)) :=
  (totallyBounded_ccmFourierWeightUnitBall ρ I).closure.isCompact_of_isClosed isClosed_closure

end RHTower
