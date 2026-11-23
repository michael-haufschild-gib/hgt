import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The exact integral of weighted critical-tolerance intervals -/
open Finset Set Real MeasureTheory Filter
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.RelativeTolerance
noncomputable section

/-- Logarithmic change from allowing one additional gate. -/
def gateWeight (j : ℕ) : ℝ := log (((j+1:ℕ):ℝ)+1)-log ((j:ℝ)+1)

theorem gateWeight_nonneg (j : ℕ) : 0 ≤ gateWeight j := by
  apply sub_nonneg.mpr (log_le_log (by positivity) _)
  push_cast; linarith

theorem sum_gateWeight (B : ℕ) : ∑ j ∈ range B, gateWeight j = log ((B:ℝ)+1) := by
  simpa only [gateWeight,Nat.cast_zero,zero_add,log_one,sub_zero] using
    Finset.sum_range_sub (fun j : ℕ => log ((j:ℝ)+1)) B

/-- Each critical height contributes on the half-open interval of starting
tolerances crossed by increasing the error by δ. -/
def thresholdLoss (B : ℕ) (h : ℕ → ℝ) (δ e : ℝ) : ℝ :=
  ∑ j ∈ range B, (Ico (h j-δ) (h j)).indicator (fun _ => gateWeight j) e

theorem thresholdLoss_nonneg (B : ℕ) (h : ℕ → ℝ) (δ e : ℝ) : 0 ≤ thresholdLoss B h δ e :=
  Finset.sum_nonneg fun j _ => indicator_nonneg (fun _ _ => gateWeight_nonneg j) e

private theorem integrable_term (h δ : ℝ) (j : ℕ) :
    Integrable ((Ico (h-δ) h).indicator (fun _ => gateWeight j)) volume :=
  (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (measure_ne_top_of_subset Ico_subset_Icc_self measure_Icc_lt_top.ne))

theorem integrable_thresholdLoss (B : ℕ) (h : ℕ → ℝ) (δ : ℝ) :
    Integrable (thresholdLoss B h δ) volume :=
  integrable_finsetSum _ fun j _ => integrable_term (h j) δ j

/-- The integrated logarithmic loss is independent of the locations
and multiplicities of the critical heights. -/
theorem integral_thresholdLoss (B : ℕ) (h : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ e, thresholdLoss B h δ e) = δ*log ((B:ℝ)+1) := by
  have hterm (j : ℕ) :
      (∫ e : ℝ, (Ico (h j-δ) (h j)).indicator (fun _ => gateWeight j) e) = δ*gateWeight j := by
    rw [integral_indicator measurableSet_Ico,setIntegral_const,Real.volume_real_Ico_of_le (sub_le_self _ hδ)]
    simp only [sub_sub_cancel,smul_eq_mul]
  rw [thresholdLoss,integral_finsetSum _ (fun j _ => integrable_term (h j) δ j)]
  simp only [hterm,←Finset.mul_sum,sum_gateWeight]

/-- Summability of the integrated losses implies summability of the
actual losses at almost every fixed tolerance. -/
theorem ae_summable_thresholdLoss (B : ℕ → ℕ) (h : ℕ → ℕ → ℝ) (δ : ℕ → ℝ)
    (hδ : ∀ k, 0 ≤ δ k) (hs : Summable fun k => δ k*log ((B k:ℝ)+1)) :
    ∀ᵐ e : ℝ ∂volume, Summable fun k => thresholdLoss (B k) (h k) (δ k) e := by
  let F (k : ℕ) := thresholdLoss (B k) (h k) (δ k)
  have hint k := integrable_thresholdLoss (B k) (h k) (δ k)
  have hnn (k : ℕ) : ∀ᵐ e : ℝ ∂volume, 0 ≤ F k e :=
    Eventually.of_forall (thresholdLoss_nonneg (B k) (h k) (δ k))
  have hn : ∀ k, 0 ≤ δ k*log ((B k:ℝ)+1) := fun k =>
    mul_nonneg (hδ k) (log_nonneg (by linarith only [Nat.cast_nonneg (α:=ℝ) (B k)]))
  have he : (∫⁻ e, ∑' k, ENNReal.ofReal (F k e)) = ENNReal.ofReal (∑' k, δ k*log ((B k:ℝ)+1)) := by
    rw [lintegral_tsum (fun k => (hint k).aemeasurable.ennreal_ofReal),ENNReal.ofReal_tsum_of_nonneg hn hs]
    apply tsum_congr
    intro k
    rw [←ofReal_integral_eq_lintegral_ofReal (hint k) (hnn k),integral_thresholdLoss _ _ (hδ k)]
  have hm : AEMeasurable (fun e : ℝ => ∑' k, ENNReal.ofReal (F k e)) volume :=
    AEMeasurable.tsum fun k => (hint k).aemeasurable.ennreal_ofReal
  filter_upwards [ae_lt_top' hm (he.trans_ne ENNReal.ofReal_ne_top)] with e hfin
  exact (ENNReal.summable_toReal hfin.ne).congr fun k =>
    ENNReal.toReal_ofReal (thresholdLoss_nonneg (B k) (h k) (δ k) e)

#print axioms integral_thresholdLoss
#print axioms ae_summable_thresholdLoss
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.RelativeTolerance
