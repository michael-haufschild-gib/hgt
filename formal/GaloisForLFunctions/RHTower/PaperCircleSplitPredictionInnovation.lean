import GaloisForLFunctions.RHTower.PaperCircleSplitCharacterPosterior
import GaloisForLFunctions.RHTower.PaperCircleSplitBitPosterior
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Paths.Gust

/-! # Exact prediction gain from revealing a native spatial branch

The source's energy increment is the actual posterior mean squared change of
character predictor when the branch bit is revealed. Its vanishing is equivalent
to pointwise agreement of both child predictors with the parent predictor.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure.Paths

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleSplitPredictionEnergy (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) (u : Grid (l+r+10)) : ℝ :=
  (paperCircleNextObservationLaw a l r k i s t).Ex (fun z =>
    (paperCircleHistorySplitBitPosterior a l r k i s t z).Ex
      (fun b => ‖paperCircleSplitCharacterMean a l r k i s t b u z‖^2))

def paperCircleSplitPredictionInnovation (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) (u : Grid (l+r+10)) : ℝ :=
  (paperCircleNextObservationLaw a l r k i s t).Ex (fun z =>
    (paperCircleHistorySplitBitPosterior a l r k i s t z).Ex
      (fun b => ‖paperCircleSplitCharacterMean a l r k i s t b u z -
        paperCircleNextCharacterMean a l r k i s t u z‖^2))

private lemma native_parent_mean (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u z : Grid (l+r+10)) :
    meanV (paperCircleObservationScene a l r k i s t) u z =
      paperCircleNextCharacterMean a l r k i s t u z := by
  change Thermal.fz (paperCircleObservationCell l i)
    (paperCircleHistoryLikelihood a (l+r+10) k s) (paperCircleHistoryCellScene a l r k i s).norm
    (paperCircleLocalizedForm a (l+r+10) k t) u z /
      (hist (paperCircleHistoryCellScene a l r k i s)
        (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z : ℂ) = _
  rw [paperCircleNextCharacterMean_source, paperCircleNextObservationLaw_hist]
  field_simp [(paperCircleNextObservationLaw_pos a l r k i s t z).ne']

private lemma native_split_expectation (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (f : Bool → Grid (l+r+10) → ℝ) :
    (paperCircleNextObservationLaw a l r k i s t).Ex (fun z =>
      (paperCircleHistorySplitBitPosterior a l r k i s t z).Ex (fun b => f b z)) =
      (∑ z : Grid (l+r+10), (matter ((paperCircleObservationScene a l r k i s t).smaller false) z * f false z +
        matter ((paperCircleObservationScene a l r k i s t).smaller true) z * f true z)) / 2 := by
  rw [Law.Ex, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Law.Ex, Fintype.sum_bool, paperCircleHistorySplitBitPosterior_apply]
  change _ = (hist ((paperCircleHistoryCellScene a l r k i s).smaller false)
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z * f false z +
    hist ((paperCircleHistoryCellScene a l r k i s).smaller true)
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z * f true z) / 2
  rw [paperCircleNextObservationLaw_hist]
  field_simp [(paperCircleNextObservationLaw_pos a l r k i s t z).ne']
  ring

private lemma native_refined_energy_source (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleSplitPredictionEnergy a l r k i s t u =
      (Capture.energy ((paperCircleObservationScene a l r k i s t).smaller false) u +
        Capture.energy ((paperCircleObservationScene a l r k i s t).smaller true) u) / 2 := by
  unfold paperCircleSplitPredictionEnergy
  rw [native_split_expectation]
  simp only [paperCircleSplitCharacterMean_source]
  rw [sun_energy ((paperCircleObservationScene_climb a l r k i s t).child false),
    sun_energy ((paperCircleObservationScene_climb a l r k i s t).child true)]
  simp only [sun, Finset.sum_add_distrib]

/-- Exact identification with the paper's positive spatial energy increment. -/
theorem paperCircleSplitPredictionInnovation_source (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleSplitPredictionInnovation a l r k i s t u =
      shower u (paperCircleObservationScene a l r k i s t) := by
  unfold paperCircleSplitPredictionInnovation
  rw [native_split_expectation]
  simp only [paperCircleSplitCharacterMean_source, ← native_parent_mean,
    shower, dew, mist, Finset.sum_div]

theorem paperCircleSplitPredictionInnovation_nonneg (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    0 ≤ paperCircleSplitPredictionInnovation a l r k i s t u :=
  Law.Ex_nonneg _ (fun _ => Law.Ex_nonneg _ (fun _ => sq_nonneg _))

/-- Revealing the branch improves actual optimal prediction by exactly its conditional innovation. -/
theorem paperCircleSplitPredictionEnergy_balance (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleSplitPredictionEnergy a l r k i s t u = paperCircleCaptureEnergy a l r k i s t u +
      paperCircleSplitPredictionInnovation a l r k i s t u := by
  rw [native_refined_energy_source, paperCircleSplitPredictionInnovation_source]
  exact wet_average _ (paperCircleObservationScene_climb a l r k i s t) u

theorem paperCircleSplitPredictionEnergy_le_one (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleSplitPredictionEnergy a l r k i s t u ≤ 1 := by
  apply le_trans (Law.Ex_mono _ (g := fun _ => (1 : ℝ)) ?_) (Law.Ex_const _ _).le
  intro z
  apply le_trans (Law.Ex_mono _ (g := fun _ => (1 : ℝ)) ?_) (Law.Ex_const _ _).le
  intro b
  exact pow_le_one₀ (norm_nonneg _) (paperCircleSplitCharacterMean_norm a l r k i s t b u z)

/-- The innovation fits entirely inside the parent's remaining prediction error. -/
theorem paperCircleSplitPredictionInnovation_le_residual (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleSplitPredictionInnovation a l r k i s t u ≤ 1 - paperCircleCaptureEnergy a l r k i s t u := by
  have h := paperCircleSplitPredictionEnergy_le_one a l r k i s t u
  rw [paperCircleSplitPredictionEnergy_balance] at h
  linarith only [h]

private lemma ex_norm_sq_zero {α : Type} [Fintype α] (P : Law α)
    (hp : ∀ x, 0 < P x) (f : α → ℂ) : P.Ex (fun x => ‖f x‖^2) = 0 ↔ ∀ x, f x = 0 := by
  constructor
  · intro h x
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => mul_nonneg (P.nonneg x) (sq_nonneg ‖f x‖))).mp h
    have hx := (mul_eq_zero.mp (ht x (Finset.mem_univ x))).resolve_left (hp x).ne'
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · intro h
    simp only [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0), Law.Ex_const]

/-- There is no prediction gain precisely when both actual child predictors already agree. -/
theorem paperCircleSplitPredictionInnovation_eq_zero_iff (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleSplitPredictionInnovation a l r k i s t u = 0 ↔
      ∀ z b, paperCircleSplitCharacterMean a l r k i s t b u z =
        paperCircleNextCharacterMean a l r k i s t u z := by
  have h := ex_norm_sq_zero
    ((paperCircleNextObservationLaw a l r k i s t).withNext
      (paperCircleHistorySplitBitPosterior a l r k i s t))
    (fun w => mul_pos (paperCircleNextObservationLaw_pos a l r k i s t w.1)
      (paperCircleHistorySplitBitPosterior_pos a l r k i s t w.1 w.2))
    (fun w => paperCircleSplitCharacterMean a l r k i s t w.2 u w.1 -
      paperCircleNextCharacterMean a l r k i s t u w.1)
  simpa only [paperCircleSplitPredictionInnovation, Law.Ex_withNext, sub_eq_zero, Prod.forall] using h

/-- The source's entire vector increment is paid by actual Fisher information and innovation. -/
theorem paperCircleSplitPrediction_factor_bound (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    (∑ z, ‖factor (paperCircleObservationScene a l r k i s t) u z‖)^2 ≤
      16 * (paperCircleCaptureEnergy a l r k i s t u * paperCircleHistorySplitFisher a l r k i s t +
        paperCircleSplitPredictionInnovation a l r k i s t u) := by
  rw [paperCircleSplitPredictionInnovation_source]
  exact factor_bill _ (paperCircleObservationScene_climb a l r k i s t) u

end
end RHTower
