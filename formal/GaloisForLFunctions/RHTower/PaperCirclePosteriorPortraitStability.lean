import GaloisForLFunctions.RHTower.PaperCirclePosteriorSnapshot
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Snapshot.Difference

/-! # Stable prediction from finite native posterior portraits

Quantized character observations determine optimal prediction energy up to two
explicit costs: the distance between their probability laws, and the precision
of the shared phase tiles. Normalization of the actual native laws sharpens the
source's comparison constants. No closeness assumption is needed.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCirclePosteriorPortrait (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (d : Finset (Grid (l+r+10))) (e : ℕ) : Law (Snapshot.Dome e d) :=
  (paperCircleHistoryCellPosterior a l r k i s).through
    (paperCircleSnapshotChannel a (l+r+10) k t d e)

theorem paperCirclePosteriorPortrait_expectation (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (d : Finset (Grid (l+r+10))) (e : ℕ) (G : Snapshot.Dome e d → ℝ) :
    (paperCirclePosteriorPortrait a l r k i s t d e).Ex G =
      ((paperCircleHistoryCellPosterior a l r k i s).withNext
        (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Ex
        (fun w => G (w.2, Snapshot.tiles e d w.1)) := by
  unfold paperCirclePosteriorPortrait
  rw [Law.Ex_through, Law.Ex_withNext]
  simp only [paperCircleSnapshotChannel, Law.Ex_send]

private lemma portrait_expectation_error {α : Type} [Fintype α] (P : Law α)
    (f g : α → ℝ) (r : ℝ) (h : ∀ x, |f x - g x| ≤ r) :
    |P.Ex f - P.Ex g| ≤ r := by
  have hlo := P.Ex_mono (fun x => (abs_le.mp (h x)).1)
  have hhi := P.Ex_mono (fun x => (abs_le.mp (h x)).2)
  rw [Law.Ex_const, Law.Ex_sub] at hlo
  rw [Law.Ex_sub, Law.Ex_const] at hhi
  exact abs_le.mpr ⟨hlo,hhi⟩

private lemma portrait_expectation_distance {α : Type} [Fintype α]
    (P Q : Law α) (f : α → ℝ) (hf : ∀ x, |f x| ≤ 3) :
    |P.Ex f - Q.Ex f| ≤ 3 * Snapshot.distance P Q := by
  unfold Law.Ex Snapshot.distance
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, |P x * f x - Q x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, 3 * |P x - Q x| := Finset.sum_le_sum fun x _ => by
      rw [← sub_mul, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

private lemma portrait_score_approximation (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (d : Finset (Grid (l+r+10))) (e : ℕ) (u : Grid (l+r+10))
    (c : Grid (l+r+10) → ℂ) (hc : ∀ z, ‖c z‖ ≤ 1)
    (F : Snapshot.TileN e d → ℂ) (δ : ℝ)
    (hF : ∀ x, ‖chi u x - F (Snapshot.tiles e d x)‖ ≤ δ) :
    |paperCircleCharacterScore a l r k i s t u c -
      (paperCirclePosteriorPortrait a l r k i s t d e).Ex
        (fun w => Capture.utility true (c w.1) (F w.2))| ≤ 2 * δ := by
  rw [paperCirclePosteriorPortrait_expectation]
  unfold paperCircleCharacterScore
  apply portrait_expectation_error
  intro w
  exact (Capture.utility_diff true (c w.2) _ _ (hc w.2)).trans
    (mul_le_mul_of_nonneg_left (hF w.1) (by norm_num))

private lemma portrait_energy_le (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (d : Finset (Grid (l+r+10))) (e : ℕ) (σ : Grid (l+r+10) → Fin 3) :
    paperCircleCaptureEnergy a l r k i s t (paperCircleSnapshotFrequency d σ) ≤
      paperCircleCaptureEnergy a l r k i v τ (paperCircleSnapshotFrequency d σ) +
        3 * Snapshot.distance (paperCirclePosteriorPortrait a l r k i s t d e)
          (paperCirclePosteriorPortrait a l r k i v τ d e) +
        4 * ((d.card : ℝ) * (8 * Period.side e)) := by
  obtain ⟨F,hF,herr⟩ := Snapshot.painted _ d (paperCircleSnapshotFrequency_enclosed d σ) e
  obtain ⟨c,hc,heq⟩ := (paperCircleCharacterScore_source_complete a l r k i s t
    (paperCircleSnapshotFrequency d σ)).2
  have hs := portrait_score_approximation a l r k i s t d e _ c hc F _ herr
  have hv := portrait_score_approximation a l r k i v τ d e _ c hc F _ herr
  have hd := portrait_expectation_distance
    (paperCirclePosteriorPortrait a l r k i s t d e)
    (paperCirclePosteriorPortrait a l r k i v τ d e)
    (fun w => Capture.utility true (c w.1) (F w.2))
    (fun w => Capture.utility_bounds true (c w.1) (F w.2) (hc w.1) (hF w.2))
  have hu := paperCircleCharacterScore_le a l r k i v τ (paperCircleSnapshotFrequency d σ) c
  rw [heq] at hs
  linarith only [(abs_le.mp hs).2, (abs_le.mp hd).2, (abs_le.mp hv).1, hu]

/-- One portrait comparison controls every signed combination of the chosen frequencies. -/
theorem paperCircleCaptureEnergy_portrait_distance (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (d : Finset (Grid (l+r+10))) (e : ℕ) (σ : Grid (l+r+10) → Fin 3) :
    |paperCircleCaptureEnergy a l r k i s t (paperCircleSnapshotFrequency d σ) -
      paperCircleCaptureEnergy a l r k i v τ (paperCircleSnapshotFrequency d σ)| ≤
        3 * Snapshot.distance (paperCirclePosteriorPortrait a l r k i s t d e)
          (paperCirclePosteriorPortrait a l r k i v τ d e) +
        4 * ((d.card : ℝ) * (8 * Period.side e)) := by
  have hs := portrait_energy_le a l r k i s v t τ d e σ
  have hv := portrait_energy_le a l r k i v s τ t d e σ
  have heq : Snapshot.distance (paperCirclePosteriorPortrait a l r k i v τ d e)
      (paperCirclePosteriorPortrait a l r k i s t d e) =
      Snapshot.distance (paperCirclePosteriorPortrait a l r k i s t d e)
        (paperCirclePosteriorPortrait a l r k i v τ d e) := by
    simp only [Snapshot.distance, abs_sub_comm]
  rw [heq] at hv
  rw [abs_le]
  constructor <;> linarith only [hs,hv]

private lemma portrait_distance_cloud {α : Type} [Fintype α] (P Q : Law α) :
    Snapshot.distance P Q ≤ Real.sqrt (2 * Snapshot.cloud P Q) := by
  have hsq := Snapshot.distance_cloud P Q P.nonneg Q.nonneg
  rw [P.total, Q.total] at hsq
  have hn := Snapshot.cloud_nonneg P Q P.nonneg Q.nonneg
  have hroot := Real.sq_sqrt (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hn)
  nlinarith only [hsq, hroot, Real.sqrt_nonneg (2 * Snapshot.cloud P Q)]

private lemma portrait_cloud_bound {α : Type} [Fintype α] (P Q : Law α)
    (x δ : ℝ) (h : x ≤ 3 * Snapshot.distance P Q + 4 * δ) :
    x ≤ 3 * Real.sqrt (2 * Snapshot.cloud P Q) + 4 * δ := by
  have hd := portrait_distance_cloud P Q
  linarith only [h,hd]

/-- The source's positive quadratic cloud cost also controls actual prediction stability. -/
theorem paperCircleCaptureEnergy_portrait_cloud (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (d : Finset (Grid (l+r+10))) (e : ℕ) (σ : Grid (l+r+10) → Fin 3) :
    |paperCircleCaptureEnergy a l r k i s t (paperCircleSnapshotFrequency d σ) -
      paperCircleCaptureEnergy a l r k i v τ (paperCircleSnapshotFrequency d σ)| ≤
        3 * Real.sqrt (2 * Snapshot.cloud (paperCirclePosteriorPortrait a l r k i s t d e)
          (paperCirclePosteriorPortrait a l r k i v τ d e)) +
        4 * ((d.card : ℝ) * (8 * Period.side e)) := by
  exact portrait_cloud_bound
    (paperCirclePosteriorPortrait a l r k i s t d e)
    (paperCirclePosteriorPortrait a l r k i v τ d e) _ _
    (paperCircleCaptureEnergy_portrait_distance a l r k i s v t τ d e σ)

end
end RHTower
