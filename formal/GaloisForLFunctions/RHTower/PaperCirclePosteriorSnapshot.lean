import GaloisForLFunctions.RHTower.PaperCirclePosteriorReference
import GaloisForLFunctions.RHTower.PaperCirclePosteriorPrediction
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Snapshot.Near

/-! # Quantized character observations for actual native posteriors

One finite quantized observation predicts every signed combination of its chosen
frequencies. Its additional information is at most the number of frequencies times
the precision. The source also gives a uniform continuity bound for the actual
optimal prediction energy as frequency varies.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleSnapshotChannel (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (d : Finset (Grid M)) (e : ℕ) (x : Grid M) : Law (Snapshot.Dome e d) :=
  (Thermal.channel (paperCircleLocalizedForm a M k t) x).send (fun z => (z, Snapshot.tiles e d x))

def paperCircleSnapshotInformation (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (d : Finset (Grid (l+r+10))) (e : ℕ) : ℝ :=
  (paperCircleHistoryCellPosterior a l r k i s).privateH
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) -
  (paperCircleHistoryCellPosterior a l r k i s).privateH (paperCircleSnapshotChannel a (l+r+10) k t d e)

theorem paperCircleSnapshotInformation_budget (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (d : Finset (Grid (l+r+10))) (e : ℕ) :
    0 ≤ paperCircleSnapshotInformation a l r k i s t d e ∧
      paperCircleSnapshotInformation a l r k i s t d e ≤ (d.card : ℝ) * e := by
  have h := Snapshot.sight_budget (paperCircleObservationScene a l r k i s t) true d e
  dsimp only at h
  simp only [deficit, paperCircleObservationScene_actor] at h
  let original := (paperCircleHistoryCellPosterior a l r k i s).privateH
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))
  let augmented := (paperCircleHistoryCellPosterior a l r k i s).privateH
    (paperCircleSnapshotChannel a (l+r+10) k t d e)
  let L := levels (paperCircleObservationScene a l r k i s t)
  change L - original ≤ L - augmented ∧ L - augmented ≤ L - original + (d.card : ℝ) * e at h
  change 0 ≤ original - augmented ∧ original - augmented ≤ (d.card : ℝ) * e
  constructor <;> linarith [h.1, h.2]

def paperCircleSnapshotFrequency {M : ℕ} (d : Finset (Grid M)) (σ : Grid M → Fin 3) : Grid M :=
  ∑ u ∈ d, ((σ u).val - (1 : ℤ)) • u

theorem paperCircleSnapshotFrequency_enclosed {M : ℕ} (d : Finset (Grid M)) (σ : Grid M → Fin 3) :
    enclosed d 1 (paperCircleSnapshotFrequency d σ) := by
  refine ⟨fun u => (σ u).val - (1 : ℤ), ?_, rfl⟩
  intro u _
  dsimp only
  rw [abs_le]
  have h := (σ u).isLt
  constructor <;> omega

/-- The same tiles reconstruct every signed frequency combination under every native history. -/
theorem paperCircleSnapshot_reconstruction (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (d : Finset (Grid (l+r+10))) (e : ℕ) (σ : Grid (l+r+10) → Fin 3) :
    ∃ F : Snapshot.TileN e d → ℂ, (∀ q, ‖F q‖ = 1) ∧
      (∀ x, ‖chi (paperCircleSnapshotFrequency d σ) x - F (Snapshot.tiles e d x)‖ ≤
        (d.card : ℝ) * (8 * Period.side e)) ∧
      ((paperCircleHistoryCellPosterior a l r k i s).withNext
        (paperCircleSnapshotChannel a (l+r+10) k t d e)).Ex
        (fun w => ‖chi (paperCircleSnapshotFrequency d σ) w.1 - F w.2.2‖^2) ≤
          ((d.card : ℝ) * (8 * Period.side e))^2 := by
  obtain ⟨F,hF,herr⟩ := Snapshot.painted _ d (paperCircleSnapshotFrequency_enclosed d σ) e
  refine ⟨F,hF,herr,?_⟩
  rw [Law.Ex_withNext]
  simp only [paperCircleSnapshotChannel, Law.Ex_send, Law.Ex_const]
  apply le_trans (Law.Ex_mono _ (g := fun _ => ((d.card : ℝ) * (8 * Period.side e))^2) ?_)
    (Law.Ex_const _ _).le
  intro x
  have h := mul_self_le_mul_self (norm_nonneg _) (herr x)
  nlinarith

/-- The actual optimal character-prediction energy varies continuously across grid frequencies. -/
theorem paperCircleCaptureEnergy_frequency_bound (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u v : Grid (l+r+10)) :
    |paperCircleCaptureEnergy a l r k i s t u - paperCircleCaptureEnergy a l r k i s t v| ≤
      16 * (paperCircleObservationCell l i).len * rad (u-v) := by
  let scene := paperCircleObservationScene a l r k i s t
  have hn : 0 < scene.norm := by
    change 0 < (paperCircleHistoryCellScene a l r k i s).norm
    rw [paperCircleHistoryCellScene_norm]
    exact paperCircleHistoryCellScene_mass_pos a l r k i s
  have hs : share scene = 1 := by
    change (paperCircleHistoryCellScene a l r k i s).mass /
      (paperCircleHistoryCellScene a l r k i s).norm = 1
    rw [paperCircleHistoryCellScene_norm, div_self (paperCircleHistoryCellScene_mass_pos a l r k i s).ne']
  have hmag (w : Grid (l+r+10)) : Capture.magnitude true scene w =
      paperCircleCaptureEnergy a l r k i s t w := rfl
  have h1 := Snapshot.magnitude_near true scene u v
    (paperCircleObservationScene_ready a l r k i s t) hn.le 1 hs.le
  have h2 := Snapshot.magnitude_near true scene v u
    (paperCircleObservationScene_ready a l r k i s t) hn.le 1 hs.le
  simp only [hmag] at h1 h2
  change paperCircleCaptureEnergy a l r k i s t u ≤ paperCircleCaptureEnergy a l r k i s t v +
    1 * (16 * (paperCircleObservationCell l i).len * rad (u-v)) at h1
  change paperCircleCaptureEnergy a l r k i s t v ≤ paperCircleCaptureEnergy a l r k i s t u +
    1 * (16 * (paperCircleObservationCell l i).len * rad (v-u)) at h2
  rw [show v-u = -(u-v) by ring, rad_even] at h2
  rw [abs_le]
  constructor <;> linarith

end
end RHTower
