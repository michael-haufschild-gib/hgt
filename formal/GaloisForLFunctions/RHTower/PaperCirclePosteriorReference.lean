import GaloisForLFunctions.RHTower.PaperCirclePredictionLaw
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Capture.Flex

/-! # Positive native posterior reference densities

The scene carries the actual next observation. Every other native history and
observation scale supplies a strictly positive reference density whose integral
against the uniform cell law is exactly one. Its induced law is the genuine
conditional posterior, including at every possible output.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleObservationScene (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) : Scene (l+r+10) :=
  let base := paperCircleHistoryCellScene a l r k i s
  { base with fund := { base.fund with mood := paperCircleLocalizedForm a (l+r+10) k t } }

theorem paperCircleObservationScene_actor (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    (paperCircleObservationScene a l r k i s t).actor = paperCircleHistoryCellPosterior a l r k i s :=
  paperCircleHistoryCellScene_actor a l r k i s

theorem paperCircleObservationScene_ready (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    Wire.ReadyAt (paperCircleObservationScene a l r k i s t) :=
  ⟨paperCircleObservationCell_ok l r i,
    fun x => (paperCircleHistoryLikelihood_pos a (l+r+10) k s x).le⟩

theorem paperCircleObservationScene_mass_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    0 < (paperCircleObservationScene a l r k i s t).mass :=
  paperCircleHistoryCellScene_mass_pos a l r k i s

/-- Actual conditional-posterior density relative to the uniform cell law. -/
def paperCirclePosteriorReference (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (v : List (ℝ≥0 × Grid (l+r+10))) (τ : ℝ≥0)
    (z x : Grid (l+r+10)) : ℝ :=
  paperCircleHistoryLikelihood a (l+r+10) k v x /
    ((paperCircleHistoryCellScene a l r k i v).norm * paperCircleNextObservationLaw a l r k i v τ z) *
      Thermal.channel (paperCircleLocalizedForm a (l+r+10) k τ) x z

theorem paperCirclePosteriorReference_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (v : List (ℝ≥0 × Grid (l+r+10)))
    (τ : ℝ≥0) (z x : Grid (l+r+10)) :
    0 < paperCirclePosteriorReference a l r k i v τ z x := by
  unfold paperCirclePosteriorReference
  rw [paperCircleHistoryCellScene_norm]
  exact mul_pos (div_pos (paperCircleHistoryLikelihood_pos a (l+r+10) k v x)
    (mul_pos (paperCircleHistoryCellScene_mass_pos a l r k i v)
      (paperCircleNextObservationLaw_pos a l r k i v τ z))) (Thermal.ch_pos _ x z)

theorem paperCirclePosteriorReference_density (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (v : List (ℝ≥0 × Grid (l+r+10)))
    (τ : ℝ≥0) (z x : Grid (l+r+10)) :
    (paperCircleObservationCell l i).dice (l+r+10) x * paperCirclePosteriorReference a l r k i v τ z x =
      paperCircleNextPosterior a l r k i v τ z x := by
  rw [paperCircleNextPosterior_apply, ← paperCircleHistoryCellScene_ante]
  change _ = ((paperCircleObservationCell l i).dice (l+r+10) x *
    paperCircleHistoryLikelihood a (l+r+10) k v x /
      (paperCircleHistoryCellScene a l r k i v).norm * _) / _
  simp only [paperCirclePosteriorReference, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The source reference normalizer is exactly one, for every target history. -/
theorem paperCirclePosteriorReference_normalized (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (z : Grid (l+r+10)) :
    Capture.normQ (paperCircleObservationScene a l r k i s t)
      (paperCirclePosteriorReference a l r k i v τ) z = 1 := by
  change (∑ x, (paperCircleObservationCell l i).dice (l+r+10) x *
    paperCirclePosteriorReference a l r k i v τ z x) = 1
  simp only [paperCirclePosteriorReference_density, Law.total]

theorem paperCircleNextPosterior_dominated (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (z : Grid (l+r+10)) :
    (paperCircleNextPosterior a l r k i s t z).dominated
      (paperCircleNextPosterior a l r k i v τ z) := by
  intro x hx
  exact (paperCircleNextPosterior_pos_iff a l r k i v τ z x).mpr
    ((paperCircleNextPosterior_pos_iff a l r k i s t z x).mp hx)

/-- Actual conditional entropy is the mean entropy of the next posteriors. -/
theorem paperCircleNextPosterior_entropy (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    (paperCircleHistoryCellPosterior a l r k i s).privateH
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) =
      (paperCircleNextObservationLaw a l r k i s t).Ex
        (fun z => (paperCircleNextPosterior a l r k i s t z).entropy) := by
  rw [Law.privateH, Law.Hcond_after, Law.send_snd_withNext]
  rfl

end
end RHTower
