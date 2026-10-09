import GaloisForLFunctions.RHTower.PaperCirclePosteriorReference

/-! # Exact conditional relative entropy from the paper's reference budget

For two actual histories and observation scales, the source's flex functional is
exactly the mean relative entropy between their next posteriors. The true native
reference has zero budget, rather than merely a nonnegative one.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCirclePosteriorCalibration (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10))) (t τ : ℝ≥0) : ℝ :=
  Capture.flex (paperCircleObservationScene a l r k i s t) true
    (paperCirclePosteriorReference a l r k i v τ)

/-- All hypotheses of the source's nonnegative reference budget are paid by native data. -/
theorem paperCirclePosteriorCalibration_nonneg (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10))) (t τ : ℝ≥0) :
    0 ≤ paperCirclePosteriorCalibration a l r k i s v t τ :=
  Capture.flex_nonneg _ (paperCircleObservationScene_ready a l r k i s t)
    (paperCircleObservationScene_mass_pos a l r k i s t) true _
    (paperCirclePosteriorReference_pos a l r k i v τ)

private lemma cell_log_density (l r : ℕ) (i : Fin (2^l)) (x : Grid (l+r+10))
    (hx : x ∈ (paperCircleObservationCell l i).block (l+r+10)) :
    -Real.log ((paperCircleObservationCell l i).dice (l+r+10) x) = (r+10 : ℕ) * Real.log 2 := by
  rw [Node.dice_apply (paperCircleObservationCell_ok l r i), if_pos hx,
    Real.log_mul (Period.side_pos _).ne' (inv_pos.mpr (paperCircleObservationCell l i).len_pos).ne']
  simp only [paperCircleObservationCell, Node.len, side_pow_two, Real.log_inv, Real.log_pow]
  push_cast
  ring

/-- Cross entropy of the reference posterior is its exact negative log-likelihood cost. -/
theorem paperCirclePosteriorReference_cross_entropy (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (z : Grid (l+r+10)) :
    (paperCircleNextPosterior a l r k i s t z).crossE (paperCircleNextPosterior a l r k i v τ z) =
      (r+10 : ℕ) * Real.log 2 - (paperCircleNextPosterior a l r k i s t z).Ex
        (fun x => Real.log (paperCirclePosteriorReference a l r k i v τ z x)) := by
  unfold Law.crossE
  rw [← Law.Ex_const (paperCircleNextPosterior a l r k i s t z) ((r+10 : ℕ) * Real.log 2),
    ← Law.Ex_sub]
  apply Law.Ex_congr_mem
  intro x hx
  have hm := (paperCircleNextPosterior_pos_iff a l r k i s t z x).mp hx
  rw [← paperCirclePosteriorReference_density,
    Real.log_mul ((Node.dice_positive (paperCircleObservationCell_ok l r i)).mpr hm).ne'
      (paperCirclePosteriorReference_pos a l r k i v τ z x).ne']
  have h := cell_log_density l r i x hm
  linarith

/-- The source flex budget is exactly the actual mean posterior KL divergence. -/
theorem paperCirclePosteriorCalibration_kl (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10))) (t τ : ℝ≥0) :
    paperCirclePosteriorCalibration a l r k i s v t τ =
      (paperCircleNextObservationLaw a l r k i s t).Ex
        (fun z => (paperCircleNextPosterior a l r k i s t z).kl
          (paperCircleNextPosterior a l r k i v τ z)) := by
  let P := paperCircleHistoryCellPosterior a l r k i s
  let K := Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)
  let J := P.withNext K
  let scene := paperCircleObservationScene a l r k i s t
  have ht : Capture.tracker scene true = J := by
    change scene.actor.withNext K = _
    rw [paperCircleObservationScene_actor]
  have hl : levels scene = (r+10 : ℕ) * Real.log 2 := by
    change ((l+r+10-l : ℕ) : ℝ) * Real.log 2 = _
    rw [show l+r+10-l = r+10 by omega]
  have hd : deficit scene (Thermal.channel (Capture.optic scene true)) =
      levels scene - P.privateH K := by
    change levels scene - scene.actor.privateH K = _
    rw [paperCircleObservationScene_actor]
  have hcross :
      (paperCircleNextObservationLaw a l r k i s t).Ex
        (fun z => (paperCircleNextPosterior a l r k i s t z).crossE
          (paperCircleNextPosterior a l r k i v τ z)) =
      (r+10 : ℕ) * Real.log 2 - J.Ex
        (fun w => Real.log (paperCirclePosteriorReference a l r k i v τ w.2 w.1)) := by
    simp only [paperCirclePosteriorReference_cross_entropy, Law.Ex_sub, Law.Ex_const]
    rw [← paperCircleNextPosterior_disintegration a l r k i s t
      (fun z x => Real.log (paperCirclePosteriorReference a l r k i v τ z x))]
  unfold paperCirclePosteriorCalibration
  change Capture.flex scene true _ = _
  rw [Capture.flex, ht, hd]
  simp only [scene, paperCirclePosteriorReference_normalized, Real.log_one, zero_sub,
    Law.Ex_neg, Law.kl, Law.Ex_sub]
  rw [hcross, ← paperCircleNextPosterior_entropy]
  change levels scene - P.privateH K + -(J.Ex _) =
    (r+10 : ℕ) * Real.log 2 - J.Ex _ - P.privateH K
  rw [hl]
  ring

theorem paperCirclePosteriorCalibration_self (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCirclePosteriorCalibration a l r k i s s t t = 0 := by
  rw [paperCirclePosteriorCalibration_kl]
  simp only [Law.kl, Law.entropy, sub_self, Law.Ex_const]

/-- Source Pinsker applied to the two actual conditional posteriors at every output. -/
theorem paperCirclePosteriorCalibration_tv_sq (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10))) (t τ : ℝ≥0) :
    (paperCircleNextObservationLaw a l r k i s t).Ex
      (fun z => ((paperCircleNextPosterior a l r k i s t z).tv
        (paperCircleNextPosterior a l r k i v τ z))^2) ≤
      paperCirclePosteriorCalibration a l r k i s v t τ := by
  rw [paperCirclePosteriorCalibration_kl]
  exact Law.Ex_mono _ (fun z => Law.tv_sq_le_kl (paperCircleNextPosterior_dominated a l r k i s v t τ z))

end
end RHTower
