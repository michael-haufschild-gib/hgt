import GaloisForLFunctions.RHTower.PaperCirclePosteriorReference
import GaloisForLFunctions.RHTower.PaperCirclePosteriorPrediction
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Paths.Energies

/-! # Actual character posteriors after native spatial refinement

Each child scene supplies a genuine probability law, followed by the actual native
observation channel. The source's normalized complex mean is exactly the character
expectation of that conditional law. All scene and positivity obligations are paid
by the native construction.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure.Paths

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem paperCircleObservationScene_climb (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    Climb (paperCircleObservationScene a l r k i s t) := by
  have hn : 0 < (paperCircleObservationScene a l r k i s t).norm := by
    change 0 < (paperCircleHistoryCellScene a l r k i s).norm
    rw [paperCircleHistoryCellScene_norm]
    exact paperCircleHistoryCellScene_mass_pos a l r k i s
  have hs : share (paperCircleObservationScene a l r k i s t) = 1 := by
    change (paperCircleHistoryCellScene a l r k i s).mass /
      (paperCircleHistoryCellScene a l r k i s).norm = 1
    rw [paperCircleHistoryCellScene_norm,
      div_self (paperCircleHistoryCellScene_mass_pos a l r k i s).ne']
  exact ⟨⟨paperCircleObservationScene_ready a l r k i s t, hn, by rw [hs]; norm_num⟩,
    by change l < l+r+10; omega, by rw [hs]; norm_num⟩

def paperCircleSplitCharacterPosterior (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (b : Bool) (z : Grid (l+r+10)) : Law (Grid (l+r+10)) :=
  (((((paperCircleObservationScene a l r k i s t).smaller b).actor).withNext
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).after Prod.snd z).send Prod.fst

def paperCircleSplitCharacterMean (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (b : Bool) (u z : Grid (l+r+10)) : ℂ :=
  (paperCircleSplitCharacterPosterior a l r k i s t b z).Cx (chi u)

private lemma scene_posterior_joint {M : ℕ} (c : Scene M) (h : Wire.ReadyAt c)
    (z x : Grid M) :
    matter c z * (((c.actor.withNext (Thermal.channel c.fund.mood)).after Prod.snd z).send Prod.fst) x =
      ante c x * Thermal.channel c.fund.mood x z := by
  have hj := Law.joint_after (c.actor.withNext (Thermal.channel c.fund.mood)) Prod.fst Prod.snd x z
  simp only [Law.send_id, Law.send_snd_withNext, Law.withNext_apply] at hj
  have ha : ante c x = (c.mass / c.norm) * c.actor x := by
    unfold ante Thermal.wt
    rw [← Scene.mass_actor h.1 h.2 x]
    ring
  rw [matter, dye, hist_source _ c h.1 h.2 z, ha, mul_assoc, ← hj, ← mul_assoc]

private lemma scene_posterior_mean {M : ℕ} (c : Scene M) (h : Wire.ReadyAt c)
    (u z : Grid M) (hz : 0 < matter c z) :
    (((c.actor.withNext (Thermal.channel c.fund.mood)).after Prod.snd z).send Prod.fst).Cx (chi u) =
      meanV c u z := by
  unfold meanV
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hz.ne')).mpr
  unfold Law.Cx letter Thermal.fz
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  have hj := congrArg (fun r : ℝ => (r : ℂ)) (scene_posterior_joint c h z x)
  simp only [Complex.ofReal_mul] at hj
  change (_ * chi u x) * (matter c z : ℂ) =
    ((ante c x * Thermal.channel c.fund.mood x z : ℝ) : ℂ) * chi u x
  rw [Complex.ofReal_mul, ← hj]
  ring

/-- Bayes' identity in the common parent normalization, with actual child conditional laws. -/
theorem paperCircleSplitCharacterPosterior_joint (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (b : Bool) (z x : Grid (l+r+10)) :
    matter ((paperCircleObservationScene a l r k i s t).smaller b) z *
      paperCircleSplitCharacterPosterior a l r k i s t b z x =
        ante ((paperCircleObservationScene a l r k i s t).smaller b) x *
          Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t) x z :=
  scene_posterior_joint _ ((paperCircleObservationScene_climb a l r k i s t).child b).ready z x

theorem paperCircleSplitCharacterMean_source (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (b : Bool) (u z : Grid (l+r+10)) :
    paperCircleSplitCharacterMean a l r k i s t b u z =
      meanV ((paperCircleObservationScene a l r k i s t).smaller b) u z :=
  scene_posterior_mean _ ((paperCircleObservationScene_climb a l r k i s t).child b).ready u z
    (paperCircleHistorySplit_child_hist_pos a l r k i s t b z)

theorem paperCircleSplitCharacterMean_norm (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (b : Bool) (u z : Grid (l+r+10)) :
    ‖paperCircleSplitCharacterMean a l r k i s t b u z‖ ≤ 1 :=
  Law.norm_Cx_unit _ _ (fun x => (norm_chi u x).le)

end
end RHTower
