import GaloisForLFunctions.RHTower.PaperCircleSplitFisherOverlap
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Capture.Dual

/-! # Actual posterior character prediction from native circle observations

The next posterior is the conditional law of the latent grid point given the
actual next observation. Its character mean identifies the source's Fourier
numerator, with every observation having strictly positive mass.
-/

open scoped BigOperators NNReal Classical ComplexConjugate
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleNextObservationLaw (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) : Law (Grid (l+r+10)) :=
  (paperCircleHistoryCellPosterior a l r k i s).through
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))

theorem paperCircleHistoryCellScene_ante (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (x : Grid (l+r+10)) :
    ante (paperCircleHistoryCellScene a l r k i s) x =
      paperCircleHistoryCellPosterior a l r k i s x := by
  rw [← paperCircleHistoryCellScene_actor a l r k i s,
    Scene.actor_def (paperCircleObservationCell_ok l r i)
      (fun x => (paperCircleHistoryLikelihood_pos a (l+r+10) k s x).le)
      (paperCircleHistoryCellScene_mass_pos a l r k i s), ante,
    paperCircleHistoryCellScene_norm]
  rfl

theorem paperCircleNextObservationLaw_hist (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z : Grid (l+r+10)) :
    hist (paperCircleHistoryCellScene a l r k i s)
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z =
      paperCircleNextObservationLaw a l r k i s t z := by
  unfold hist
  change (∑ x, ante (paperCircleHistoryCellScene a l r k i s) x * _) = _
  simp only [paperCircleHistoryCellScene_ante]
  rfl

theorem paperCircleNextObservationLaw_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z : Grid (l+r+10)) :
    0 < paperCircleNextObservationLaw a l r k i s t z := by
  rw [← paperCircleNextObservationLaw_hist]
  exact paperCircleHistorySplit_hist_pos a l r k i s t z

def paperCircleNextPosterior (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) : Law (Grid (l+r+10)) :=
  (((paperCircleHistoryCellPosterior a l r k i s).withNext
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).after Prod.snd z).send Prod.fst

/-- Bayes' joint identity for the actual native observation, with no exceptional outputs. -/
theorem paperCircleNextPosterior_joint (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z x : Grid (l+r+10)) :
    paperCircleNextObservationLaw a l r k i s t z * paperCircleNextPosterior a l r k i s t z x =
      paperCircleHistoryCellPosterior a l r k i s x *
        Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t) x z := by
  have h := Law.joint_after
    ((paperCircleHistoryCellPosterior a l r k i s).withNext
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))) Prod.fst Prod.snd x z
  simpa only [paperCircleNextObservationLaw, paperCircleNextPosterior,
    Law.send_id, Law.send_snd_withNext, Law.withNext_apply] using h.symm

theorem paperCircleNextPosterior_apply (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z x : Grid (l+r+10)) :
    paperCircleNextPosterior a l r k i s t z x =
      (paperCircleHistoryCellPosterior a l r k i s x *
        Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t) x z) /
          paperCircleNextObservationLaw a l r k i s t z := by
  apply (eq_div_iff (paperCircleNextObservationLaw_pos a l r k i s t z).ne').mpr
  rw [mul_comm]
  exact paperCircleNextPosterior_joint a l r k i s t z x

theorem paperCircleNextPosterior_pos_iff (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z x : Grid (l+r+10)) :
    0 < paperCircleNextPosterior a l r k i s t z x ↔
      x ∈ (paperCircleObservationCell l i).block (l+r+10) := by
  rw [paperCircleNextPosterior_apply,
    div_pos_iff_of_pos_right (paperCircleNextObservationLaw_pos a l r k i s t z),
    mul_pos_iff_of_pos_right (Thermal.ch_pos _ x z), paperCircleHistoryCellPosterior_pos_iff]

/-- Disintegration uses the genuine next posterior at every output. -/
theorem paperCircleNextPosterior_disintegration (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (f : Grid (l+r+10) → Grid (l+r+10) → ℝ) :
    ((paperCircleHistoryCellPosterior a l r k i s).withNext
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Ex (fun v => f v.2 v.1) =
    (paperCircleNextObservationLaw a l r k i s t).Ex
      (fun z => (paperCircleNextPosterior a l r k i s t z).Ex (f z)) := by
  have h := Law.after_Ex_sum
    ((paperCircleHistoryCellPosterior a l r k i s).withNext
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))) Prod.snd (fun z v => f z v.1)
  rw [Law.send_snd_withNext] at h
  simpa only [paperCircleNextPosterior, Law.Ex_send, paperCircleNextObservationLaw] using h.symm

def paperCircleNextCharacterMean (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (u z : Grid (l+r+10)) : ℂ :=
  (paperCircleNextPosterior a l r k i s t z).Cx (chi u)

theorem paperCircleNextCharacterMean_norm (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u z : Grid (l+r+10)) :
    ‖paperCircleNextCharacterMean a l r k i s t u z‖ ≤ 1 :=
  Law.norm_Cx_unit _ _ (fun x => (norm_chi u x).le)

/-- The paper's unnormalized Fourier moment is observation mass times posterior mean. -/
theorem paperCircleNextCharacterMean_source (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u z : Grid (l+r+10)) :
    Thermal.fz (paperCircleObservationCell l i) (paperCircleHistoryLikelihood a (l+r+10) k s)
      (paperCircleHistoryCellScene a l r k i s).norm
      (paperCircleLocalizedForm a (l+r+10) k t) u z =
    (paperCircleNextObservationLaw a l r k i s t z : ℂ) *
      paperCircleNextCharacterMean a l r k i s t u z := by
  unfold paperCircleNextCharacterMean Law.Cx Thermal.fz Thermal.omegaObs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, ← Complex.ofReal_mul, paperCircleNextPosterior_joint]
  congr 2
  change ante (paperCircleHistoryCellScene a l r k i s) x * _ = _
  rw [paperCircleHistoryCellScene_ante]

end
end RHTower
