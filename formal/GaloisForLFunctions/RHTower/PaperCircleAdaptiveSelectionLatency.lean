import GaloisForLFunctions.RHTower.PaperCircleAdaptiveSelectionBudget
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Paths.Screen

/-! # Delayed detection on actual adaptive histories

Unflagged high Fourier signals that remain uncaught occur in one depth window.
Its length is linear in the binary capacity of the path's selected frequency set.
The native posterior therefore pays a logarithmic expected delay budget, uniformly
over the tested frequency. Constant terms retain their exact expectation.
-/

open Filter
open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure.Paths

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleHistorySelectionDelay (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (x : Grid M) : ℕ :=
  Troupe.billWait ⟨main,n⟩ j ((paperCircleHistoryThread a M k s j).stream x)

/-- Distinct unflagged high depths still uncaught through the corresponding beat. -/
def paperCircleHistoryUnseenHighDepths (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (u x : Grid M) : Finset ℕ :=
  let L := (paperCircleHistoryThread a M k s j).stream x
  (L.toFinset.filter (fun b => Troupe.snag ⟨main,n⟩ u b ∧ ∃ l r : Path M,
    L = l ++ b :: r ∧ Troupe.stall u ⟨main,n⟩ j L (l ++ [b]))).image Troupe.depthB

theorem paperCircleHistoryThread_cast (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ x : Grid M,
      Troupe.Cast j M (paperCircleHistoryLikelihood a M k s)
        (paperCircleHistoryBegin a M k s).reset ((paperCircleHistoryThread a M k s j).stream x) := by
  filter_upwards [paperCircleHistoryThread_following a M k s] with j hj x
  exact Troupe.stream_cast _ hj x

theorem paperCircleHistorySelectionDelay_formula (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (x : Grid M) :
    paperCircleHistorySelectionDelay a M k s j main n x =
      1000 * (1 + paperCircleHistorySelectionCapacity a M k s j main n x + n + Compress.Params.ell j) := rfl

/-- All uncaught unflagged high depths lie in a single window, simultaneously for every frequency. -/
theorem paperCircleHistoryUnseenHighDepths_window (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (main : Bool) (n : ℕ) (u x : Grid M), ∃ start : ℕ,
      paperCircleHistoryUnseenHighDepths a M k s j main n u x ⊆
        Finset.Ico start (start + paperCircleHistorySelectionDelay a M k s j main n x) := by
  filter_upwards [paperCircleHistoryThread_cast a M k s] with j hj main n u x
  let L := (paperCircleHistoryThread a M k s j).stream x
  obtain ⟨start,hstart⟩ := Troupe.bound_stage (u := u) L (hj x) (Troupe.Grade.mk main n)
  refine ⟨start,?_⟩
  intro depth hd
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨_,hsnag,l,r,heq,hstall⟩ := Finset.mem_filter.mp hb
  apply Finset.mem_Ico.mpr
  change Troupe.betweenS start (Troupe.billWait ⟨main,n⟩ j L) b
  apply hstart (l ++ [b]) r ?_ hstall b (by simp) hsnag
  simpa only [List.append_assoc, List.singleton_append] using heq

theorem paperCircleHistoryUnseenHighDepths_card (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (main : Bool) (n : ℕ) (u x : Grid M),
      (paperCircleHistoryUnseenHighDepths a M k s j main n u x).card ≤
        paperCircleHistorySelectionDelay a M k s j main n x := by
  filter_upwards [paperCircleHistoryUnseenHighDepths_window a M k s] with j hj main n u x
  obtain ⟨start,hstart⟩ := hj main n u x
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using Finset.card_le_card hstart

/-- Exact posterior averaging preserves constant terms in the delay. -/
theorem paperCircleHistorySelectionDelay_mean (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) :
    (paperCircleHistoryPosterior a M k s).Ex (fun x =>
      (paperCircleHistorySelectionDelay a M k s j main n x : ℝ)) =
        1000 * (1 + (paperCircleHistoryPosterior a M k s).Ex (fun x =>
          (paperCircleHistorySelectionCapacity a M k s j main n x : ℝ)) + n + Compress.Params.ell j) := by
  simp only [paperCircleHistorySelectionDelay_formula, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat, Law.Ex_lmul, Law.Ex_add, Law.Ex_const]

theorem paperCircleHistorySelectionDelay_posterior_bound (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ main : Bool,
      (paperCircleHistoryPosterior a M k s).Ex (fun x =>
        (paperCircleHistorySelectionDelay a M k s j main n x : ℝ)) ≤
          1000 * (1 + (10^6 * (1 + Real.log (paperCircleHistorySelectionHeight a M k s j) + n)) /
            paperCircleHistoryEvidence a M k s + n + Compress.Params.ell j) := by
  filter_upwards [paperCircleHistorySelection_posterior_bounds a M k s n] with j hj main
  rw [paperCircleHistorySelectionDelay_mean]
  gcongr
  exact (hj main).2.1

/-- One posterior bound controls the unresolved high-depth count at every frequency. -/
theorem paperCircleHistoryUnseenHighDepths_posterior_bound (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ (main : Bool) (u : Grid M),
      (paperCircleHistoryPosterior a M k s).Ex (fun x =>
        ((paperCircleHistoryUnseenHighDepths a M k s j main n u x).card : ℝ)) ≤
          1000 * (1 + (10^6 * (1 + Real.log (paperCircleHistorySelectionHeight a M k s j) + n)) /
            paperCircleHistoryEvidence a M k s + n + Compress.Params.ell j) := by
  filter_upwards [paperCircleHistoryUnseenHighDepths_card a M k s,
    paperCircleHistorySelectionDelay_posterior_bound a M k s n] with j hc hb main u
  apply le_trans (Law.Ex_mono _ (fun x => ?_)) (hb main)
  exact_mod_cast hc main n u x

/-- The tested frequency may itself be selected after observing the entire input path. -/
theorem paperCircleHistoryUnseenHighDepths_adaptive_posterior_bound
    (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ (main : Bool) (pick : Grid M → Grid M),
      (paperCircleHistoryPosterior a M k s).Ex (fun x =>
        ((paperCircleHistoryUnseenHighDepths a M k s j main n (pick x) x).card : ℝ)) ≤
          1000 * (1 + (10^6 * (1 + Real.log (paperCircleHistorySelectionHeight a M k s j) + n)) /
            paperCircleHistoryEvidence a M k s + n + Compress.Params.ell j) := by
  filter_upwards [paperCircleHistoryUnseenHighDepths_card a M k s,
    paperCircleHistorySelectionDelay_posterior_bound a M k s n] with j hc hb main pick
  apply le_trans (Law.Ex_mono _ (fun x => ?_)) (hb main)
  exact_mod_cast hc main n (pick x) x

/-- Existence of an exceptional frequency costs no factor for the number of frequencies. -/
theorem paperCircleHistoryUnseenHighDepths_any_frequency_tail
    (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ (main : Bool) (v : ℝ),
      let B := 1000 * (1 + (10^6 * (1 + Real.log (paperCircleHistorySelectionHeight a M k s j) + n)) /
        paperCircleHistoryEvidence a M k s + n + Compress.Params.ell j)
      (paperCircleHistoryPosterior a M k s).prob (fun x => ∃ u : Grid M,
        Real.exp v * B ≤ ((paperCircleHistoryUnseenHighDepths a M k s j main n u x).card : ℝ)) ≤
          Real.exp (-v) := by
  filter_upwards [paperCircleHistoryUnseenHighDepths_card a M k s,
    paperCircleHistorySelectionDelay_posterior_bound a M k s n] with j hc hb main v
  let B := 1000 * (1 + (10^6 * (1 + Real.log (paperCircleHistorySelectionHeight a M k s j) + n)) /
    paperCircleHistoryEvidence a M k s + n + Compress.Params.ell j)
  have hB : 0 < B := by
    have hlog := Real.log_nonneg (paperCircleHistorySelectionHeight_ge_one a M k s j)
    have he := paperCircleHistoryEvidence_pos a M k s
    dsimp [B]
    positivity
  have ht := (paperCircleHistoryPosterior a M k s).upperTail
    (fun x => ∃ u : Grid M, Real.exp v * B ≤
      ((paperCircleHistoryUnseenHighDepths a M k s j main n u x).card : ℝ))
    (fun x => (paperCircleHistorySelectionDelay a M k s j main n x : ℝ))
    (fun _ => Nat.cast_nonneg _) (Real.exp v * B) (fun x ⟨u,hu⟩ =>
      hu.trans (by exact_mod_cast hc main n u x))
  have he : (Real.exp v * B) * Real.exp (-v) = B := by
    calc
      _ = (Real.exp v * Real.exp (-v)) * B := by ring
      _ = B := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have h := (ht.trans (hb main)).trans_eq he.symm
  exact le_of_mul_le_mul_left h (mul_pos (Real.exp_pos _) hB)

end
end RHTower
