/-
Doc 37 §1 (tasks #142/#143): the corrected step ledger, machine-checked.

The exact regrouping of the equilibrium-constraint difference ΔG = G_{i+1} − G_i at
matched pole-distance: the two leftover terms are the FAR-BEHIND extra
`f (t (i+2) − t 1 − s)` and the FAR-AHEAD extra `f (t d − t (i+1) + s)`; everything
else pairs into matched-index drift terms. Doc 30 §1's display listed a "near swap
extra coth((δ_{i+1}+s)/2)" — this identity refutes that bookkeeping (the near-ahead
term is PAIRED, not leftover), which is what invalidated the phantom O(1/δ) bulk
cushion (doc 37 §1). Generic in the kernel `f` and the positions `t`: pure finite-sum
algebra, no analysis. Instantiating `f x = coth (x/2)` gives the MWM step ledger.
-/
import Mathlib

namespace RHTower

open Finset

/-- The equilibrium constraint function of gap `i` (kernel `f`, positions `t`,
`d` poles): behind terms minus the near-pole term minus ahead terms, all at
matched pole-distance `s`. -/
noncomputable def ledgerG (f : ℝ → ℝ) (t : ℕ → ℝ) (d i : ℕ) (s : ℝ) : ℝ :=
  (∑ k ∈ range i, f (t (i + 1) - t (i - k) - s)) - f s
    - ∑ j ∈ range (d - i - 1), f (t (i + 2 + j) - t (i + 1) + s)

/-- **The corrected step ledger** (doc 37 §1): the difference of consecutive
constraint functions at matched distance regroups EXACTLY into the far-behind extra,
the far-ahead extra, the matched-index behind drifts, and the matched-index ahead
drifts. There is no near-field extra. -/
theorem ledger_regroup (f : ℝ → ℝ) (t : ℕ → ℝ) {d i : ℕ} (s : ℝ) (hid : i + 2 ≤ d) :
    ledgerG f t d (i + 1) s - ledgerG f t d i s
      = f (t (i + 2) - t 1 - s) + f (t d - t (i + 1) + s)
        + (∑ k ∈ range i,
            (f (t (i + 2) - t (i + 1 - k) - s) - f (t (i + 1) - t (i - k) - s)))
        + ∑ j ∈ range (d - i - 2),
            (f (t (i + 2 + j) - t (i + 1) + s) - f (t (i + 3 + j) - t (i + 2) + s)) := by
  have h1 : d - (i + 1) - 1 = d - i - 2 := by omega
  have h2 : d - i - 1 = (d - i - 2) + 1 := by omega
  have h3 : i + 2 + (d - i - 2) = d := by omega
  have h4 : i + 1 - i = 1 := by omega
  have e1 : i + 1 + 1 = i + 2 := rfl
  simp only [ledgerG, h1, e1]
  rw [Finset.sum_range_succ (fun k => f (t (i + 2) - t (i + 1 - k) - s)) i,
    h2, Finset.sum_range_succ (fun j => f (t (i + 2 + j) - t (i + 1) + s)) (d - i - 2),
    h3, h4, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have ha : (∑ j ∈ range (d - i - 2), f (t (i + 1 + 2 + j) - t (i + 2) + s))
      = ∑ j ∈ range (d - i - 2), f (t (i + 3 + j) - t (i + 2) + s) := by
    apply Finset.sum_congr rfl
    intro j _
    have hj : i + 1 + 2 + j = i + 3 + j := by omega
    rw [hj]
  rw [ha]
  ring

/-- **Sign of the behind drifts** (the "gains", doc 30 §2 / doc 37 §2): for an
antitone kernel and nonincreasing log-gaps, every matched-index behind drift term is
nonnegative. -/
theorem ledger_gain_nonneg {f : ℝ → ℝ} (hf : Antitone f) (t : ℕ → ℝ) {i k : ℕ}
    (s : ℝ) (hgap : t (i + 2) - t (i + 1) ≤ t (i + 1 - k) - t (i - k)) :
    0 ≤ f (t (i + 2) - t (i + 1 - k) - s) - f (t (i + 1) - t (i - k) - s) := by
  have harg : t (i + 2) - t (i + 1 - k) - s ≤ t (i + 1) - t (i - k) - s := by
    linarith
  linarith [hf harg]

/-- **Sign of the ahead drifts** (the "losses"): for an antitone kernel and
nonincreasing log-gaps, every matched-index ahead drift term is nonpositive — losses
must be dominated by gains plus extras, never ignored. -/
theorem ledger_loss_nonpos {f : ℝ → ℝ} (hf : Antitone f) (t : ℕ → ℝ) {i j : ℕ}
    (s : ℝ) (hgap : t (i + 3 + j) - t (i + 2 + j) ≤ t (i + 2) - t (i + 1)) :
    f (t (i + 2 + j) - t (i + 1) + s) - f (t (i + 3 + j) - t (i + 2) + s) ≤ 0 := by
  have harg : t (i + 3 + j) - t (i + 2) + s ≤ t (i + 2 + j) - t (i + 1) + s := by
    linarith
  linarith [hf harg]

end RHTower
