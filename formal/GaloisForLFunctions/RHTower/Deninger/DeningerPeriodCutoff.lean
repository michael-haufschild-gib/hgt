import GaloisForLFunctions.RHTower.Deninger.DeningerTomographyNonstrict

/-!
# A smooth cutoff adapted to a period

The lattice sum `∑_j h(t + jL)` has no summable majorant valid on the whole line: the `j`-th term is
as large as `h` itself near `t = -jL`.  Multiplying by a cutoff that is `1` on a neighbourhood of one
period and vanishes outside a slightly larger interval restores a summable majorant, because on the
support of the cutoff the `j`-th translate is at distance at least `|j|L - R` from the origin.

* `deningerPeriodCutoff` : the bump, `1` on `[-(|L|+4), |L|+4]`, supported in `[-(|L|+5), |L|+5]`.
* `deningerPeriodCutoff_eq_one` : it is `1` on the inner interval.
* `deningerPeriodCutoff_iteratedFDeriv_eq_zero` : all its derivatives vanish outside the outer one.
* `deningerPeriodCutoff_iteratedFDeriv_bound` : a single bound for all derivatives up to any order.
-/

namespace RHTower

open Metric

noncomputable section

/-- A smooth bump equal to `1` on `[-(|L|+4), |L|+4]` and supported in `[-(|L|+5), |L|+5]`. -/
def deningerPeriodCutoff (L : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := |L| + 4
  rOut := |L| + 5
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

@[simp]
theorem deningerPeriodCutoff_rIn (L : ℝ) : (deningerPeriodCutoff L).rIn = |L| + 4 := rfl

@[simp]
theorem deningerPeriodCutoff_rOut (L : ℝ) : (deningerPeriodCutoff L).rOut = |L| + 5 := rfl

theorem deningerPeriodCutoff_contDiff (L : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deningerPeriodCutoff L : ℝ → ℝ) :=
  (deningerPeriodCutoff L).contDiff

/-- **The cutoff is `1` on the inner interval.** -/
theorem deningerPeriodCutoff_eq_one {L t : ℝ} (ht : |t| ≤ |L| + 4) :
    (deningerPeriodCutoff L : ℝ → ℝ) t = 1 := by
  refine (deningerPeriodCutoff L).one_of_mem_closedBall ?_
  simpa [Real.dist_eq] using ht

/-- **Every derivative of the cutoff vanishes outside the outer interval.** -/
theorem deningerPeriodCutoff_iteratedFDeriv_eq_zero {L t : ℝ} (ht : |L| + 5 < |t|) (i : ℕ) :
    iteratedFDeriv ℝ i (deningerPeriodCutoff L : ℝ → ℝ) t = 0 := by
  have hts : tsupport (deningerPeriodCutoff L : ℝ → ℝ) = closedBall (0 : ℝ) (|L| + 5) := by
    rw [tsupport, (deningerPeriodCutoff L).support_eq]
    exact closure_ball (0 : ℝ) (ne_of_gt (deningerPeriodCutoff L).rOut_pos)
  have hnot : t ∉ tsupport (deningerPeriodCutoff L : ℝ → ℝ) := by
    rw [hts]
    simpa [Real.dist_eq] using not_le.2 ht
  have hsub := tsupport_iteratedFDeriv_subset (𝕜 := ℝ)
    (f := (deningerPeriodCutoff L : ℝ → ℝ)) i
  by_contra hne
  exact hnot (hsub (subset_tsupport _ hne))

theorem deningerPeriodCutoff_hasCompactSupport (L : ℝ) :
    HasCompactSupport (deningerPeriodCutoff L : ℝ → ℝ) :=
  (deningerPeriodCutoff L).hasCompactSupport

/-- **A single bound for all derivatives of the cutoff up to a given order.** -/
theorem deningerPeriodCutoff_iteratedFDeriv_bound (L : ℝ) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ i ≤ k, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i (deningerPeriodCutoff L : ℝ → ℝ) t‖ ≤ D := by
  have hbd : ∀ i : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i (deningerPeriodCutoff L : ℝ → ℝ) t‖ ≤ D := by
    intro i
    have hcs : HasCompactSupport (iteratedFDeriv ℝ i (deningerPeriodCutoff L : ℝ → ℝ)) :=
      (deningerPeriodCutoff_hasCompactSupport L).iteratedFDeriv i
    have hcont : Continuous (iteratedFDeriv ℝ i (deningerPeriodCutoff L : ℝ → ℝ)) :=
      (deningerPeriodCutoff_contDiff L).continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨D, hD⟩ := hcs.exists_bound_of_continuous hcont
    exact ⟨max D 0, le_max_right _ _, fun t => le_trans (hD t) (le_max_left _ _)⟩
  choose D hDnn hDle using hbd
  refine ⟨∑ i ∈ Finset.range (k + 1), D i, Finset.sum_nonneg fun i _ => hDnn i, ?_⟩
  intro i hi t
  refine le_trans (hDle i t) ?_
  exact Finset.single_le_sum (f := D) (fun j _ => hDnn j) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

end

end RHTower
