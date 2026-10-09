import GaloisForLFunctions.RHTower.WeilLogShiftCutoffReconstruction

/-!
# Adaptive realization of recovery samples

A target policy may inspect every earlier finalized coefficient before choosing
the next sample. The current state has exactly that final prefix and the untouched
baseline tail. Positive triangular diagonals realize every such policy.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Each recovery sample is a fixed offset plus a finite linear combination
of coefficient coordinates. -/
theorem weilLogShiftRecoveryProbe_affine (lam : ℕ → ℝ) (n : ℕ) :
    weilLogShiftRecoveryProbe lam n = weilLogShiftRecoveryProbe (fun _ => 0) n +
      ∑ j ∈ Finset.Icc 2 n, lam j * weilLogShiftRecoveryWeight n j := by
  have h := weilLogShiftRecoveryProbe_sub lam (fun _ => 0) n
  simp only [sub_zero] at h
  linarith only [h]

theorem continuous_weilLogShiftRecoveryProbe (n : ℕ) :
    Continuous (fun lam : ℕ → ℝ => weilLogShiftRecoveryProbe lam n) := by
  have hfun : (fun lam : ℕ → ℝ => weilLogShiftRecoveryProbe lam n) =
      (fun lam => weilLogShiftRecoveryProbe (fun _ => 0) n +
        ∑ j ∈ Finset.Icc 2 n, lam j * weilLogShiftRecoveryWeight n j) :=
    funext fun lam => weilLogShiftRecoveryProbe_affine lam n
  rw [hfun]
  exact continuous_const.add (continuous_finsetSum _ fun j _ =>
    (continuous_apply j).mul_const _)

/-- Earlier coordinates are finalized; all later coordinates retain the baseline. -/
def weilLogShiftRecoveryPrefix (base lam : ℕ → ℝ) (n j : ℕ) : ℝ :=
  if j < n then lam j else base j

private def recoveryStep (n : ℕ) (lam : ℕ → ℝ) (target : ℝ) : ℕ → ℝ :=
  fun j => lam j + if j = n then
    (target - weilLogShiftRecoveryProbe lam n) / weilLogShiftRecoveryWeight n n else 0

private theorem recoveryStep_head (n : ℕ) (lam : ℕ → ℝ) (target : ℝ)
    (j : ℕ) (hj : j < n) : recoveryStep n lam target j = lam j := by
  simp only [recoveryStep, if_neg (show j ≠ n by omega), add_zero]

private theorem recoveryStep_value (n : ℕ) (lam : ℕ → ℝ) (target : ℝ)
    (hn : 2 ≤ n) : weilLogShiftRecoveryProbe (recoveryStep n lam target) n = target := by
  have hdiff := weilLogShiftRecoveryProbe_first_difference
    (recoveryStep n lam target) lam n hn
    (fun j _ hj => recoveryStep_head n lam target j hj)
  have hdelta : recoveryStep n lam target n - lam n =
      (target - weilLogShiftRecoveryProbe lam n) / weilLogShiftRecoveryWeight n n := by
    simp only [recoveryStep, ite_true, add_sub_cancel_left]
  rw [hdelta] at hdiff
  have hw := weilLogShiftRecoveryWeight_diagonal_pos n hn
  have hcancel : weilLogShiftRecoveryWeight n n *
      ((target - weilLogShiftRecoveryProbe lam n) / weilLogShiftRecoveryWeight n n) =
      target - weilLogShiftRecoveryProbe lam n := by field_simp [hw.ne']
  rw [hcancel] at hdiff
  linarith only [hdiff]

private def recoveryStages (base : ℕ → ℝ) (target : ℕ → (ℕ → ℝ) → ℝ) : ℕ → ℕ → ℝ
  | 0 => base
  | k + 1 => recoveryStep (k + 2) (recoveryStages base target k)
      (target k (recoveryStages base target k))

private theorem recoveryStages_head_eq (base : ℕ → ℝ) (target : ℕ → (ℕ → ℝ) → ℝ)
    (i j n : ℕ) (hij : i ≤ j) (hn : n < i + 2) :
    recoveryStages base target j n = recoveryStages base target i n := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    rw [recoveryStages, recoveryStep_head _ _ _ _ (by omega), ih]

private theorem recoveryStages_tail (base : ℕ → ℝ) (target : ℕ → (ℕ → ℝ) → ℝ)
    (k j : ℕ) (hj : k + 2 ≤ j) : recoveryStages base target k j = base j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : j ≠ k + 2 := by omega
    simp only [recoveryStages, recoveryStep, if_neg hne, add_zero]
    exact ih (by omega)

/-- Realize a policy that chooses each sample from its current coefficient state. -/
def weilLogShiftRecoveryAdaptive (base : ℕ → ℝ)
    (target : ℕ → (ℕ → ℝ) → ℝ) (n : ℕ) : ℝ :=
  recoveryStages base target n n

private theorem recoveryAdaptive_head_eq (base : ℕ → ℝ)
    (target : ℕ → (ℕ → ℝ) → ℝ) (i n : ℕ) (hn : n < i + 2) :
    weilLogShiftRecoveryAdaptive base target n = recoveryStages base target i n := by
  dsimp only [weilLogShiftRecoveryAdaptive]
  by_cases hin : i ≤ n
  · exact recoveryStages_head_eq base target i n n hin hn
  · exact (recoveryStages_head_eq base target n i n (by omega) (by omega)).symm

private theorem recoveryStages_eq_prefix (base : ℕ → ℝ)
    (target : ℕ → (ℕ → ℝ) → ℝ) (k : ℕ) :
    recoveryStages base target k =
      weilLogShiftRecoveryPrefix base (weilLogShiftRecoveryAdaptive base target) (k + 2) := by
  funext j
  by_cases hj : j < k + 2
  · rw [weilLogShiftRecoveryPrefix, if_pos hj]
    exact (recoveryAdaptive_head_eq base target k j hj).symm
  · rw [weilLogShiftRecoveryPrefix, if_neg hj]
    exact recoveryStages_tail base target k j (by omega)

theorem weilLogShiftRecoveryAdaptive_head (base : ℕ → ℝ)
    (target : ℕ → (ℕ → ℝ) → ℝ) :
    weilLogShiftRecoveryAdaptive base target 0 = base 0 ∧
      weilLogShiftRecoveryAdaptive base target 1 = base 1 := by
  exact ⟨recoveryAdaptive_head_eq base target 0 0 (by omega),
    recoveryAdaptive_head_eq base target 0 1 (by omega)⟩

/-- The policy sees the final earlier prefix and the original baseline tail. -/
theorem weilLogShiftRecoveryAdaptive_probe (base : ℕ → ℝ)
    (target : ℕ → (ℕ → ℝ) → ℝ) (k : ℕ) :
    weilLogShiftRecoveryProbe (weilLogShiftRecoveryAdaptive base target) (k + 2) =
      target k (weilLogShiftRecoveryPrefix base
        (weilLogShiftRecoveryAdaptive base target) (k + 2)) := by
  have hp := (weilLogShiftRecoveryProbe_prefix_iff
    (weilLogShiftRecoveryAdaptive base target) (recoveryStages base target (k + 1))
    (k + 2)).mpr (fun n _ hn => recoveryAdaptive_head_eq base target (k + 1) n (by omega))
  rw [hp (k + 2) (by omega) le_rfl]
  change weilLogShiftRecoveryProbe
    (recoveryStep (k + 2) (recoveryStages base target k)
      (target k (recoveryStages base target k))) (k + 2) = _
  rw [recoveryStep_value _ _ _ (by omega), recoveryStages_eq_prefix]

private theorem continuous_recoveryStages (base : ℕ → ℝ) (k : ℕ) :
    Continuous (fun height : ℕ → ℝ => recoveryStages base (fun j _ => height j) k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    apply continuous_pi
    intro n
    have hcoord := (continuous_apply n).comp ih
    have hprobe := (continuous_weilLogShiftRecoveryProbe (k + 2)).comp ih
    change Continuous (fun height : ℕ → ℝ =>
      recoveryStages base (fun j _ => height j) k n +
        if n = k + 2 then
          (height k - weilLogShiftRecoveryProbe
            (recoveryStages base (fun j _ => height j) k) (k + 2)) /
              weilLogShiftRecoveryWeight (k + 2) (k + 2) else 0)
    by_cases hn : n = k + 2
    · simp only [if_pos hn]
      exact hcoord.add (((continuous_apply k).sub hprobe).div_const _)
    · simp only [if_neg hn, add_zero]
      exact hcoord

/-- Policies independent of their state depend continuously on their chosen heights. -/
theorem continuous_weilLogShiftRecoveryAdaptive_height (base : ℕ → ℝ) :
    Continuous (fun height : ℕ → ℝ =>
      weilLogShiftRecoveryAdaptive base (fun k _ => height k)) := by
  exact continuous_pi fun n => (continuous_apply n).comp (continuous_recoveryStages base n)

end RHTower
