import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelProbeRecovery

/-!
# Entrywise stability of the inverse-probe reconstruction

The numbered diagonal has spacing at least one. Off-diagonal errors are
therefore bounded by the local readout error times the damping width.
Diagonal errors are controlled by the all-ones readout and the relevant
row and anchor column of the diagonal readout.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

theorem norm_hamiltonianAbelShift (ε : Ioi (0 : ℝ)) :
    ‖hamiltonianAbelShift ε‖ = (ε : ℝ) := by
  have he : hamiltonianAbelShift ε = ((ε : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hamiltonianAbelShift, Complex.mul_re, Complex.mul_im]
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < (ε : ℝ) from ε.2)]

private theorem norm_abelCommutatorReadout_sub_apply (ε : Ioi (0 : ℝ))
    (P X Y : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    ‖abelCommutatorReadout ε P X i j - abelCommutatorReadout ε P Y i j‖ =
      (ε : ℝ) * ‖X i j - Y i j‖ := by
  let z := hamiltonianAbelShift ε
  change ‖z * (P i j - X i j) - z * (P i j - Y i j)‖ = _
  rw [show z * (P i j - X i j) - z * (P i j - Y i j) = -(z * (X i j - Y i j)) from by ring,
    norm_neg, norm_mul, norm_hamiltonianAbelShift]

private theorem one_le_norm_probeGap {i j : Fin d} (hij : i ≠ j) :
    1 ≤ ‖(j.val : ℂ) - (i.val : ℂ)‖ := by
  rw [← Complex.ofReal_natCast j.val, ← Complex.ofReal_natCast i.val, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (show i.val < j.val from h)
    have hr : 1 ≤ (j.val : ℝ) - (i.val : ℝ) := by linarith only [hle]
    exact hr.trans (le_abs_self _)
  · have hle : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (show j.val < i.val from h)
    have hr : 1 ≤ -((j.val : ℝ) - (i.val : ℝ)) := by linarith only [hle]
    exact hr.trans (neg_le_abs _)

/-- An off-diagonal entry only depends on its own diagonal-probe
reading, with Lipschitz constant at most the damping width. -/
theorem norm_abelRelativeRecovery_sub_apply_le_of_ne (o : Fin d) (ε : Ioi (0 : ℝ))
    (D J D' J' : Matrix (Fin d) (Fin d) ℂ) {i j : Fin d} (hij : i ≠ j) :
    ‖abelRelativeRecovery o ε D J i j - abelRelativeRecovery o ε D' J' i j‖ ≤
      (ε : ℝ) * ‖D i j - D' i j‖ := by
  rw [abelRelativeRecovery_apply_ne o ε D J hij, abelRelativeRecovery_apply_ne o ε D' J' hij,
    ← sub_div, norm_div, norm_abelCommutatorReadout_sub_apply]
  exact div_le_self (mul_nonneg (show 0 < (ε : ℝ) from ε.2).le (norm_nonneg _))
    (one_le_norm_probeGap hij)

/-- Diagonal error is bounded by a single all-ones reading and the
row and anchor-column errors of the diagonal probe. -/
theorem norm_abelRelativeRecovery_sub_diag_le (o : Fin d) (ε : Ioi (0 : ℝ))
    (D J D' J' : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    ‖abelRelativeRecovery o ε D J i i - abelRelativeRecovery o ε D' J' i i‖ ≤
      (ε : ℝ) * (‖J i o - J' i o‖ + (∑ k, ‖D i k - D' i k‖) + ∑ k, ‖D k o - D' k o‖) := by
  let B := abelRelativeRecovery o ε D J
  let B' := abelRelativeRecovery o ε D' J'
  let row (M : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) := if i = k then 0 else M i k
  let col (M : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) := if k = o then 0 else M k o
  let s := abelCommutatorReadout ε (abelSumProbe d) J i o -
    abelCommutatorReadout ε (abelSumProbe d) J' i o
  have he : B i i - B' i i =
      s - (∑ k, (row B k - row B' k)) + ∑ k, (col B k - col B' k) := by
    change abelRelativeRecovery o ε D J i i - abelRelativeRecovery o ε D' J' i i = _
    rw [abelRelativeRecovery_diag o ε D J i, abelRelativeRecovery_diag o ε D' J' i]
    simp only [row, col, B, B', s, Finset.sum_sub_distrib]
    abel
  have hε : 0 ≤ (ε : ℝ) := (show 0 < (ε : ℝ) from ε.2).le
  have hsum (f : Fin d → ℂ) (g : Fin d → ℝ)
      (h : ∀ k, ‖f k‖ ≤ (ε : ℝ) * g k) :
      ‖∑ k, f k‖ ≤ (ε : ℝ) * ∑ k, g k := by
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => h k)
  have hr : ‖∑ k, (row B k - row B' k)‖ ≤ (ε : ℝ) * ∑ k, ‖D i k - D' i k‖ := by
    apply hsum
    intro k
    dsimp only [row]
    by_cases h : i = k
    · simp only [h, if_true, sub_self, norm_zero]
      exact mul_nonneg hε (norm_nonneg _)
    · simp only [if_neg h]
      exact norm_abelRelativeRecovery_sub_apply_le_of_ne o ε D J D' J' h
  have hc : ‖∑ k, (col B k - col B' k)‖ ≤ (ε : ℝ) * ∑ k, ‖D k o - D' k o‖ := by
    apply hsum
    intro k
    dsimp only [col]
    by_cases h : k = o
    · simp only [h, if_true, sub_self, norm_zero]
      exact mul_nonneg hε (norm_nonneg _)
    · simp only [if_neg h]
      exact norm_abelRelativeRecovery_sub_apply_le_of_ne o ε D J D' J' h
  have hs : ‖s‖ = (ε : ℝ) * ‖J i o - J' i o‖ :=
    norm_abelCommutatorReadout_sub_apply ε (abelSumProbe d) J J' i o
  change ‖B i i - B' i i‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖s‖ + ‖∑ k, (row B k - row B' k)‖ + ‖∑ k, (col B k - col B' k)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (ε : ℝ) * ‖J i o - J' i o‖ + (ε : ℝ) * (∑ k, ‖D i k - D' i k‖) +
        (ε : ℝ) * (∑ k, ‖D k o - D' k o‖) :=
      add_le_add (add_le_add hs.le hr) hc
    _ = _ := by ring

#print axioms norm_abelRelativeRecovery_sub_apply_le_of_ne
#print axioms norm_abelRelativeRecovery_sub_diag_le

end

end GaloisForLFunctions.HTGeometry
