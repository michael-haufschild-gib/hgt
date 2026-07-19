import GaloisForLFunctions.HTGeometry.InterNode

/-!
# A root above the largest node

Above the largest root of `Q_{n+1}` there is a root of `Q_{n+2}`.  The cofactor at that node is
monic
with all its roots below, so it is positive there; the confluent identity then makes `Qₙ` positive
there too, and the collapsed recurrence makes `Q_{n+2}` negative.  Since `Q_{n+2}` is monic it is
eventually positive, so a root lies above.

Together with the gap selection this accounts for one of the two level-`n+1` nodes outside the span
of the level-`n` nodes.
-/

open scoped BigOperators
open Polynomial Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- A monic real polynomial is eventually positive. -/
theorem monic_eventually_pos {P : Polynomial ℝ} (hP : P.Monic) :
    ∀ᶠ x in atTop, 0 < P.eval x := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
  · have hc : P.coeff 0 = 1 := by
      rw [← h0, Polynomial.coeff_natDegree]
      exact hP
    have hP1 : P = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_one]
    simp [hP1]
  · have hdeg : 0 < P.degree := natDegree_pos_iff_degree_pos.mp hpos
    have hlc : (0 : ℝ) ≤ P.leadingCoeff := by rw [hP]; norm_num
    exact Filter.Tendsto.eventually_gt_atTop
      (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg (P := P) hdeg hlc) 0

/-- **A root of `Q_{n+2}` above every root of `Q_{n+1}`.** -/
theorem exists_root_above_last (h : PositiveMomentForm s) (n : ℕ) :
    ∃ z, gaussNode h n (Fin.last n) < z ∧ (monicOrtho s (n + 2)).eval z = 0 := by
  set xi := gaussNode h n (Fin.last n) with hxidef
  obtain ⟨G, hG, hG0⟩ := exists_cofactor h n (gaussNode_root h n (Fin.last n))
  have hGmonic : G.Monic :=
    Monic.of_mul_monic_left (monic_X_sub_C xi) (hG ▸ monicOrtho_monic s (n + 1))
  have hmax : ∀ y, (monicOrtho s (n + 1)).eval y = 0 → y ≤ xi := by
    intro y hy
    obtain ⟨j, hj⟩ := exists_gaussNode_eq h n hy
    rw [← hj]
    exact (gaussNode h n).monotone (Fin.le_last j)
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp (monic_eventually_pos hGmonic)
  obtain ⟨R1, hR1⟩ := eventually_atTop.mp (monic_eventually_pos (monicOrtho_monic s (n + 2)))
  set R := max (max R0 R1) (xi + 1) with hRdef
  have hxiR : xi < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hGR : 0 < G.eval R := hR0 R (le_trans (le_max_left R0 R1) (le_max_left _ _))
  have hQR : 0 < (monicOrtho s (n + 2)).eval R :=
    hR1 R (le_trans (le_max_right R0 R1) (le_max_left _ _))
  -- the cofactor is positive at the largest node
  have hGpos : 0 < G.eval xi := by
    have hsign := mul_pos_of_ne_zero_on_Icc hxiR.le (continuousOn_eval G _) (fun y hy => ?_)
    · nlinarith [hsign, hGR]
    · rcases eq_or_lt_of_le hy.1 with heq | hlt
      · rw [← heq]; exact hG0
      · intro h0
        have hyroot : (monicOrtho s (n + 1)).eval y = 0 := by rw [hG]; simp [h0]
        exact absurd (hmax y hyroot) (not_le.mpr hlt)
  -- hence `Qₙ` is positive and `Q_{n+2}` is negative there
  have hQn : 0 < (monicOrtho s n).eval xi := by
    have := cofactor_mul_monicOrtho_pos h n hG
    nlinarith [this, hGpos]
  have hQ2 : (monicOrtho s (n + 2)).eval xi < 0 := by
    rw [monicOrtho_eval_succ_succ_of_root h n (gaussNode_root h n (Fin.last n))]
    nlinarith [recurOff_pos h n, hQn]
  obtain ⟨z, hz, hfz⟩ := intermediate_value_Ioo hxiR.le
    (continuousOn_eval (monicOrtho s (n + 2)) _) ⟨hQ2, hQR⟩
  exact ⟨z, hz.1, hfz⟩

end HTGeometry
