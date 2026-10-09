import GaloisForLFunctions.RHTower.WeilLogShiftDomainBoundary

/-!
# Strict outward kernel domination

Larger absolute shifts eventually dominate every fixed multiple of a smaller
shift's paired kernel. The strict gap in the existing exponential rates pays
for the comparison, without a minimum separation between shifts.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- Every fixed multiple of an inner paired kernel is eventually dominated
by a strictly outer paired kernel. The multiplier may have either sign. -/
theorem eventually_mul_pairedLogKernel_le_of_abs_lt {y c : ℝ}
    (hyc : |y| < |c|) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A * pairedLogKernel y n ≤ pairedLogKernel c n := by
  by_cases hA : A ≤ 0
  · exact Filter.Eventually.of_forall fun n =>
      (mul_nonpos_of_nonpos_of_nonneg hA (pairedLogKernel_pos y n).le).trans
        (pairedLogKernel_pos c n).le
  have hA0 : 0 < A := lt_of_not_ge hA
  have hr : logKernelCriticalRate c < logKernelCriticalRate y :=
    mul_lt_mul_of_pos_left (exp_lt_exp.mpr (neg_lt_neg hyc)) (by positivity)
  obtain ⟨b, hcb, hby⟩ := exists_between hr
  obtain ⟨a, hba, hay⟩ := exists_between hby
  have ha0 : 0 < a := (logKernelCriticalRate_pos c).trans (hcb.trans hba)
  obtain ⟨C, _, hC⟩ := exists_paired_logKernel_upper_of_lt_rate ha0 hay
  obtain ⟨D, hD, hlower⟩ := exists_paired_logKernel_lower_of_rate_lt hcb
  have hgap : 0 < a - b := sub_pos.mpr hba
  have hscaled : Tendsto (fun n : ℕ => D * exp ((a - b) * n)) atTop atTop :=
    (tendsto_exp_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hgap)).const_mul_atTop hD
  filter_upwards [hlower, hscaled.eventually_ge_atTop (A * C),
    eventually_ge_atTop (1 : ℕ)] with n hn hlarge hn1
  have hex : (D * exp ((a - b) * n)) * exp (-(a * n)) = D * exp (-(b * n)) := by
    rw [mul_assoc, ← exp_add]
    congr 1
    congr 1
    ring
  calc
    A * pairedLogKernel y n ≤ A * (C * exp (-(a * n))) :=
      mul_le_mul_of_nonneg_left (hC n hn1) hA0.le
    _ = (A * C) * exp (-(a * n)) := by ring
    _ ≤ (D * exp ((a - b) * n)) * exp (-(a * n)) :=
      mul_le_mul_of_nonneg_right hlarge (exp_pos _).le
    _ = D * exp (-(b * n)) := hex
    _ ≤ pairedLogKernel c n := hn

end RHTower
