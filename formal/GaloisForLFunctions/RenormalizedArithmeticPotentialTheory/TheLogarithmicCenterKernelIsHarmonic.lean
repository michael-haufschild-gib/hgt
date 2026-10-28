import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine

/-!
# The center-density kernel in pole gauge

Dividing the exact archimedean collar by the two pole weights gives the sum of
an inverse-difference kernel and an inverse-sum kernel. This identity retains
both sides of every logarithmic row and its zero diagonal.
-/

noncomputable section

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open _root_.RHTower

/-- `ω(log t) = t√t/(t² − 1)` for `t > 1`. -/
private theorem center_density_log {t : ℝ} (ht : 1 < t) :
    archLevyDensity (Real.log t) = t * Real.sqrt t / (t ^ 2 - 1) := by
  have ht0 : 0 < t := by linarith only [ht]
  have ht0' := ht0.ne'
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs' := hs.ne'
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have ht2 : t ^ 2 - 1 ≠ 0 := by nlinarith only [ht]
  unfold archLevyDensity
  have e1 : Real.exp (-Real.log t / 2) = (Real.sqrt t)⁻¹ := by
    rw [neg_div, Real.exp_neg, ← Real.log_sqrt ht0.le, Real.exp_log hs]
  have e2 : Real.exp (-2 * Real.log t) = (t ^ 2)⁻¹ := by
    rw [show -2 * Real.log t = -Real.log (t ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_neg, Real.exp_log (by positivity)]
  have hinv : (Real.sqrt t)⁻¹ = Real.sqrt t / t := by
    rw [eq_div_iff ht0', inv_mul_eq_div, div_eq_iff hs', hss]
  rw [e1, e2, hinv, show 1 - (t ^ 2)⁻¹ = (t ^ 2 - 1) / t ^ 2 by field_simp]
  field_simp

/-- **Exact algebraic value of the archimedean collar density between any two Hecke cycles.** For
`1 ≤ a < b`, `ω(log(b/a)) = b√(ab) / (b² − a²)`. -/
private theorem center_density_log_div_nat {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    archLevyDensity (Real.log ((b : ℝ) / a)) =
      (b : ℝ) * Real.sqrt ((a : ℝ) * b) / ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have ha0' := ha0.ne'
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have ht : 1 < (b : ℝ) / a := (one_lt_div ha0).mpr hab'
  have hsq : Real.sqrt ((a : ℝ) * b) = (a : ℝ) * Real.sqrt ((b : ℝ) / a) := by
    rw [show (a : ℝ) * b = (a : ℝ) ^ 2 * ((b : ℝ) / a) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha0.le]
  have hba : (b : ℝ) ^ 2 - (a : ℝ) ^ 2 ≠ 0 := by nlinarith only [ha0, hab']
  rw [center_density_log ht, hsq,
    show ((b : ℝ) / a) ^ 2 - 1 = ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / (a : ℝ) ^ 2 by field_simp]
  field_simp

/-- The off-diagonal archimedean collar weight between two positive integers:
`archimedeanCenterKernel a b = ω(|log b − log a|)` for `a ≠ b` positive, and `0` on the diagonal or at `0`. -/
def archimedeanCenterKernel (a b : ℕ) : ℝ :=
  if a = b ∨ a = 0 ∨ b = 0 then 0 else archLevyDensity |Real.log b - Real.log a|

theorem archimedeanCenterKernel_comm (a b : ℕ) : archimedeanCenterKernel a b = archimedeanCenterKernel b a := by
  unfold archimedeanCenterKernel
  have heq : (a = b ∨ a = 0 ∨ b = 0) ↔ (b = a ∨ b = 0 ∨ a = 0) := by tauto
  simp only [heq, abs_sub_comm]

theorem archimedeanCenterKernel_self (a : ℕ) : archimedeanCenterKernel a a = 0 := by
  simp [archimedeanCenterKernel]

theorem archimedeanCenterKernel_nonneg (a b : ℕ) : 0 ≤ archimedeanCenterKernel a b := by
  unfold archimedeanCenterKernel
  split_ifs with h
  · exact le_rfl
  · push Not at h
    rcases h with ⟨hab, ha0, hb0⟩
    have ha_pos : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha0
    have hb_pos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb0
    have hlog_ne : Real.log (b : ℝ) - Real.log (a : ℝ) ≠ 0 := by
      intro hsub
      have hlog_eq : Real.log (b : ℝ) = Real.log (a : ℝ) := sub_eq_zero.mp hsub
      have hba : (b : ℝ) = a := by
        have := congrArg Real.exp hlog_eq
        rwa [Real.exp_log hb_pos, Real.exp_log ha_pos] at this
      exact hab (by exact_mod_cast hba.symm)
    exact (archLevyDensity_pos (abs_pos.mpr hlog_ne)).le

/-- For `1 ≤ a < b`, `archimedeanCenterKernel a b = b√(ab) / (b² − a²)`. -/
theorem archimedeanCenterKernel_eq_of_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    archimedeanCenterKernel a b = (b : ℝ) * Real.sqrt ((a : ℝ) * b) / ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hlog : Real.log (b : ℝ) - Real.log (a : ℝ) = Real.log ((b : ℝ) / a) :=
    (Real.log_div hb0.ne' ha0.ne').symm
  have hpos : 0 < Real.log ((b : ℝ) / a) := Real.log_pos ((one_lt_div ha0).mpr hab')
  unfold archimedeanCenterKernel
  rw [if_neg (by omega), hlog, abs_of_pos hpos, center_density_log_div_nat ha hab]

private theorem archimedeanCenterKernel_div_sqrt_mul_of_lt {n j : ℕ}
    (hn : 1 ≤ n) (hnj : n < j) :
    archimedeanCenterKernel n j / (Real.sqrt n * Real.sqrt j) =
      (1 / 2 : ℝ) * (1 / ((j : ℝ) - n) + 1 / ((n : ℝ) + j)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnjR : (n : ℝ) < j := by exact_mod_cast hnj
  have hj0 : (0 : ℝ) < j := hn0.trans hnjR
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hsj : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hj0).ne'
  have hdiff : (j : ℝ) - n ≠ 0 := (sub_pos.mpr hnjR).ne'
  have hsum : (n : ℝ) + j ≠ 0 := (add_pos hn0 hj0).ne'
  have hsq : (j : ℝ) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    nlinarith only [hn0, hnjR]
  rw [archimedeanCenterKernel_eq_of_lt hn hnj, Real.sqrt_mul hn0.le]
  field_simp [hsn, hsj, hdiff, hsum, hsq]
  ring

/-- The literal collar in pole gauge is an exact symmetric harmonic kernel. -/
theorem archimedeanCenterKernel_div_sqrt_mul {n j : ℕ}
    (hn : 1 ≤ n) (hj : 1 ≤ j) (hnj : n ≠ j) :
    archimedeanCenterKernel n j / (Real.sqrt n * Real.sqrt j) =
      (1 / 2 : ℝ) * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) := by
  rcases lt_or_gt_of_ne hnj with hlt | hgt
  · rw [archimedeanCenterKernel_div_sqrt_mul_of_lt hn hlt,
      abs_of_neg (sub_neg.mpr (show (n : ℝ) < j by exact_mod_cast hlt)), neg_sub]
  · rw [archimedeanCenterKernel_comm, mul_comm (Real.sqrt n),
      archimedeanCenterKernel_div_sqrt_mul_of_lt hj hgt,
      abs_of_pos (sub_pos.mpr (show (j : ℝ) < n by exact_mod_cast hgt)),
      add_comm (j : ℝ)]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
