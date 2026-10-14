import GaloisForLFunctions.RHTower.PaperLagCayleyTraceApproximation
import GaloisForLFunctions.RHTower.KapustinGaugeSmirnovCollision
import GaloisForLFunctions.RHTower.DQPTStateError

/-! # The summable signed relative phase of the actual lag curvature

The full source and arithmetic Cayley phases admit an exact arctangent lift.
Its tail is strictly negative and has a reciprocal absolute-sum bound.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions.HTGeometry Filter _root_.Complex
open scoped Topology

def relativeAngle (n : ℕ) : ℝ := 2 * (Real.arctan (source n) - Real.arctan (arithmetic n))

def relativePhase (n : ℕ) : ℂ := (phase n : ℂ) / arithmeticPhase n

def relativeAngleTail (N : ℕ) : ℝ := ∑' n, relativeAngle (n + N)

theorem abs_relativeAngle_le (n : ℕ) :
    |relativeAngle n| ≤ 2 * |source n - arithmetic n| := by
  simpa only [relativeAngle, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
    mul_le_mul_of_nonneg_left (DQPT.dqpt_arctan_lipschitz (source n) (arithmetic n))
      (by norm_num : (0 : ℝ) ≤ 2)

theorem summable_abs_relativeAngle : Summable (fun n => |relativeAngle n|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) abs_relativeAngle_le
    (summable_source_discrepancy.mul_left 2)

theorem summable_relativeAngle : Summable relativeAngle := summable_abs_relativeAngle.of_abs

theorem relativeAngle_tail_neg (n : ℕ) : relativeAngle (n + 9) < 0 := by
  exact mul_neg_of_pos_of_neg (by norm_num)
    (sub_neg.mpr (Real.arctan_strictMono (source_tail_lt_arithmetic n)))

theorem abs_relativeAngle_tail_le (n : ℕ) :
    |relativeAngle (n + 9)| ≤ 1 / (3 * (n + 12 : ℝ) * (n + 11)) := by
  calc
    _ ≤ 2 * |source (n + 9) - arithmetic (n + 9)| := abs_relativeAngle_le _
    _ = 2 * (arithmetic (n + 9) - source (n + 9)) := by
      rw [abs_of_neg (sub_neg.mpr (source_tail_lt_arithmetic n)), neg_sub]
    _ ≤ 2 * (1 / (6 * ((n + 9 : ℕ) + 3 : ℝ) * ((n + 9 : ℕ) + 2))) :=
      mul_le_mul_of_nonneg_left (arithmetic_sub_source_le _) (by norm_num)
    _ = _ := by push_cast; field_simp; ring

theorem relativeAngle_abs_budget : (∑' n, |relativeAngle n|) ≤ 4 := by
  calc
    _ ≤ ∑' n, 2 * |source n - arithmetic n| :=
      summable_abs_relativeAngle.tsum_le_tsum abs_relativeAngle_le
        (summable_source_discrepancy.mul_left 2)
    _ = 2 * ∑' n, |source n - arithmetic n| := tsum_mul_left
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left source_discrepancy_budget (by norm_num)
    _ = 4 := by ring

theorem relativeAngle_abs_tail_sum_le (N : ℕ) :
    (∑' n, |relativeAngle (n + (N + 9))|) ≤ 1 / (3 * (N + 11 : ℝ)) := by
  let F : ℕ → ℝ := fun n => 1 / (3 * (n + N + 11 : ℝ))
  have hb (n : ℕ) : |relativeAngle (n + (N + 9))| ≤ F n - F (n + 1) := by
    have h := abs_relativeAngle_tail_le (n + N)
    rw [Nat.add_assoc] at h
    refine h.trans_eq ?_
    dsimp only [F]
    push_cast
    rw [show (n : ℝ) + 1 + N + 11 = n + N + 12 by ring]
    have h11 : (n : ℝ) + N + 11 ≠ 0 := by positivity
    have h12 : (n : ℝ) + N + 12 ≠ 0 := by positivity
    field_simp
    ring
  apply Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _)
  intro M
  calc
    _ ≤ ∑ n ∈ Finset.range M, (F n - F (n + 1)) := Finset.sum_le_sum fun n _ => hb n
    _ = F 0 - F M := Finset.sum_range_sub' F M
    _ ≤ F 0 := sub_le_self _ (by dsimp only [F]; positivity)
    _ = _ := by simp only [F, Nat.cast_zero, zero_add]

theorem relativePhase_eq_exp (n : ℕ) :
    relativePhase n = Complex.exp ((relativeAngle n : ℂ) * I) := by
  change realCayley (source n) / realCayley (arithmetic n) = _
  rw [realCayley_eq_neg_exp_two_mul_I_arctan, realCayley_eq_neg_exp_two_mul_I_arctan,
    neg_div_neg_eq, ← Complex.exp_sub]
  congr 1
  simp only [relativeAngle]
  push_cast
  ring

theorem norm_relativePhase (n : ℕ) : ‖relativePhase n‖ = 1 := by
  simp only [relativePhase, norm_div, Circle.norm_coe, div_self one_ne_zero]

theorem norm_relativePhase_sub_one (n : ℕ) :
    ‖relativePhase n - 1‖ = ‖(phase n : ℂ) - arithmeticPhase n‖ := by
  have hn : (arithmeticPhase n : ℂ) ≠ 0 := by
    intro h
    have hh := Circle.norm_coe (arithmeticPhase n)
    rw [h, norm_zero] at hh
    norm_num at hh
  have he : relativePhase n - 1 = ((phase n : ℂ) - arithmeticPhase n) / arithmeticPhase n := by
    dsimp only [relativePhase]
    field_simp
  rw [he, norm_div, Circle.norm_coe, div_one]

theorem hasProd_relativePhase_tail (N : ℕ) :
    HasProd (fun n => relativePhase (n + N))
      (Complex.exp ((relativeAngleTail N : ℂ) * I)) := by
  have hs : HasSum (fun n => relativeAngle (n + N)) (relativeAngleTail N) :=
    ((summable_nat_add_iff N).mpr summable_relativeAngle).hasSum
  have h := ((Complex.ofRealCLM.hasSum hs).mul_right I).cexp
  exact h.congr_fun fun n => relativePhase_eq_exp (n + N)

theorem relativeAngleTail_neg (N : ℕ) : relativeAngleTail (N + 9) < 0 := by
  have hs := (summable_nat_add_iff (N + 9)).mpr summable_relativeAngle
  have hn (n : ℕ) : relativeAngle (n + (N + 9)) < 0 := by
    simpa only [Nat.add_assoc] using relativeAngle_tail_neg (n + N)
  have hp := hs.neg.tsum_pos (fun n => neg_nonneg.mpr (hn n).le) 0
    (neg_pos.mpr (hn 0))
  rw [tsum_neg] at hp
  exact neg_pos.mp hp

theorem abs_relativeAngleTail_le (N : ℕ) :
    |relativeAngleTail (N + 9)| ≤ 1 / (3 * (N + 11 : ℝ)) := by
  have hs := (summable_nat_add_iff (N + 9)).mpr summable_abs_relativeAngle
  have hb := norm_tsum_le_tsum_norm (f := fun n => relativeAngle (n + (N + 9)))
    (by simpa only [Real.norm_eq_abs] using hs)
  have hb' : |relativeAngleTail (N + 9)| ≤ ∑' n, |relativeAngle (n + (N + 9))| := by
    simpa only [Real.norm_eq_abs, relativeAngleTail] using hb
  exact hb'.trans (relativeAngle_abs_tail_sum_le N)

theorem relativeAngleTail_mem_principal (N : ℕ) :
    -Real.pi < relativeAngleTail (N + 9) ∧ relativeAngleTail (N + 9) < 0 := by
  have hb := (abs_le.mp (abs_relativeAngleTail_le N)).1
  have hsmall : 1 / (3 * (N + 11 : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  exact ⟨by linarith [Real.pi_gt_three], relativeAngleTail_neg N⟩

theorem exp_relativeAngleTail_ne_one (N : ℕ) :
    Complex.exp ((relativeAngleTail (N + 9) : ℂ) * I) ≠ 1 := by
  intro he
  obtain ⟨hl, hu⟩ := relativeAngleTail_mem_principal N
  have hi : (((relativeAngleTail (N + 9) : ℝ) : ℂ) * I).im =
      relativeAngleTail (N + 9) := by simp
  have h := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (relativeAngleTail (N + 9) : ℂ) * I)
    (by simpa only [hi] using hl)
    (by rw [hi]; linarith [Real.pi_pos])
    (by simpa using neg_neg_of_pos Real.pi_pos)
    (by simpa using Real.pi_pos.le)
    (y := 0) (by simpa using he)
  have hz := congrArg Complex.im h
  simp only [hi, Complex.zero_im] at hz
  linarith

theorem norm_exp_relativeAngleTail_sub_one_le (N : ℕ) :
    ‖Complex.exp ((relativeAngleTail (N + 9) : ℂ) * I) - 1‖ ≤
      1 / (3 * (N + 11 : ℝ)) := by
  calc
    _ ≤ |relativeAngleTail (N + 9)| := by
      simpa only [mul_comm I, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := relativeAngleTail (N + 9)))
    _ ≤ _ := abs_relativeAngleTail_le N

end
end RHTower.PaperLagCayley
