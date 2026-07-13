import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCancellation

/-!
# All-order theta-tail seam jets

The modular reflection law annihilates every odd jet of the completed theta source at the seam.
Transferred through `Phi = T'' - T / 4`, this gives an exact two-step recurrence, and hence a
closed formula, for every odd boundary jet of the raw one-sided theta tail.  These are the
source-specific boundary values required by any repeated integration-by-parts treatment of the
raw theta-tail/seam mixed current.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped ContDiff

namespace RHTower

noncomputable section

/-- Iterating differentiation on the theta tail just shifts its derivative index. -/
theorem iteratedDeriv_thetaCuspTailDerivative (m r : ℕ) :
    iteratedDeriv r (thetaCuspTailDerivative m) =
      thetaCuspTailDerivative (m + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [(hasDerivAt_thetaCuspTailDerivative (m + r) x).deriv]
      congr 1

/-- Every theta-tail derivative is smooth to every prescribed finite order. -/
theorem contDiff_thetaCuspTailDerivative (m n : ℕ) :
    ContDiff ℝ n (thetaCuspTailDerivative m) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro r _hr
  rw [iteratedDeriv_thetaCuspTailDerivative]
  exact differentiable_thetaCuspTailDerivative (m + r)

/-- Every odd completed theta-source jet vanishes at the modular seam. -/
theorem iteratedDeriv_thetaCuspFullSource_zero_of_odd
    {m : ℕ} (hm : Odd m) :
    iteratedDeriv m thetaCuspFullSource 0 = 0 := by
  have h := iteratedDeriv_thetaCuspFullSource_neg m 0
  rw [neg_zero] at h
  rw [hm.neg_one_pow] at h
  linarith

/-- The odd raw-tail seam jets satisfy the exact completion recurrence
`T^(m+2)(0) = T^m(0) / 4`. -/
theorem thetaCuspTailDerivative_odd_seam_step
    {m : ℕ} (hm : Odd m) :
    thetaCuspTailDerivative (m + 2) 0 =
      (1 / 4 : ℝ) * thetaCuspTailDerivative m 0 := by
  have hzero := iteratedDeriv_thetaCuspFullSource_zero_of_odd hm
  have hfun : thetaCuspFullSource = fun x : ℝ =>
      thetaCuspTailDerivative 2 x -
        (1 / 4 : ℝ) * thetaCuspTailDerivative 0 x := by
    funext x
    exact thetaCuspFullSource_eq_tail_second_sub x
  rw [hfun] at hzero
  change iteratedDeriv m
    (thetaCuspTailDerivative 2 -
      fun x => (1 / 4 : ℝ) * thetaCuspTailDerivative 0 x) 0 = 0 at hzero
  have hT2 : ContDiffAt ℝ m (thetaCuspTailDerivative 2) 0 :=
    (contDiff_thetaCuspTailDerivative 2 m).contDiffAt
  have hT0 : ContDiffAt ℝ m (thetaCuspTailDerivative 0) 0 :=
    (contDiff_thetaCuspTailDerivative 0 m).contDiffAt
  rw [iteratedDeriv_sub hT2 (contDiffAt_const.mul hT0),
    iteratedDeriv_const_mul (1 / 4 : ℝ) hT0,
    iteratedDeriv_thetaCuspTailDerivative,
    iteratedDeriv_thetaCuspTailDerivative] at hzero
  norm_num at hzero ⊢
  have h := sub_eq_zero.mp hzero
  simpa [add_comm] using h

/-- Closed form of every odd raw theta-tail boundary jet. -/
theorem thetaCuspTailDerivative_odd_seam_closed (r : ℕ) :
    thetaCuspTailDerivative (2 * r + 1) 0 =
      -((1 / 4 : ℝ) ^ (r + 1)) := by
  induction r with
  | zero =>
      simpa using thetaCuspTailDerivative_one_zero
  | succ r ih =>
      have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
      have hstep := thetaCuspTailDerivative_odd_seam_step hodd
      rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega,
        hstep, ih, pow_succ]
      ring

end

end RHTower
