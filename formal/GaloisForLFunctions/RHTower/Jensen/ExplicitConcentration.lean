import GaloisForLFunctions.RHTower.XiThetaHermiteMixedLimit

/-!
# Explicit concentration at the Xi Jensen saddle

The local Ward inequality gives a reciprocal-saddle bound for every positive
even fluctuation moment. Finite sums make the bound uniform through any fixed
degree, and a score ceiling gives an explicit saddle threshold.
-/

open Real Polynomial Finset
noncomputable section
namespace RHTower

/-- Cubic growth of the score controls the local Ward tail without a limit. -/
theorem cube_le_thetaJensenScore {s : ℝ} (hs : 2 ≤ s) : s ^ 3 ≤ thetaJensenScore s := by
  have hs0 : 0 < s := by linarith only [hs]
  have he : (s + 1) ^ 2 ≤ Real.exp (2 * s) := by
    calc
      _ ≤ Real.exp s ^ 2 := (sq_le_sq₀ (by positivity) (Real.exp_pos s).le).mpr
        (by simpa only [add_comm] using Real.add_one_le_exp s)
      _ = _ := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos (2 * s)).le
  have hb : s ^ 2 ≤ Real.pi * Real.exp (2 * s) - 9 / 4 := by
    nlinarith only [he, hp, hs]
  rw [thetaJensenScore_eq]
  nlinarith only [mul_le_mul_of_nonneg_left hb hs0.le]

theorem thetaJensenSaddle_sq_div_le_inv (n : ℕ) (hs : 2 ≤ thetaJensenSaddle n) :
    thetaJensenSaddle n ^ 2 / ((n : ℝ) + 1 / 2) ≤ 1 / thetaJensenSaddle n := by
  have hs0 := thetaJensenSaddle_pos n
  have hc := cube_le_thetaJensenScore hs
  rw [thetaJensenSaddle_score] at hc
  calc
    _ ≤ thetaJensenSaddle n ^ 2 / thetaJensenSaddle n ^ 3 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hc
    _ = _ := by field_simp

/-- A score ceiling is sufficient to exceed any prescribed nonnegative saddle height. -/
theorem le_thetaJensenSaddle_of_score_ceil_le {S : ℝ} (hS : 0 ≤ S) {n : ℕ}
    (hn : ⌈thetaJensenScore S⌉₊ ≤ n) : S ≤ thetaJensenSaddle n := by
  have hceil : thetaJensenScore S ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  by_contra h
  have hs :=
    (thetaCuspGaussianApertureExactTailSaddleDegree_strictMonoOn_Ici_zero (by rfl)).monotoneOn
      (thetaJensenSaddle_pos n).le hS (lt_of_not_ge h).le
  change thetaJensenScore (thetaJensenSaddle n) ≤ thetaJensenScore S at hs
  rw [thetaJensenSaddle_score] at hs
  linarith only [hs, hceil]

/-- Explicit numerator in the reciprocal-saddle centered-moment bound. -/
def thetaJensenConcentrationConstant (p : ℕ) : ℝ :=
  12 * Real.exp 2 * (2 * (p : ℝ) + 1) * thetaJensenMomentBoundConstant p +
    8 * Real.exp 2 * (2 * (p : ℝ) + 1) * thetaJensenMomentBoundConstant (p + 1) +
      thetaJensenMomentBoundConstant (p + 2)

theorem thetaJensenConcentrationConstant_pos (p : ℕ) : 0 < thetaJensenConcentrationConstant p := by
  have h₀ := thetaJensenMomentBoundConstant_pos p
  have h₁ := thetaJensenMomentBoundConstant_pos (p + 1)
  have h₂ := thetaJensenMomentBoundConstant_pos (p + 2)
  unfold thetaJensenConcentrationConstant
  positivity

theorem thetaJensenNormalizedCenteredMoment_le_explicit (n p : ℕ)
    (hs : 2 ≤ thetaJensenSaddle n) (hn : 4 * ((p : ℝ) + 2) ≤ n) :
    thetaJensenNormalizedCenteredMoment n (p + 1) ≤
      thetaJensenConcentrationConstant p / thetaJensenSaddle n := by
  have hs0 := thetaJensenSaddle_pos n
  have h₀ := thetaJensenNormalizedCenteredMoment_le n p (by linarith only [hs])
    (by linarith only [hn])
  have h₁ := thetaJensenNormalizedCenteredMoment_le n (p + 1) (by linarith only [hs])
    (by push_cast; linarith only [hn])
  have h₂ := thetaJensenNormalizedCenteredMoment_le n (p + 2) (by linarith only [hs])
    (by push_cast; linarith only [hn])
  have hcoef : 4 * Real.exp 2 * (2 * (p : ℝ) + 1) /
      (((n : ℝ) + 1 / 2) * thetaJensenSaddle n) ≤
        8 * Real.exp 2 * (2 * (p : ℝ) + 1) / thetaJensenSaddle n := by
    apply (div_le_div_iff₀ (by positivity) hs0).mpr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith only [mul_nonneg hn0
      (show 0 ≤ 8 * Real.exp 2 * (2 * (p : ℝ) + 1) * thetaJensenSaddle n by positivity)]
  have hfirst := mul_le_mul_of_nonneg_left h₀
    (show 0 ≤ 12 * Real.exp 2 * (2 * (p : ℝ) + 1) / thetaJensenSaddle n by positivity)
  have hsecond := (mul_le_mul_of_nonneg_left h₁
    (show 0 ≤ 4 * Real.exp 2 * (2 * (p : ℝ) + 1) /
      (((n : ℝ) + 1 / 2) * thetaJensenSaddle n) by positivity)).trans
        (mul_le_mul_of_nonneg_right hcoef (thetaJensenMomentBoundConstant_pos (p + 1)).le)
  have hthird := (mul_le_mul_of_nonneg_left h₂
    (show 0 ≤ thetaJensenSaddle n ^ 2 / ((n : ℝ) + 1 / 2) by positivity)).trans
      (mul_le_mul_of_nonneg_right (thetaJensenSaddle_sq_div_le_inv n hs)
        (thetaJensenMomentBoundConstant_pos (p + 2)).le)
  exact ((thetaJensenNormalizedCenteredMoment_local_bound n p hs).trans
    (add_le_add (add_le_add hfirst hsecond) hthird)).trans_eq
      (by unfold thetaJensenConcentrationConstant; ring)

/-- Full-source comparison applied to the explicit leading-channel bound. -/
def xiThetaConcentrationConstant (p : ℕ) : ℝ :=
  3 * thetaJensenConcentrationConstant p

theorem xiThetaConcentrationConstant_pos (p : ℕ) : 0 < xiThetaConcentrationConstant p :=
  mul_pos (by norm_num) (thetaJensenConcentrationConstant_pos p)

theorem xiThetaSourceComparisonFactor_le_three : xiThetaSourceComparisonFactor ≤ 3 := by
  unfold xiThetaSourceComparisonFactor
  linarith only [thetaCuspHigherAtomDominationWeight_le_one_div_three_hundred]

theorem xiThetaExpectation_fluctuation_succ_abs_le (n p : ℕ)
    (hs : 2 ≤ thetaJensenSaddle n) (hn : 4 * ((p : ℝ) + 2) ≤ n) :
    |xiThetaExpectation n (xiThetaFluctuation n ^ (p + 1))| ≤
      Real.sqrt (xiThetaConcentrationConstant p / thetaJensenSaddle n) := by
  have hb := (xiThetaNormalizedCenteredMoment_le n (p + 1)).trans
    (mul_le_mul_of_nonneg_left (thetaJensenNormalizedCenteredMoment_le_explicit n p hs hn)
      xiThetaSourceComparisonFactor_pos.le)
  have hb' := hb.trans (mul_le_mul_of_nonneg_right xiThetaSourceComparisonFactor_le_three
    (div_nonneg (thetaJensenConcentrationConstant_pos p).le (thetaJensenSaddle_pos n).le))
  have hsq := xiThetaExpectation_fluctuation_sq_le n (p + 1)
  rw [xiThetaExpectation_fluctuation_even] at hsq
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (div_nonneg (xiThetaConcentrationConstant_pos p).le
    (thetaJensenSaddle_pos n).le)]
  exact hsq.trans (hb'.trans_eq (by unfold xiThetaConcentrationConstant; ring))

/-- One finite numerator controls every fluctuation moment through degree `d`. -/
def xiJensenFluctuationBound (d : ℕ) : ℝ :=
  1 + ∑ p ∈ range d, xiThetaConcentrationConstant p

theorem one_le_xiJensenFluctuationBound (d : ℕ) : 1 ≤ xiJensenFluctuationBound d := by
  have hsum := Finset.sum_nonneg (fun p (_ : p ∈ range d) => (xiThetaConcentrationConstant_pos p).le)
  unfold xiJensenFluctuationBound
  linarith only [hsum]

theorem xiThetaConcentrationConstant_le_fluctuationBound {p d : ℕ} (hp : p < d) :
    xiThetaConcentrationConstant p ≤ xiJensenFluctuationBound d := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ range d) =>
    (xiThetaConcentrationConstant_pos i).le) (Finset.mem_range.mpr hp)
  unfold xiJensenFluctuationBound
  linarith only [h]

theorem xiThetaExpectation_fluctuation_error_le (n d k : ℕ)
    (hs : 2 ≤ thetaJensenSaddle n) (hn : 4 * (d + 1) ≤ n) (hk : k ≤ d) :
    |xiThetaExpectation n (xiThetaFluctuation n ^ k) - (if k = 0 then 1 else 0)| ≤
      Real.sqrt (xiJensenFluctuationBound d / thetaJensenSaddle n) := by
  cases k with
  | zero => simpa only [pow_zero, xiThetaExpectation_one, if_pos rfl, ite_true, sub_self, abs_zero] using
      Real.sqrt_nonneg (xiJensenFluctuationBound d / thetaJensenSaddle n)
  | succ p =>
    simp only [Nat.succ_ne_zero, if_false, sub_zero]
    have hn' : 4 * ((p : ℝ) + 2) ≤ n := by
      have hp : 4 * (p + 2) ≤ n := by omega
      exact_mod_cast hp
    exact (xiThetaExpectation_fluctuation_succ_abs_le n p hs hn').trans
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
        (xiThetaConcentrationConstant_le_fluctuationBound (by omega)) (thetaJensenSaddle_pos n).le))

theorem xiJensenDelta_le_fluctuationBound (n d : ℕ) (hs : 2 ≤ thetaJensenSaddle n) :
    xiJensenDelta n ≤ Real.sqrt (xiJensenFluctuationBound d / thetaJensenSaddle n) := by
  have hs0 := thetaJensenSaddle_pos n
  have hr : 0 < (n : ℝ) + 1 / 2 := by positivity
  have hc := cube_le_thetaJensenScore hs
  rw [thetaJensenSaddle_score] at hc
  have hsq : 1 ≤ thetaJensenSaddle n ^ 2 := by nlinarith only [hs]
  have hcube : thetaJensenSaddle n ≤ thetaJensenSaddle n ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_left hsq hs0.le]
  have hδ : xiJensenDelta n ^ 2 = 1 / ((n : ℝ) + 1 / 2) := by
    apply (eq_div_iff hr.ne').mpr
    nlinarith only [xiJensenDelta_sq n]
  rw [← Real.sqrt_sq (xiJensenDelta_pos n).le, hδ]
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ hr hs0).mpr
  have hF := mul_le_mul_of_nonneg_right (one_le_xiJensenFluctuationBound d) hr.le
  nlinarith only [hF, hcube, hc]

end RHTower

#print axioms RHTower.le_thetaJensenSaddle_of_score_ceil_le
#print axioms RHTower.thetaJensenNormalizedCenteredMoment_le_explicit
#print axioms RHTower.xiThetaExpectation_fluctuation_error_le
#print axioms RHTower.xiJensenDelta_le_fluctuationBound
