import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarTentRegularity
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalSource

/-! Explicit Lipschitz and L¹ budgets for the pole-cancelling factorial ramp. -/

open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

private theorem factorial_exp_le {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : x ≤ Real.log (4*(N : ℝ)+1)) : Real.exp x ≤ 5*(N : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ Real.exp (Real.log (4*(N : ℝ)+1)) := Real.exp_le_exp.mpr hx
    _ = 4*(N : ℝ)+1 := Real.exp_log (by positivity)
    _ ≤ _ := by linarith

private theorem factorial_exp_abs_sub_le {N : ℕ} (hN : 1 ≤ N) {x y : ℝ}
    (hx : x ≤ Real.log (4*(N : ℝ)+1)) (hy : y ≤ Real.log (4*(N : ℝ)+1)) :
    |Real.exp x-Real.exp y| ≤ 5*(N : ℝ)*|x-y| := by
  exact (exp_abs_sub_le_of_le hx hy).trans
    (mul_le_mul_of_nonneg_right (factorial_exp_le hN le_rfl) (abs_nonneg _))

private theorem factorial_ramp_term_abs_sub_le {N K j : ℕ} (hN : 1 ≤ N)
    (hK : 1 ≤ K) (hj : j ≤ K) {x y : ℝ}
    (hx : x ≤ Real.log (4*(N : ℝ)+1)) (hy : y ≤ Real.log (4*(N : ℝ)+1)) :
    |clampedRamp (sourceFactorialCollar N) ((j : ℝ)*Real.exp x/K)-
      clampedRamp (sourceFactorialCollar N) ((j : ℝ)*Real.exp y/K)| ≤
        75*(N : ℝ)^2*|x-y| := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hjk : (j : ℝ)/K ≤ 1 := (div_le_iff₀ hk).2
    (by simpa only [one_mul] using (show (j : ℝ) ≤ K by exact_mod_cast hj))
  have hdiff : |(j : ℝ)*Real.exp x/K-(j : ℝ)*Real.exp y/K| ≤ 5*(N : ℝ)*|x-y| := by
    calc
      _ = ((j : ℝ)/K)*|Real.exp x-Real.exp y| := by
        rw [show (j : ℝ)*Real.exp x/K-(j : ℝ)*Real.exp y/K =
          ((j : ℝ)/K)*(Real.exp x-Real.exp y) by ring,
          abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ)/K)]
      _ ≤ 1*(5*(N : ℝ)*|x-y|) :=
        mul_le_mul hjk (factorial_exp_abs_sub_le hN hx hy) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  calc
    _ ≤ |(j : ℝ)*Real.exp x/K-(j : ℝ)*Real.exp y/K|/sourceFactorialCollar N :=
      clampedRamp_abs_sub_le (sourceFactorialCollar_pos hN) _ _
    _ ≤ (5*(N : ℝ)*|x-y|)/sourceFactorialCollar N :=
      div_le_div_of_nonneg_right hdiff (sourceFactorialCollar_pos hN).le
    _ = (5*(N : ℝ)*|x-y|)*(1/sourceFactorialCollar N) := by ring
    _ ≤ (5*(N : ℝ)*|x-y|)*(15*(N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sourceFactorialCollar_inv_le hN) (by positivity)
    _ = _ := by ring

private theorem smoothFactorialLift_interval_abs_sub_le {N K : ℕ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) {x y : ℝ}
    (hx : x ∈ Icc 0 (Real.log (4*(N : ℝ)+1)))
    (hy : y ∈ Icc 0 (Real.log (4*(N : ℝ)+1))) :
    |smoothFactorialLift (sourceFactorialCollar N) K x-
      smoothFactorialLift (sourceFactorialCollar N) K y| ≤ 380*(K : ℝ)*(N : ℝ)^3*|x-y| := by
  let S := fun t : ℝ => ∑ j ∈ Finset.Icc 1 K,
    clampedRamp (sourceFactorialCollar N) ((j : ℝ)*Real.exp t/K)
  have hS (t : ℝ) : |S t| ≤ K := by
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => clampedRamp_nonneg _ _))]
    calc
      S t ≤ ∑ _j ∈ Finset.Icc 1 K, (1 : ℝ) :=
        Finset.sum_le_sum (fun _ _ => clampedRamp_le_one _ _)
      _ = K := by simp
  have hSd : |S x-S y| ≤ (K : ℝ)*(75*(N : ℝ)^2*|x-y|) := by
    dsimp only [S]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 K,
        |clampedRamp (sourceFactorialCollar N) ((j : ℝ)*Real.exp x/K)-
          clampedRamp (sourceFactorialCollar N) ((j : ℝ)*Real.exp y/K)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.Icc 1 K, 75*(N : ℝ)^2*|x-y| := by
        apply Finset.sum_le_sum
        intro j hj
        exact factorial_ramp_term_abs_sub_le hN hK (Finset.mem_Icc.mp hj).2 hx.2 hy.2
      _ = _ := by simp
  have hhalf : |Real.exp (x/2)-Real.exp (y/2)| ≤ 5*(N : ℝ)*|x-y| := by
    have h := factorial_exp_abs_sub_le hN
      (show x/2 ≤ Real.log (4*(N : ℝ)+1) by linarith [hx.1,hx.2])
      (show y/2 ≤ Real.log (4*(N : ℝ)+1) by linarith [hy.1,hy.2])
    rw [show x/2-y/2 = (x-y)/2 by ring, abs_div, show |(2 : ℝ)| = 2 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (x-y)]) (by positivity))
  have hey : |Real.exp (y/2)| ≤ 5*(N : ℝ) := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact factorial_exp_le hN (by linarith [hy.1,hy.2])
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn3 : (N : ℝ) ≤ (N : ℝ)^3 := by nlinarith [sq_nonneg ((N : ℝ)-1)]
  change |Real.exp (x/2)*S x-Real.exp (y/2)*S y| ≤ _
  calc
    _ ≤ |Real.exp (x/2)-Real.exp (y/2)| * |S x|+|Real.exp (y/2)| * |S x-S y| :=
      abs_mul_sub_mul_le _ _ _ _
    _ ≤ (5*(N : ℝ)*|x-y|)*(K : ℝ)+(5*(N : ℝ))*((K : ℝ)*(75*(N : ℝ)^2*|x-y|)) :=
      add_le_add (mul_le_mul hhalf (hS x) (abs_nonneg _) (by positivity))
        (mul_le_mul hey hSd (abs_nonneg _) (by positivity))
    _ = 5*(K : ℝ)*(N : ℝ)*|x-y|+375*(K : ℝ)*(N : ℝ)^3*|x-y| := by ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hn3 (show 0 ≤ 5*(K : ℝ)*|x-y| by positivity)
      nlinarith

theorem sourceFactorialRamp_abs_sub_le {N : ℕ} (hN : 1 ≤ N) (x y : ℝ) :
    |sourceFactorialRamp N x-sourceFactorialRamp N y| ≤ 10000*(N : ℝ)^4*|x-y| := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log (4*(N : ℝ)+1) := Real.log_nonneg (by linarith)
  apply compact_interval_abs_sub_le hL (by positivity)
    (fun t ht => sourceFactorialRamp_zero_of_nonpos hN ht)
    (fun t ht => rampBiNull_tail (sourceFactorialCollar_pos hN) hN (sourceFactorialCollar_budget hN) ht)
  intro u hu v hv
  have h4 := smoothFactorialLift_interval_abs_sub_le hN (show 1 ≤ 4*N by omega) hu hv
  have h2 := smoothFactorialLift_interval_abs_sub_le hN (show 1 ≤ 2*N by omega) hu hv
  have h1 := smoothFactorialLift_interval_abs_sub_le hN hN hu hv
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h4 h2
  let A := smoothFactorialLift (sourceFactorialCollar N) (4*N) u-
    smoothFactorialLift (sourceFactorialCollar N) (4*N) v
  let B := smoothFactorialLift (sourceFactorialCollar N) (2*N) u-
    smoothFactorialLift (sourceFactorialCollar N) (2*N) v
  let C := smoothFactorialLift (sourceFactorialCollar N) N u-
    smoothFactorialLift (sourceFactorialCollar N) N v
  have heq : sourceFactorialRamp N u-sourceFactorialRamp N v = (A-4*B+4*C)/Real.sqrt N := by
    dsimp [A,B,C,sourceFactorialRamp,rampBiNull]
    ring
  have hnum : |A-4*B+4*C| ≤ 6080*(N : ℝ)^4*|u-v| := by
    have hh : |A-4*B+4*C| ≤ |A|+4*|B|+4*|C| := by
      calc
        _ ≤ |A-4*B|+|4*C| := abs_add_le _ _
        _ ≤ (|A|+|4*B|)+|4*C| := add_le_add
          (by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le A (-(4*B))) le_rfl
        _ = _ := by rw [abs_mul, abs_mul]; norm_num
    dsimp only [A,B,C] at hh
    nlinarith
  have hs : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hn
  have hsp : 0 < Real.sqrt (N : ℝ) := by positivity
  rw [heq, abs_div, abs_of_pos hsp]
  apply (div_le_iff₀ hsp).2
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 10000*(N : ℝ)^4*|u-v| by positivity)
  nlinarith [mul_nonneg (pow_nonneg (Nat.cast_nonneg N) 4) (abs_nonneg (u-v))]

theorem abs_sourceFactorialRamp_le_five {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    |sourceFactorialRamp N x| ≤ 5 := by
  by_cases h0 : x ≤ 0
  · rw [sourceFactorialRamp_zero_of_nonpos hN h0, abs_zero]
    norm_num
  by_cases hL : Real.log (4*(N : ℝ)+1) ≤ x
  · change |rampBiNull _ N x| ≤ 5
    rw [rampBiNull_tail (sourceFactorialCollar_pos hN) hN (sourceFactorialCollar_budget hN) hL, abs_zero]
    norm_num
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := rampBiNull_sq_le (sourceFactorialCollar_pos hN) hN x
  have he := factorial_exp_le hN (le_of_not_ge hL)
  have hq : (sourceFactorialRamp N x)^2 ≤ 20 := by
    exact hb.trans ((div_le_iff₀ hn).2 (by nlinarith))
  nlinarith [sq_abs (sourceFactorialRamp N x), abs_nonneg (sourceFactorialRamp N x)]

theorem integral_abs_sourceFactorialRamp_le {N : ℕ} (hN : 1 ≤ N) :
    (∫ x : ℝ, |sourceFactorialRamp N x|) ≤ 20*(N : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log (4*(N : ℝ)+1) := Real.log_nonneg (by linarith)
  have heq : (∫ x : ℝ, |sourceFactorialRamp N x|) =
      ∫ x in Icc 0 (Real.log (4*(N : ℝ)+1)), |sourceFactorialRamp N x| := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_cases h0 : x ≤ 0
    · rw [sourceFactorialRamp_zero_of_nonpos hN h0, abs_zero]
    · have ht : Real.log (4*(N : ℝ)+1) ≤ x := by
        by_contra! hh
        exact hx ⟨le_of_not_ge h0, hh.le⟩
      change |rampBiNull _ N x| = 0
      rw [rampBiNull_tail (sourceFactorialCollar_pos hN) hN (sourceFactorialCollar_budget hN) ht, abs_zero]
  rw [heq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
  calc
    _ ≤ ∫ _x in (0 : ℝ)..Real.log (4*(N : ℝ)+1), (5 : ℝ) :=
      intervalIntegral.integral_mono_on hL
        ((continuous_sourceFactorialRamp N).abs.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun x _ => abs_sourceFactorialRamp_le_five hN x)
    _ = 5*Real.log (4*(N : ℝ)+1) := by rw [intervalIntegral.integral_const]; simp; ring
    _ ≤ 20*(N : ℝ) := by
      have hh := Real.log_le_sub_one_of_pos (show 0 < 4*(N : ℝ)+1 by positivity)
      linarith

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
