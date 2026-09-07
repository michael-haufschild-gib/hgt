import GaloisForLFunctions.RHTower.ThetaCuspAllOrderLikelihoodCooling
import GaloisForLFunctions.RHTower.ThetaCuspSchwartz

/-!
# All-order first-atom approximation of the literal theta source

Every fixed derivative of the complete source agrees with the first atom up to
a relative error smaller than any fixed power of the source scale. The entire
higher source is retained by the exact likelihood factorization.
-/

open Filter Topology Set Polynomial
open scoped ContDiff
namespace RHTower
noncomputable section

private theorem contDiff_firstAtom : ContDiff ℝ ∞ (fun x : ℝ => thetaCuspSourceTerm x 1) := by
  rw [thetaCuspSourceTerm_eq_polynomialAtom]
  unfold thetaCuspPolynomialAtom
  simp only [thetaCuspSeedPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  fun_prop

private theorem scale_eq_pi_exp_sq (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 x = Real.pi * Real.exp x^2 := by
  unfold thetaCuspSingleAtomReflectionScale
  norm_num only [Nat.cast_one, one_pow, mul_one]
  rw [show Real.exp (2*x) = Real.exp x^2 by rw [pow_two, ← Real.exp_add]; congr 1; ring]

private theorem firstSeed_one_le {x : ℝ} (hx : 0 < x) :
    1 ≤ Polynomial.eval (Real.exp x) thetaCuspSeedPolynomial := by
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  rw [scale_eq_pi_exp_sq] at hq
  simp only [thetaCuspSeedPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  nlinarith [sq_nonneg (Real.pi*Real.exp x^2-3)]

/-- Every first-atom derivative has a fixed polynomial relative bound. -/
theorem abs_firstAtom_derivative_ratio_le (m : ℕ) {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv m (fun y : ℝ => thetaCuspSourceTerm y 1) x / thetaCuspSourceTerm x 1| ≤
      thetaCuspCoeffMass (thetaCuspLogDerivativePolynomial m) *
        thetaCuspSingleAtomReflectionScale 1 x^(thetaCuspLogDerivativePolynomial m).natDegree := by
  have hseed := firstSeed_one_le hx
  have hseedpos : 0 < Polynomial.eval (Real.exp x) thetaCuspSeedPolynomial := by linarith
  have he : 1 ≤ Real.exp x := Real.one_le_exp hx.le
  have hq : Real.exp x ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    rw [scale_eq_pi_exp_sq]
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.exp x-1)]
  have hq0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := (Real.exp_pos x).le.trans hq
  have heval := (abs_eval_le_coeffMass_mul_pow (thetaCuspLogDerivativePolynomial m) he).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.exp_pos x).le hq _)
      (thetaCuspCoeffMass_nonneg _))
  have hratio : iteratedDeriv m (fun y : ℝ => thetaCuspSourceTerm y 1) x /
      thetaCuspSourceTerm x 1 =
      Polynomial.eval (Real.exp x) (thetaCuspLogDerivativePolynomial m) /
        Polynomial.eval (Real.exp x) thetaCuspSeedPolynomial := by
    rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom,
      show thetaCuspSourceTerm x 1 = thetaCuspPolynomialAtom thetaCuspSeedPolynomial 1 x from
        congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1) x]
    unfold thetaCuspPolynomialAtom
    simp only [Nat.cast_one, one_mul]
    field_simp [Real.exp_ne_zero, hseedpos.ne']
  rw [hratio, abs_div, abs_of_pos hseedpos]
  apply (div_le_iff₀ hseedpos).mpr
  exact heval.trans (le_mul_of_one_le_right
    (mul_nonneg (thetaCuspCoeffMass_nonneg _) (pow_nonneg hq0 _)) hseed)

/-- The actual likelihood remainder is smooth wherever the first source atom is positive. -/
theorem contDiffAt_thetaCuspLikelihoodSourceRemainder {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ thetaCuspLikelihoodSourceRemainder x := by
  have he : thetaCuspLikelihoodSourceRemainder =ᶠ[𝓝 x]
      (fun y : ℝ => thetaCuspFullSource y / thetaCuspSourceTerm y 1 - 1) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    unfold thetaCuspLikelihoodSourceRemainder
    rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition
      (thetaCuspLikelihoodCoordinate_pos hy.le)]
    rw [mul_div_cancel_left₀ _ (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hy (by norm_num)).ne']
  exact (((contDiff_thetaCuspFullSource.contDiffAt).div contDiff_firstAtom.contDiffAt
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne').sub contDiffAt_const).congr_of_eventuallyEq he

/-- Exact derivative decomposition of the complete source's higher-atom error. -/
theorem thetaCuspFullSource_derivative_sub_first_eq (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n thetaCuspFullSource x -
      iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x =
    ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
      iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x *
        iteratedDeriv (n-i) thetaCuspLikelihoodSourceRemainder x := by
  have he : (fun y : ℝ => thetaCuspFullSource y - thetaCuspSourceTerm y 1) =ᶠ[𝓝 x]
      (fun y : ℝ => thetaCuspSourceTerm y 1 * thetaCuspLikelihoodSourceRemainder y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition (thetaCuspLikelihoodCoordinate_pos hy.le)]
    unfold thetaCuspLikelihoodSourceRemainder
    ring
  rw [← iteratedDeriv_fun_sub (contDiff_thetaCuspFullSource.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
    (contDiff_firstAtom.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))), he.iteratedDeriv_eq,
    iteratedDeriv_fun_mul (contDiff_firstAtom.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
      ((contDiffAt_thetaCuspLikelihoodSourceRemainder hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))]

private theorem derivative_ratio_mul_remainder_scaled_tendsto_zero (k i j : ℕ) :
    Tendsto (fun x : ℝ => thetaCuspSingleAtomReflectionScale 1 x^k *
      (iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x / thetaCuspSourceTerm x 1) *
        iteratedDeriv j thetaCuspLikelihoodSourceRemainder x) atTop (𝓝 0) := by
  let d := (thetaCuspLogDerivativePolynomial i).natDegree
  let C := thetaCuspCoeffMass (thetaCuspLogDerivativePolynomial i)
  have hlim := (iteratedDeriv_thetaCuspLikelihoodSourceRemainder_scaled_tendsto_zero (k+d) j).abs.const_mul C
  have habs : Tendsto (fun x : ℝ => |thetaCuspSingleAtomReflectionScale 1 x^k *
      (iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x / thetaCuspSourceTerm x 1) *
        iteratedDeriv j thetaCuspLikelihoodSourceRemainder x|) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun x => abs_nonneg _) ?_
      (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using hlim)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hq : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
      have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
      linarith
    have hb := abs_firstAtom_derivative_ratio_le i hx
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (pow_nonneg hq k))
      (abs_nonneg (iteratedDeriv j thetaCuspLikelihoodSourceRemainder x))
    simpa only [abs_mul, abs_pow, abs_of_nonneg hq, pow_add, mul_assoc, mul_left_comm,
      mul_comm, d, C] using hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using habs.neg) habs
    (Filter.Eventually.of_forall fun x => neg_abs_le _) (Filter.Eventually.of_forall fun x => le_abs_self _)

/-- Every actual source derivative agrees with the first atom up to a relative error smaller
than any fixed power of the source scale. -/
theorem thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero (k n : ℕ) :
    Tendsto (fun x : ℝ => thetaCuspSingleAtomReflectionScale 1 x^k *
      ((iteratedDeriv n thetaCuspFullSource x -
        iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x) / thetaCuspSourceTerm x 1))
      atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum (Finset.range (n+1)) (fun i _ =>
    (derivative_ratio_mul_remainder_scaled_tendsto_zero k i (n-i)).const_mul (n.choose i : ℝ))
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using hsum).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [thetaCuspFullSource_derivative_sub_first_eq n hx, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end RHTower
