import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomAllOrderApproximation
import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomReflectionJets

/-!
# All-order native reflection approximation by the first atom

The complete native reflection jets differ from their first-atom jets by a
relative error decaying after every fixed scale power. This is an exact
infinite-source tail theorem, with no finite truncation premise.
-/

open Filter Topology Set
namespace RHTower
noncomputable section

private theorem firstRatio_mul_flat
    (g : ℝ → ℝ)
    (hg : ∀ k : ℕ, Tendsto (fun x => thetaCuspSingleAtomReflectionScale 1 x^k*g x) atTop (𝓝 0))
    (k i : ℕ) :
    Tendsto (fun x => thetaCuspSingleAtomReflectionScale 1 x^k *
      (iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x / thetaCuspSourceTerm x 1) * g x)
      atTop (𝓝 0) := by
  let d := (thetaCuspLogDerivativePolynomial i).natDegree
  let C := thetaCuspCoeffMass (thetaCuspLogDerivativePolynomial i)
  have hlim := (hg (k+d)).abs.const_mul C
  have habs : Tendsto (fun x => |thetaCuspSingleAtomReflectionScale 1 x^k *
      (iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x / thetaCuspSourceTerm x 1) * g x|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun x => abs_nonneg _) ?_
      (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using hlim)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hq : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
      have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
      linarith
    have hb := abs_firstAtom_derivative_ratio_le i hx
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (pow_nonneg hq k))
      (abs_nonneg (g x))
    simpa only [abs_mul, abs_pow, abs_of_nonneg hq, pow_add, mul_assoc, mul_left_comm,
      mul_comm, d, C] using hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using habs.neg) habs
    (Filter.Eventually.of_forall fun x => neg_abs_le _) (Filter.Eventually.of_forall fun x => le_abs_self _)

private def sourceDerivativeRelativeError (n : ℕ) (x : ℝ) : ℝ :=
  (iteratedDeriv n thetaCuspFullSource x -
    iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x) / thetaCuspSourceTerm x 1

private theorem sourceDerivativeProduct_error_scaled_tendsto_zero (k i j : ℕ) :
    Tendsto (fun x : ℝ => thetaCuspSingleAtomReflectionScale 1 x^k *
      ((iteratedDeriv i thetaCuspFullSource x*iteratedDeriv j thetaCuspFullSource x -
        iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x *
          iteratedDeriv j (fun y : ℝ => thetaCuspSourceTerm y 1) x) / thetaCuspSourceTerm x 1^2))
      atTop (𝓝 0) := by
  have he (n k : ℕ) : Tendsto (fun x => thetaCuspSingleAtomReflectionScale 1 x^k *
      sourceDerivativeRelativeError n x) atTop (𝓝 0) :=
    thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero k n
  have hi := firstRatio_mul_flat (sourceDerivativeRelativeError i) (he i) k j
  have hj := firstRatio_mul_flat (sourceDerivativeRelativeError j) (he j) k i
  have he0 : Tendsto (sourceDerivativeRelativeError j) atTop (𝓝 0) := by simpa using he j 0
  have hprod := (he i k).mul he0
  have h := (hi.add hj).add hprod
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))).ne'
  unfold sourceDerivativeRelativeError
  field_simp [hf]
  ring

/-- At every fixed derivative order, the entire higher-source correction to the native reflection
jet is smaller than any fixed inverse power of the scale, relative to first-atom mass squared. -/
theorem thetaCuspNativeReflectionJet_firstAtom_error_scaled_tendsto_zero (k n : ℕ) :
    Tendsto (fun x : ℝ => thetaCuspSingleAtomReflectionScale 1 x^k *
      ((thetaCuspNativeReflectionJet n x - thetaCuspFirstAtomReflectionJet n x) /
        thetaCuspSourceTerm x 1^2)) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum (Finset.range (n+1)) (fun i _ =>
    (sourceDerivativeProduct_error_scaled_tendsto_zero k i (n-i)).const_mul
      ((n.choose i : ℝ)*(-1)^(n-i)))
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using hsum).congr'
  filter_upwards with x
  rw [thetaCuspNativeReflectionJet_eq, thetaCuspFirstAtomReflectionJet_eq,
    ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end RHTower
