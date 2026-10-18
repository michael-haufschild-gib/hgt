import GaloisForLFunctions.BiScaleUncertainty.IntegerAffineShear

/-!
# All-scale integer affine shear and exact coefficient readouts

An actual l1 coefficient vector constructs a norm-convergent operator series.
Two cofinal coordinates recover each signed coefficient exactly; neither
readout requires truncation of the remaining scales.
-/

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty.IntegerAffineShear
set_option autoImplicit false

abbrev Weights := lp (fun _ : ℕ => ℝ) 1

private theorem coefficient_norm_hasSum (a : Weights) :
    HasSum (fun d => ‖a d‖) ‖a‖ := by
  simpa using lp.hasSum_norm (p := 1) (by norm_num) a

private theorem term_norm_le (a : Weights) (d : ℕ) :
    ‖a d • shear d‖ ≤ ‖a d‖*2 := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_shear_le d) (norm_nonneg _)

theorem summable_shear (a : Weights) : Summable (fun d => a d • shear d) :=
  ((coefficient_norm_hasSum a).mul_right 2).summable.of_norm_bounded (term_norm_le a)

/-- The complete, operator-norm convergent combination of all integer dilation shears. -/
def series (a : Weights) : State →L[ℝ] State := ∑' d, a d • shear d

theorem norm_series_le (a : Weights) : ‖series a‖ ≤ 2*‖a‖ := by
  have h := tsum_of_norm_bounded ((coefficient_norm_hasSum a).mul_right 2) (term_norm_le a)
  simpa only [series, mul_comm] using h

theorem series_zero : series 0 = 0 := by
  simp [series]

theorem series_sub (a b : Weights) : series (a-b) = series a - series b := by
  simp only [series, lp.coeFn_sub, Pi.sub_apply, sub_smul]
  exact (summable_shear a).tsum_sub (summable_shear b)

private theorem series_coordinate (a : Weights) (n k : ℕ) :
    series a (lp.single 2 n (1 : ℝ)) k =
      ∑' d, a d * shear d (lp.single 2 n (1 : ℝ)) k := by
  let E : (State →L[ℝ] State) →L[ℝ] ℝ :=
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k).comp
      (ContinuousLinearMap.apply ℝ State (lp.single 2 n (1 : ℝ)))
  exact E.map_tsum (summable_shear a)

/-- Every cofinal positive endpoint reads its own coefficient from the full infinite series. -/
theorem series_single_plus (a : Weights) (d n : ℕ) (hn : d+2 ≤ n) :
    series a (lp.single 2 n (1 : ℝ)) ((d+2)*n+1) = a d := by
  rw [series_coordinate]
  simp_rw [shear_single_plus d _ n hn, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq d (fun e => a e)

/-- The negative endpoint supplies the opposite signed coefficient, without a tail error. -/
theorem series_single_minus (a : Weights) (d n : ℕ) (hn : d+2 ≤ n) :
    series a (lp.single 2 n (1 : ℝ)) ((d+2)*(n+1)) = -a d := by
  rw [series_coordinate]
  simp_rw [shear_single_minus d _ n hn, mul_ite, mul_neg_one, mul_zero]
  exact tsum_ite_eq d (fun e => -a e)

end GaloisForLFunctions.BiScaleUncertainty.IntegerAffineShear
