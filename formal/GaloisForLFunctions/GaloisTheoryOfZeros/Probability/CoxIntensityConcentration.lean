import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.GammaCoxDetection

/-!
# Concentration of the Gamma-driven intensity

Exponential Markov bounds upgrade the Laplace formulas to statements about the
random intensity itself: mass escapes every bounded interval at a true zero,
and tends to zero in probability at every nonzero residual.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
namespace GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
noncomputable section

/-- Gamma laws are supported on nonnegative intensities. -/
theorem ae_nonneg_gamma (a b : ℝ) : ∀ᵐ x ∂gammaMeasure a b, 0 ≤ x := by
  apply (ae_withDensity_iff
    (show Measurable (gammaPDF a b) from (measurable_gammaPDFReal a b).ennreal_ofReal)).mpr
  exact Eventually.of_forall fun x hx => le_of_not_gt fun h => hx (gammaPDF_of_neg h)

/-- Nonnegative Laplace parameters give bounded integrable exponentials. -/
theorem integrable_exp_neg_gamma (a b u : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u) :
    Integrable (fun x => Real.exp (-(u * x))) (gammaMeasure a b) := by
  letI := isProbabilityMeasure_gammaMeasure ha hb
  apply (integrable_const (1 : ℝ)).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable)
  filter_upwards [ae_nonneg_gamma a b] with x hx
  change ‖Real.exp (-(u * x))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hu hx))

/-- The Laplace transform bounds the probability that growing Gamma mass stays bounded. -/
theorem gamma_lower_tail_le (K R : ℝ) (hK : 0 < K) :
    (gammaMeasure K 1).real {x | x ≤ R} ≤
      Real.exp R * (1 - detection K 0) := by
  letI := isProbabilityMeasure_gammaMeasure hK zero_lt_one
  have hint := integrable_exp_neg_gamma K 1 1 hK zero_lt_one zero_le_one
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun x => (Real.exp_pos (-(1 * x))).le) hint (Real.exp (-R))
  have hi : (∫ x, Real.exp (-x) ∂gammaMeasure K 1) = 1 - detection K 0 := by
    rw [detection_eq_gamma_integral K 0 hK]
    simp [weight]
  simp only [one_mul, Real.exp_le_exp, neg_le_neg_iff] at hm
  rw [hi] at hm
  have hh := mul_le_mul_of_nonneg_left hm (Real.exp_pos R).le
  have he : Real.exp R * Real.exp (-R) = 1 := by rw [← Real.exp_add]; simp
  simpa only [← mul_assoc, he, one_mul] using hh

/-- Detection probability controls the upper tail of the underlying random intensity. -/
theorem gamma_upper_tail_le (K r ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    (gammaMeasure K 1).real {x | ε ≤ weight K r * x} ≤
      detection K r / (1 - Real.exp (-ε)) := by
  letI := isProbabilityMeasure_gammaMeasure hK zero_lt_one
  have hw : 0 < weight K r := Real.exp_pos _
  have hint := integrable_exp_neg_gamma K 1 (weight K r) hK zero_lt_one hw.le
  have hn : 0 ≤ᵐ[gammaMeasure K 1] fun x => 1 - Real.exp (-(weight K r * x)) := by
    filter_upwards [ae_nonneg_gamma K 1] with x hx
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hw.le hx)))
  have hm := mul_meas_ge_le_integral_of_nonneg hn
    ((integrable_const (1 : ℝ)).sub hint) (1 - Real.exp (-ε))
  have he : {x : ℝ | 1 - Real.exp (-ε) ≤ 1 - Real.exp (-(weight K r * x))} =
      {x | ε ≤ weight K r * x} := by
    ext x
    simp only [mem_setOf_eq, sub_le_sub_iff_left, Real.exp_le_exp, neg_le_neg_iff]
  rw [he, integral_sub (integrable_const _) hint] at hm
  have hi : (∫ _ : ℝ, (1 : ℝ) ∂gammaMeasure K 1) = 1 := by simp
  rw [hi, ← detection_eq_gamma_integral K r hK] at hm
  have hden : 0 < 1 - Real.exp (-ε) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hε))
  exact (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hm)

/-- Growing Gamma mass escapes every fixed bounded-above interval. -/
theorem tendsto_gamma_lower_tail (R : ℝ) :
    Tendsto (fun K => (gammaMeasure K 1).real {x | x ≤ R}) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg)
    ((eventually_gt_atTop (0 : ℝ)).mono fun K hK => gamma_lower_tail_le K R hK) ?_
  simpa only [ite_true, sub_self, mul_zero] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_detection 0)).const_mul (Real.exp R)

/-- Damping at a nonzero residual sends the actual random intensity to zero in probability. -/
theorem tendsto_gamma_upper_tail (r ε : ℝ) (hr : r ≠ 0) (hε : 0 < ε) :
    Tendsto (fun K => (gammaMeasure K 1).real {x | ε ≤ weight K r * x})
      atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg)
    ((eventually_gt_atTop (0 : ℝ)).mono fun K hK => gamma_upper_tail_le K r ε hK hε) ?_
  simpa only [if_neg hr, zero_div] using
    (tendsto_detection r).div_const (1 - Real.exp (-ε))

/-- Every positive threshold separates vanishing and escaping intensities in probability. -/
theorem tendsto_intensity_classification_error (r s : ℝ) :
    Tendsto (fun K => (gammaMeasure K 1).real
      {x | if r = 0 then weight K r * x ≤ Real.exp s else Real.exp s ≤ weight K r * x})
      atTop (𝓝 0) := by
  by_cases hr : r = 0
  · subst r
    simpa [weight] using tendsto_gamma_lower_tail (Real.exp s)
  · simpa only [if_neg hr] using
      tendsto_gamma_upper_tail r (Real.exp s) hr (Real.exp_pos s)

end
end GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.ae_nonneg_gamma
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.integrable_exp_neg_gamma
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.gamma_lower_tail_le
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.gamma_upper_tail_le
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_gamma_lower_tail
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_gamma_upper_tail
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_intensity_classification_error

