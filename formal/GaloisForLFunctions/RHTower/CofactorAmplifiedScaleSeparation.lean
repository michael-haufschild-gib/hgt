import GaloisForLFunctions.RHTower.MobiusSparseForbiddenDeletion

/-!
# Scale separation in the cofactor-amplified E3 construction

For cofactor cutoff `T=U^(2η)`, the smallest large-prime scale in the card is

`sqrt ((U/T) / (log U)^a)`.

This module proves the exact quotient identity and its divergence when `η<1/6`.  Consequently any
fixed positive proportion of that large-prime scale eventually exceeds `T`.  This is the
unconditional asymptotic fact used to separate both large E3 prime factors from every cofactor
prime, hence to make the support coprime and decodable.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The card's cofactor cutoff `T=U^(2η)`. -/
def cofactorAmplifiedCutoff (η U : ℝ) : ℝ := U ^ (2 * η)

/-- Worst-case large-prime scale after taking `t≤T` and a logarithmic small-prime factor. -/
def cofactorAmplifiedLargePrimeScale (a η U : ℝ) : ℝ :=
  Real.sqrt (U / cofactorAmplifiedCutoff η U / (Real.log U) ^ a)

private theorem tendsto_rpow_div_log_rpow_atTop (b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => x ^ δ / (Real.log x) ^ b) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ b / x ^ δ)
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_log_rpow_div_rpow b hδ) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hx) b)
      (Real.rpow_pos_of_pos (by linarith) δ)
  have hinv := tendsto_inv_nhdsGT_zero.comp h0
  refine hinv.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [inv_div]

/-- Exact exponent calculation: the scale ratio has power gap `1/2-3η`. -/
theorem cofactorAmplifiedLargePrimeScale_div_cutoff_eq
    (a η U : ℝ) (hU : 1 < U) :
    cofactorAmplifiedLargePrimeScale a η U / cofactorAmplifiedCutoff η U =
      U ^ ((1 : ℝ) / 2 - 3 * η) / (Real.log U) ^ (a / 2) := by
  have hU0 : 0 < U := by linarith
  have hlog : 0 < Real.log U := Real.log_pos hU
  rw [cofactorAmplifiedLargePrimeScale, cofactorAmplifiedCutoff, Real.sqrt_eq_rpow]
  rw [Real.div_rpow (by positivity)
    (Real.rpow_nonneg hlog.le a)]
  rw [Real.div_rpow hU0.le (Real.rpow_nonneg hU0.le (2 * η))]
  rw [← Real.rpow_mul hU0.le]
  rw [← Real.rpow_mul hlog.le]
  ring_nf
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hU0 η),
    ne_of_gt (Real.rpow_pos_of_pos hU0 (2 * η)),
    ne_of_gt (Real.rpow_pos_of_pos hlog (a / 2))]
  rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]
  congr 1
  ring

/-- The large-prime scale dominates the cofactor cutoff exactly below `η=1/6`. -/
theorem tendsto_cofactorAmplifiedLargePrimeScale_div_cutoff
    {a η : ℝ} (hη : η < (1 : ℝ) / 6) :
    Tendsto (fun U : ℝ =>
      cofactorAmplifiedLargePrimeScale a η U / cofactorAmplifiedCutoff η U)
      atTop atTop := by
  have hδ : 0 < (1 : ℝ) / 2 - 3 * η := by linarith
  have hlim := tendsto_rpow_div_log_rpow_atTop (a / 2) hδ
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with U hU
  exact (cofactorAmplifiedLargePrimeScale_div_cutoff_eq a η U hU).symm

/-- Any fixed positive asymptotic lower-bound constant still leaves large primes above `T`. -/
theorem eventually_cofactorAmplifiedCutoff_lt_const_mul_largePrimeScale
    {a η c : ℝ} (hη : η < (1 : ℝ) / 6) (hc : 0 < c) :
    ∀ᶠ U : ℝ in atTop,
      cofactorAmplifiedCutoff η U < c * cofactorAmplifiedLargePrimeScale a η U := by
  have hlim := (tendsto_cofactorAmplifiedLargePrimeScale_div_cutoff (a := a) hη).const_mul_atTop hc
  filter_upwards [hlim.eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with U hratio hU
  have hcutoff : 0 < cofactorAmplifiedCutoff η U :=
    Real.rpow_pos_of_pos (by linarith) (2 * η)
  have hscaled : 1 < c *
      (cofactorAmplifiedLargePrimeScale a η U / cofactorAmplifiedCutoff η U) := by
    linarith
  have hdiv : 1 < (c * cofactorAmplifiedLargePrimeScale a η U) /
      cofactorAmplifiedCutoff η U := by
    simpa only [mul_div_assoc] using hscaled
  have := (lt_div_iff₀ hcutoff).mp hdiv
  simpa only [one_mul] using this

end

end RHTower
