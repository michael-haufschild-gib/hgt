import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# A uniform logarithmic moment for Gauss digit perturbations

Normalized denominator ratios lie in `[0,1]`. Their digit probabilities are
bounded by `2/(i+1)^2`. For exponents at most one half, the weighted increment
has a common summable envelope `16 log(i+2)/(i+2)^(3/2)`.
The envelope supplies a positive absolute constant for weighted finite-digit
contraction, with no dependence on the parent word or cutoff.
-/

open Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDigitPerturbation
noncomputable section

/-- The ratio of the penultimate denominator to the final denominator. -/
abbrev Ratio := Set.Icc (0 : ℝ) 1

/-- Conditional mass of the next continued-fraction digit `i+1`. -/
def weight (r : Ratio) (i : ℕ) : ℝ :=
  (1 + r.val) / (((i : ℝ) + 1 + r.val) * ((i : ℝ) + 2 + r.val))

/-- A common summable bound for the derivative of the weighted digit mass. -/
def envelope (i : ℕ) : ℝ :=
  16 * Real.log ((i : ℝ) + 2) * ((i : ℝ) + 2) ^ (-(3 / 2 : ℝ))

theorem envelope_nonneg (i : ℕ) : 0 ≤ envelope i := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hl : 0 ≤ Real.log ((i : ℝ) + 2) := Real.log_nonneg (by linarith only [hi])
  unfold envelope
  positivity

/-- The existing logarithmic Dirichlet-moment theorem controls the entire digit alphabet. -/
theorem envelope_summable : Summable envelope := by
  have h := RHTower.summable_abs_log_natCast_pow_mul_rpow_neg 1 (3 / 2) (by norm_num)
  have hbase : Summable (fun j : ℕ => Real.log j * (j : ℝ) ^ (-(3 / 2 : ℝ))) := by
    simpa only [pow_one, abs_of_nonneg (Real.log_natCast_nonneg _)] using h
  have hshift := (summable_nat_add_iff 2).mpr hbase
  exact (hshift.mul_left (16 : ℝ)).congr (fun i => by
    simp only [envelope, Nat.cast_add, Nat.cast_ofNat]
    ring)

/-- Total logarithmic perturbation envelope. -/
def moment : ℝ := ∑' i : ℕ, envelope i

theorem moment_nonneg : 0 ≤ moment := tsum_nonneg envelope_nonneg

/-- A positive absolute exponent scale, chosen from the actual convergent envelope. -/
def beta : ℝ := 1 / (4 * (moment + 1))

/-- The cutoff-dependent exponent in the cylinder estimate. -/
def eta (n : ℕ) : ℝ := beta / ((n : ℝ) + 1)

/-- The retained fraction in the weighted cylinder contraction. -/
def cutoffRate (n : ℕ) : ℝ := (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)

theorem beta_pos : 0 < beta := by
  have h := moment_nonneg
  unfold beta
  positivity

theorem beta_le_quarter : beta ≤ 1 / 4 := by
  have h := moment_nonneg
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith only [h])

theorem moment_mul_beta_le_quarter : moment * beta ≤ 1 / 4 := by
  have hc := moment_nonneg
  have hd : 0 < 4 * (moment + 1) := by positivity
  rw [beta, mul_one_div]
  apply (div_le_iff₀ hd).mpr
  nlinarith only [hc]

theorem eta_pos (n : ℕ) : 0 < eta n := div_pos beta_pos (by positivity)

theorem eta_le_quarter (n : ℕ) : eta n ≤ 1 / 4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact (div_le_self beta_pos.le (by linarith only [hn])).trans beta_le_quarter

theorem cutoffRate_bounds (n : ℕ) : 0 < cutoffRate n ∧ cutoffRate n < 1 := by
  constructor
  · unfold cutoffRate
    positivity
  · rw [cutoffRate, div_lt_one (by positivity : 0 < 2 * (n : ℝ) + 2)]
    linarith

/-- The unweighted loss absorbs the full logarithmic correction. -/
theorem retained_plus_correction_le (n : ℕ) :
    (n : ℝ) / ((n : ℝ) + 1) + eta n * moment ≤ cutoffRate n := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he : eta n * moment = (moment * beta) / ((n : ℝ) + 1) := by
    unfold eta
    ring
  have hc : eta n * moment ≤ (1 / 4 : ℝ) / ((n : ℝ) + 1) := by
    rw [he]
    exact div_le_div_of_nonneg_right moment_mul_beta_le_quarter hn.le
  calc
    _ ≤ (n : ℝ) / ((n : ℝ) + 1) + (1 / 4 : ℝ) / ((n : ℝ) + 1) := add_le_add le_rfl hc
    _ = ((n : ℝ) + 1 / 4) / ((n : ℝ) + 1) := (add_div _ _ _).symm
    _ ≤ cutoffRate n := by
      apply (div_le_div_iff₀ hn (by positivity : 0 < 2 * (n : ℝ) + 2)).mpr
      nlinarith only [hn0]

private theorem exp_sub_one_le (u : ℝ) : Real.exp u - 1 ≤ u * Real.exp u := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
  have he : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [he] at h
  nlinarith only [h]

private theorem rpow_increment_le (b : ℝ) (hb : 1 ≤ b) (n : ℕ) :
    b ^ (2 * eta n) - 1 ≤ 2 * eta n * Real.log b * b ^ (1 / 2 : ℝ) := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have heta := eta_pos n
  have hl : 0 ≤ Real.log b := Real.log_nonneg hb
  have he : 2 * eta n ≤ (1 / 2 : ℝ) := by linarith only [eta_le_quarter n]
  have hp : b ^ (2 * eta n) ≤ b ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hb he
  have hi : b ^ (2 * eta n) - 1 ≤ 2 * eta n * Real.log b * b ^ (2 * eta n) := by
    have h := exp_sub_one_le (Real.log b * (2 * eta n))
    rw [Real.rpow_def_of_pos hb0]
    nlinarith only [h]
  exact hi.trans (mul_le_mul_of_nonneg_left hp (by positivity))

private theorem increment_nonneg (b : ℝ) (hb : 1 ≤ b) (n : ℕ) :
    0 ≤ b ^ (2 * eta n) - 1 := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have heta := eta_pos n
  have hl : 0 ≤ Real.log b := Real.log_nonneg hb
  rw [Real.rpow_def_of_pos hb0]
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hl (by positivity)))

private theorem weight_le (r : Ratio) (i : ℕ) : weight r i ≤ 2 / ((i : ℝ) + 1) ^ 2 := by
  have hi : 0 < (i : ℝ) + 1 := by positivity
  have h0 := r.property.1
  have h1 := r.property.2
  have hd : 0 < ((i : ℝ) + 1 + r.val) * ((i : ℝ) + 2 + r.val) := by positivity
  have hb : ((i : ℝ) + 1) ^ 2 ≤ ((i : ℝ) + 1 + r.val) * ((i : ℝ) + 2 + r.val) := by
    rw [pow_two]
    apply mul_le_mul (by linarith only [h0]) (by linarith only [h0]) hi.le
    positivity
  calc
    weight r i ≤ 2 / (((i : ℝ) + 1 + r.val) * ((i : ℝ) + 2 + r.val)) :=
      div_le_div_of_nonneg_right (by linarith only [h1]) hd.le
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hi) hb

private theorem half_power_ratio_le (i : ℕ) :
    ((i : ℝ) + 2) ^ (1 / 2 : ℝ) / ((i : ℝ) + 1) ^ 2 ≤
      4 * ((i : ℝ) + 2) ^ (-(3 / 2 : ℝ)) := by
  have hi : 0 < (i : ℝ) + 1 := by positivity
  have hb : 0 < (i : ℝ) + 2 := by positivity
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hq : ((i : ℝ) + 2) ^ 2 / ((i : ℝ) + 1) ^ 2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hi)).mpr
    nlinarith only [hi0, sq_nonneg (i : ℝ)]
  have he : ((i : ℝ) + 2) ^ (1 / 2 : ℝ) =
      ((i : ℝ) + 2) ^ 2 * ((i : ℝ) + 2) ^ (-(3 / 2 : ℝ)) := by
    calc
      _ = ((i : ℝ) + 2) ^ ((2 : ℝ) + -(3 / 2 : ℝ)) :=
        congrArg (fun t : ℝ => ((i : ℝ) + 2) ^ t) (by norm_num)
      _ = ((i : ℝ) + 2) ^ (2 : ℝ) * ((i : ℝ) + 2) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_add hb 2 (-(3 / 2 : ℝ))
      _ = _ := congrArg (fun t : ℝ => t * ((i : ℝ) + 2) ^ (-(3 / 2 : ℝ)))
        (Real.rpow_two _)
  rw [he, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hb.le _)

/-- Every weighted digit increment has the same summable bound, uniformly in the denominator ratio. -/
theorem digit_correction_le (r : Ratio) (n i : ℕ) :
    weight r i * (((i : ℝ) + 2) ^ (2 * eta n) - 1) ≤ eta n * envelope i := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hb : (1 : ℝ) ≤ (i : ℝ) + 2 := by linarith only [hi]
  have heta := eta_pos n
  have hl : 0 ≤ Real.log ((i : ℝ) + 2) := Real.log_nonneg hb
  calc
    _ ≤ (2 / ((i : ℝ) + 1) ^ 2) *
        (2 * eta n * Real.log ((i : ℝ) + 2) * ((i : ℝ) + 2) ^ (1 / 2 : ℝ)) :=
      mul_le_mul (weight_le r i) (rpow_increment_le _ hb n)
        (increment_nonneg _ hb n) (by positivity)
    _ = (4 * eta n * Real.log ((i : ℝ) + 2)) *
        (((i : ℝ) + 2) ^ (1 / 2 : ℝ) / ((i : ℝ) + 1) ^ 2) := by ring
    _ ≤ (4 * eta n * Real.log ((i : ℝ) + 2)) *
        (4 * ((i : ℝ) + 2) ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (half_power_ratio_le i) (by positivity)
    _ = eta n * envelope i := by unfold envelope; ring

/-- The entire finite digit correction is controlled by one absolute logarithmic moment. -/
theorem finite_correction_le (r : Ratio) (n : ℕ) :
    (∑ i : Fin n, weight r i * (((i : ℝ) + 2) ^ (2 * eta n) - 1)) ≤ eta n * moment := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => weight r i * (((i : ℝ) + 2) ^ (2 * eta n) - 1)) n]
  calc
    _ ≤ ∑ i ∈ Finset.range n, eta n * envelope i :=
      Finset.sum_le_sum (fun i _ => digit_correction_le r n i)
    _ = eta n * ∑ i ∈ Finset.range n, envelope i := (Finset.mul_sum _ _ _).symm
    _ ≤ eta n * moment := mul_le_mul_of_nonneg_left
      (envelope_summable.sum_le_tsum (Finset.range n) (fun i _ => envelope_nonneg i)) (eta_pos n).le

#print axioms envelope_summable
#print axioms beta_pos
#print axioms retained_plus_correction_le
#print axioms digit_correction_le
#print axioms finite_correction_le

end
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDigitPerturbation
