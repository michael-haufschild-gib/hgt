import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Detection

/-! # The packet width ratio that saturates the thermal contrast -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets

open Real Filter Topology

/-- Ratio of relative packet widths required for extremal limiting discrimination. -/
def optimal (D β γ : ℝ) := exp (((β+γ)/2-1)*D)

private theorem odds_equality {s u : ℝ} (hs : 1 < s) (hu : 0 < u) :
    |s^2*u/(1+s^2*u)-u/(1+u)| = (s-1)/(s+1) ↔ s*u=1 := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hs2 : 1 < s^2 := by nlinarith only [hs,sq_nonneg (s-1)]
  have d := add_pos zero_lt_one hu
  have d' := add_pos zero_lt_one (mul_pos (sq_pos_of_pos hs0) hu)
  have ord : u/(1+u) ≤ s^2*u/(1+s^2*u) := by
    apply (div_le_div_iff₀ d d').mpr
    nlinarith only [mul_lt_mul_of_pos_right hs2 hu]
  have cross : s^2*u/(1+s^2*u)*(1-u/(1+u)) = s^2*(u/(1+u))*(1-s^2*u/(1+s^2*u)) := by
    field_simp [d.ne',d'.ne']; ring
  rw [abs_of_nonneg (sub_nonneg.mpr ord),binary_equality hs (div_nonneg hu.le d.le) cross.le,and_iff_left cross]
  rw [← mul_div_assoc,div_eq_iff d.ne',one_mul]
  constructor <;> intro h <;> linarith only [h]

private theorem ordered_equality {D k β γ : ℝ} (hD : 0 < D) (hk : 0 < k) (hbg : β < γ) :
    |upperProbability D k β-upperProbability D k γ| = tanh (|β-γ| * D/4) ↔ k=optimal D β γ := by
  let s := halfRatio (|β-γ| * D)
  let u := odds D k γ
  have hab : |β-γ| = γ-β := by rw [abs_of_neg (sub_neg.mpr hbg)]; ring
  have hs : 1 < s := by
    apply one_lt_exp_iff.mpr
    rw [hab]
    exact half_pos (mul_pos (sub_pos.mpr hbg) hD)
  have hstep : odds D k β = s^2*u := by
    rw [odds_step D k β γ]
    dsimp only [s,u]
    rw [halfRatio_sq,hab]
  have hmul : s*u = k/optimal D β γ := by
    dsimp only [s,u,halfRatio,odds,optimal]
    rw [hab,div_eq_mul_inv k,← exp_neg,mul_left_comm,← exp_add]
    congr 2; ring
  rw [← defect_eq,upperProbability,upperProbability,hstep]
  change |s^2*u/(1+s^2*u)-u/(1+u)| = (s-1)/(s+1) ↔ _
  rw [odds_equality hs (odds_pos D hk γ),hmul]
  exact div_eq_one_iff_eq (show optimal D β γ ≠ 0 from (exp_pos _).ne')

/-- For distinct temperatures the limiting binary contrast is sharp at exactly one width ratio. -/
theorem sharp_iff {D k β γ : ℝ} (hD : 0 < D) (hk : 0 < k) (hne : β ≠ γ) :
    |upperProbability D k β-upperProbability D k γ| = tanh (|β-γ| * D/4) ↔ k=optimal D β γ := by
  rcases lt_or_gt_of_ne hne with hh | hh
  · exact ordered_equality hD hk hh
  · simpa only [abs_sub_comm (upperProbability D k γ) (upperProbability D k β),abs_sub_comm γ β,
      optimal,add_comm γ β] using ordered_equality (k := k) hD hk hh

theorem optimal_eq_one_iff {D : ℝ} (hD : 0 < D) (β γ : ℝ) :
    optimal D β γ = 1 ↔ (β+γ)/2=1 := by
  rw [optimal,Real.exp_eq_one_iff,mul_eq_zero,or_iff_left hD.ne',sub_eq_zero]

/-- Equal logarithmic widths select inverse-temperature midpoint one. -/
theorem equal_width_iff {D β γ : ℝ} (hD : 0 < D) (hne : β ≠ γ) :
    |upperProbability D 1 β-upperProbability D 1 γ| = tanh (|β-γ| * D/4) ↔ (β+γ)/2=1 := by
  rw [sharp_iff hD zero_lt_one hne,eq_comm (a := (1:ℝ)),optimal_eq_one_iff hD]

#print axioms sharp_iff
#print axioms equal_width_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets
