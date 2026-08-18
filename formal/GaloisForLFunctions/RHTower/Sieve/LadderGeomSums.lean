import GaloisForLFunctions.RHTower.Sieve.LadderAffineMajorant

/-!
# The geometric sums of the ladder

The ladder's affine slope and constant are built from four sums over the steps: the endpoints, their
reciprocals, the squares of their reciprocals and their square roots.  All four are geometric, hence
explicit.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The endpoints sum to the top divided by the step ratio. -/
theorem sum_ladderEndpoint_le {Q η hR : ℝ} (hQ0 : 0 < Q) (hη : 0 < η) {L : ℕ}
    (hle : Q * (1 + η) ^ L ≤ hR) :
    (∑ j ∈ Finset.range L, Q * (1 + η) ^ j) ≤ hR / η := by
  have hne : (1 : ℝ) + η ≠ 1 := by linarith
  have hgeom : (∑ j ∈ Finset.range L, ((1 : ℝ) + η) ^ j)
      = ((1 + η) ^ L - 1) / ((1 + η) - 1) := geom_sum_eq hne L
  have hsimp : ((1 : ℝ) + η) - 1 = η := by ring
  rw [hsimp] at hgeom
  rw [← Finset.mul_sum, hgeom]
  rw [mul_div_assoc'] at *
  rw [div_le_div_iff₀ hη hη]
  nlinarith [hle, hη]

/-- The reciprocals of the endpoints form a geometric series. -/
theorem sum_inv_ladderEndpoint_le {Q η : ℝ} (hQ0 : 0 < Q) (hη : 0 < η) (hη1 : η ≤ 1) (L : ℕ) :
    (∑ j ∈ Finset.range L, 1 / (Q * (1 + η) ^ j)) ≤ 2 / (Q * η) := by
  have hr0 : (0 : ℝ) < 1 / (1 + η) := by positivity
  have hr1 : (1 : ℝ) / (1 + η) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hne : (1 : ℝ) / (1 + η) ≠ 1 := ne_of_lt hr1
  have hgeom : (∑ j ∈ Finset.range L, ((1 : ℝ) / (1 + η)) ^ j)
      = (((1 : ℝ) / (1 + η)) ^ L - 1) / ((1 : ℝ) / (1 + η) - 1) := geom_sum_eq hne L
  have hsum : (∑ j ∈ Finset.range L, ((1 : ℝ) / (1 + η)) ^ j) ≤ (1 + η) / η := by
    rw [hgeom]
    have hden : (1 : ℝ) / (1 + η) - 1 = -(η / (1 + η)) := by
      field_simp
      ring
    rw [hden]
    have hnum : ((1 : ℝ) / (1 + η)) ^ L - 1 ≤ 0 := by
      have : ((1 : ℝ) / (1 + η)) ^ L ≤ 1 := pow_le_one₀ hr0.le hr1.le
      linarith
    have hd0 : (0 : ℝ) < η / (1 + η) := by positivity
    rw [div_neg, neg_le]
    rw [le_div_iff₀ hd0]
    have hnum0 : (0 : ℝ) ≤ ((1 : ℝ) / (1 + η)) ^ L := by positivity
    have hid : -((1 + η) / η) * (η / (1 + η)) = -1 := by
      field_simp
    rw [hid]
    linarith
  have hrewrite : (∑ j ∈ Finset.range L, 1 / (Q * (1 + η) ^ j))
      = (1 / Q) * ∑ j ∈ Finset.range L, ((1 : ℝ) / (1 + η)) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, one_pow]
    field_simp
  rw [hrewrite]
  have hstep : (1 / Q) * ∑ j ∈ Finset.range L, ((1 : ℝ) / (1 + η)) ^ j
      ≤ (1 / Q) * ((1 + η) / η) := by
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  refine hstep.trans ?_
  have hid : (1 / Q) * ((1 + η) / η) = (1 + η) / (Q * η) := by
    field_simp
  rw [hid, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_pos hQ0 hη).le (sub_nonneg.2 hη1)]

/-- The squared reciprocals of the endpoints. -/
theorem sum_inv_sq_ladderEndpoint_le {Q η : ℝ} (hQ0 : 0 < Q) (hη : 0 < η) (hη1 : η ≤ 1) (L : ℕ) :
    (∑ j ∈ Finset.range L, 1 / (Q * (1 + η) ^ j) ^ 2) ≤ 2 / (Q ^ 2 * η) := by
  have hterm : ∀ j ∈ Finset.range L,
      1 / (Q * (1 + η) ^ j) ^ 2 ≤ (1 / Q) * (1 / (Q * (1 + η) ^ j)) := by
    intro j _
    have hpow : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ (by linarith)
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    rw [div_mul_div_comm, one_mul]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [hpow, hQ0, hbase]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hstep := mul_le_mul_of_nonneg_left (sum_inv_ladderEndpoint_le hQ0 hη hη1 L)
    (by positivity : (0 : ℝ) ≤ 1 / Q)
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- The square roots of the endpoints, bounded by the top. -/
theorem sum_sqrt_ladderEndpoint_le {Q η hR : ℝ} (hQ0 : 0 < Q) (hη : 0 ≤ η) {L : ℕ}
    (hle : Q * (1 + η) ^ L ≤ hR) :
    (∑ j ∈ Finset.range L, Real.sqrt (Q * (1 + η) ^ j)) ≤ (L : ℝ) * Real.sqrt hR := by
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hterm : ∀ j ∈ Finset.range L, Real.sqrt (Q * (1 + η) ^ j) ≤ Real.sqrt hR := by
    intro j hj
    refine Real.sqrt_le_sqrt ?_
    have hjL : j ≤ L := le_of_lt (Finset.mem_range.1 hj)
    have := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 hjL) hQ0.le
    linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]

end

end RHTower.Sieve
