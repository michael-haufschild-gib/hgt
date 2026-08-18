import GaloisForLFunctions.RHTower.Sieve.LadderGeomSums

/-!
# The three sums of the ladder's affine majorant, bounded

The slope and the constant of the ladder's affine majorant are built from two weighted sums over the
steps and from the defect's shape factor.  All three reduce to the geometric sums of the previous
file.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The slope's sum. -/
theorem sum_S1_le {B₀ : ℕ} {Q η hR : ℝ} (hQ0 : 0 < Q) (hη : 0 < η) {L : ℕ}
    (hle : Q * (1 + η) ^ L ≤ hR) :
    (∑ j ∈ Finset.range L,
        (Q * (1 + η) ^ j) * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
      ≤ (L : ℝ) * Real.sqrt ((B₀ : ℝ) * hR) + hR / η := by
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hterm : ∀ j ∈ Finset.range L,
      (Q * (1 + η) ^ j) * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)
        ≤ Real.sqrt ((B₀ : ℝ) * hR) + Q * (1 + η) ^ j := by
    intro j hj
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    have hjL : Q * (1 + η) ^ j ≤ hR := by
      have := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hr1 (le_of_lt (Finset.mem_range.1 hj))) hQ0.le
      linarith
    have hid : (Q * (1 + η) ^ j) * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)
        = Real.sqrt ((B₀ : ℝ) * (Q * (1 + η) ^ j) + (Q * (1 + η) ^ j) ^ 2) := by
      rw [show (B₀ : ℝ) * (Q * (1 + η) ^ j) + (Q * (1 + η) ^ j) ^ 2
          = (Q * (1 + η) ^ j) ^ 2 * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1) by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hbase.le]
    rw [hid]
    have hsplit : Real.sqrt ((B₀ : ℝ) * (Q * (1 + η) ^ j) + (Q * (1 + η) ^ j) ^ 2)
        ≤ Real.sqrt ((B₀ : ℝ) * (Q * (1 + η) ^ j)) + Q * (1 + η) ^ j := by
      have ha : (0 : ℝ) ≤ (B₀ : ℝ) * (Q * (1 + η) ^ j) := by positivity
      have hsa := Real.sq_sqrt ha
      have hsa0 := Real.sqrt_nonneg ((B₀ : ℝ) * (Q * (1 + η) ^ j))
      have hkey : (B₀ : ℝ) * (Q * (1 + η) ^ j) + (Q * (1 + η) ^ j) ^ 2
          ≤ (Real.sqrt ((B₀ : ℝ) * (Q * (1 + η) ^ j)) + Q * (1 + η) ^ j) ^ 2 := by
        nlinarith [hsa, hsa0, hbase.le]
      calc Real.sqrt ((B₀ : ℝ) * (Q * (1 + η) ^ j) + (Q * (1 + η) ^ j) ^ 2)
          ≤ Real.sqrt ((Real.sqrt ((B₀ : ℝ) * (Q * (1 + η) ^ j)) + Q * (1 + η) ^ j) ^ 2) :=
            Real.sqrt_le_sqrt hkey
        _ = Real.sqrt ((B₀ : ℝ) * (Q * (1 + η) ^ j)) + Q * (1 + η) ^ j :=
            Real.sqrt_sq (by positivity)
    have hmono : Real.sqrt ((B₀ : ℝ) * (Q * (1 + η) ^ j)) ≤ Real.sqrt ((B₀ : ℝ) * hR) :=
      Real.sqrt_le_sqrt (by nlinarith [hjL, Nat.cast_nonneg (α := ℝ) B₀])
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  linarith [sum_ladderEndpoint_le hQ0 hη hle]

/-- The constant's sum. -/
theorem sum_S2_le {B₀ : ℕ} {Q η hR : ℝ} (hQ0 : 0 < Q) (hη : 0 < η) {L : ℕ}
    (hle : Q * (1 + η) ^ L ≤ hR) :
    (∑ j ∈ Finset.range L,
        (Q * (1 + η) ^ j)
          * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j)) * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)))
      ≤ (L : ℝ) * (B₀ : ℝ) + hR / η := by
  have hterm : ∀ j ∈ Finset.range L,
      (Q * (1 + η) ^ j)
        * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j)) * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
        ≤ (B₀ : ℝ) + Q * (1 + η) ^ j := by
    intro j _
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    have hN0 : (0 : ℝ) ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) := by positivity
    have hsq : Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j))
          * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
        ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) + 1 := by
      have hle2 : ((B₀ : ℝ) / (Q * (1 + η) ^ j)) * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)
          ≤ ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1) ^ 2 := by nlinarith [hN0]
      calc Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j))
              * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
          ≤ Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1) ^ 2) := Real.sqrt_le_sqrt hle2
        _ = (B₀ : ℝ) / (Q * (1 + η) ^ j) + 1 := Real.sqrt_sq (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hsq hbase.le
    refine hmul.trans (le_of_eq ?_)
    field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  linarith [sum_ladderEndpoint_le hQ0 hη hle]

/-- The defect's inner sum. -/
theorem ladderDefect_inner_le {B₀ : ℕ} {Q η hR : ℝ} (hQ0 : 0 < Q) (hη : 0 < η) (hη1 : η ≤ 1)
    {L : ℕ} (hle : Q * (1 + η) ^ L ≤ hR) :
    (∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
        * ((1 + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5 + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ 2))
      ≤ (L : ℝ) * ((1 + (B₀ : ℝ)) * η ^ 2 + 5) + 5 * hR
        + (η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η) * (2 / (Q * η)) + (B₀ : ℝ) * (2 / (Q ^ 2 * η)) := by
  have hterm : ∀ j ∈ Finset.range L,
      (Q * (1 + η) ^ j * η + 1)
          * ((1 + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5 + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ 2)
        = ((1 + (B₀ : ℝ)) * η ^ 2 + 5) + 5 * η * (Q * (1 + η) ^ j)
          + (η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η) * (1 / (Q * (1 + η) ^ j))
          + (B₀ : ℝ) * (1 / (Q * (1 + η) ^ j) ^ 2) := by
    intro j _
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  have e1 : (∑ j ∈ Finset.range L, 5 * η * (Q * (1 + η) ^ j))
      = 5 * η * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j) := by rw [Finset.mul_sum]
  have e2 : (∑ j ∈ Finset.range L,
        (η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η) * (1 / (Q * (1 + η) ^ j)))
      = (η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η)
        * ∑ j ∈ Finset.range L, (1 / (Q * (1 + η) ^ j)) := by rw [Finset.mul_sum]
  have e3 : (∑ j ∈ Finset.range L, (B₀ : ℝ) * (1 / (Q * (1 + η) ^ j) ^ 2))
      = (B₀ : ℝ) * ∑ j ∈ Finset.range L, (1 / (Q * (1 + η) ^ j) ^ 2) := by rw [Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, Finset.card_range, e1, e2, e3]
  have h1 := sum_ladderEndpoint_le hQ0 hη hle
  have h2 := sum_inv_ladderEndpoint_le hQ0 hη hη1 L
  have h3 := sum_inv_sq_ladderEndpoint_le hQ0 hη hη1 L
  have hc1 : (0 : ℝ) ≤ 5 * η := by linarith
  have hc2 : (0 : ℝ) ≤ η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η := by positivity
  have hc3 : (0 : ℝ) ≤ (B₀ : ℝ) := Nat.cast_nonneg _
  have hs1 := mul_le_mul_of_nonneg_left h1 hc1
  have hs2 := mul_le_mul_of_nonneg_left h2 hc2
  have hs3 := mul_le_mul_of_nonneg_left h3 hc3
  have hid : 5 * η * (hR / η) = 5 * hR := by
    field_simp
  linarith [hs1, hs2, hs3, hid]

end

end RHTower.Sieve
