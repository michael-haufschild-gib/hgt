import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicLadderError

/-!
# Sharp schedule-ready bound for Menon's harmonic ladder defect

The closed harmonic support-defect budget is useful only after retaining the geometric top of the
designated prime ladder.  This file bounds every summand by that top.  In particular, truncating
the prime ladder below the ambient scale yields a genuine power of the logarithm instead of paying
for all integers up to the ambient endpoint.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The summand in the closed harmonic ladder-defect budget, bounded using the actual geometric
top of the designated-prime ladder. -/
theorem menonHarmonicLadder_gapSummand_le
    {A₀ B₀ : ℕ} {Q eta U : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta)
    {L j : ℕ} (hj : j < L) (htop : Q * (1 + eta) ^ L ≤ U) :
    (Q * (1 + eta) ^ j * eta + 1) *
        (((A₀ : ℝ) + (B₀ : ℝ)) * eta / (Q * (1 + eta) ^ j) + 5 +
          (B₀ : ℝ) / (Q * (1 + eta) ^ j) ^ (2 : ℕ)) ≤
      ((A₀ : ℝ) + (B₀ : ℝ)) * eta ^ (2 : ℕ) + 5 * eta * U +
        (((A₀ : ℝ) + 2 * (B₀ : ℝ)) * eta) / Q + 5 + (B₀ : ℝ) / Q ^ (2 : ℕ) := by
  have hr : (1 : ℝ) ≤ 1 + eta := by linarith
  have hQj0 : 0 < Q * (1 + eta) ^ j := mul_pos hQ (pow_pos (by linarith) _)
  have hmono : Q * (1 + eta) ^ j ≤ Q * (1 + eta) ^ L := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (Nat.le_of_lt hj)) hQ.le
  have hQjU : Q * (1 + eta) ^ j ≤ U := hmono.trans htop
  have hQle : Q ≤ Q * (1 + eta) ^ j := by
    have hjone : (1 : ℝ) ≤ (1 + eta) ^ j := one_le_pow₀ hr
    nlinarith
  have hinv : 1 / (Q * (1 + eta) ^ j) ≤ 1 / Q := by
    exact one_div_le_one_div_of_le hQ hQle
  have hinvSq : 1 / (Q * (1 + eta) ^ j) ^ (2 : ℕ) ≤ 1 / Q ^ (2 : ℕ) := by
    calc
      1 / (Q * (1 + eta) ^ j) ^ (2 : ℕ) = (1 / (Q * (1 + eta) ^ j)) ^ (2 : ℕ) := by ring
      _ ≤ (1 / Q) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hinv 2
      _ = 1 / Q ^ (2 : ℕ) := by ring
  have hA : (0 : ℝ) ≤ (A₀ : ℝ) + (B₀ : ℝ) := by positivity
  have hB : (0 : ℝ) ≤ (B₀ : ℝ) := by positivity
  have hEtaU : eta * (Q * (1 + eta) ^ j) ≤ eta * U :=
    mul_le_mul_of_nonneg_left hQjU heta
  have hInvAB :
      (((A₀ : ℝ) + (B₀ : ℝ)) * eta) * (1 / (Q * (1 + eta) ^ j)) ≤
        (((A₀ : ℝ) + (B₀ : ℝ)) * eta) * (1 / Q) :=
    mul_le_mul_of_nonneg_left hinv (mul_nonneg hA heta)
  have hInvB :
      ((B₀ : ℝ) * eta) * (1 / (Q * (1 + eta) ^ j)) ≤
        ((B₀ : ℝ) * eta) * (1 / Q) :=
    mul_le_mul_of_nonneg_left hinv (mul_nonneg hB heta)
  have hInvSqB :
      (B₀ : ℝ) * (1 / (Q * (1 + eta) ^ j) ^ (2 : ℕ)) ≤
        (B₀ : ℝ) * (1 / Q ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hinvSq hB
  calc
    (Q * (1 + eta) ^ j * eta + 1) *
        (((A₀ : ℝ) + (B₀ : ℝ)) * eta / (Q * (1 + eta) ^ j) + 5 +
          (B₀ : ℝ) / (Q * (1 + eta) ^ j) ^ (2 : ℕ)) =
      ((A₀ : ℝ) + (B₀ : ℝ)) * eta ^ (2 : ℕ) +
        5 * (eta * (Q * (1 + eta) ^ j)) +
        ((B₀ : ℝ) * eta) * (1 / (Q * (1 + eta) ^ j)) +
        (((A₀ : ℝ) + (B₀ : ℝ)) * eta) * (1 / (Q * (1 + eta) ^ j)) +
        5 + (B₀ : ℝ) * (1 / (Q * (1 + eta) ^ j) ^ (2 : ℕ)) := by
          field_simp
          ring
    _ ≤ ((A₀ : ℝ) + (B₀ : ℝ)) * eta ^ (2 : ℕ) + 5 * (eta * U) +
        ((B₀ : ℝ) * eta) * (1 / Q) +
        (((A₀ : ℝ) + (B₀ : ℝ)) * eta) * (1 / Q) +
        5 + (B₀ : ℝ) * (1 / Q ^ (2 : ℕ)) := by
          gcongr
    _ = ((A₀ : ℝ) + (B₀ : ℝ)) * eta ^ (2 : ℕ) + 5 * eta * U +
        (((A₀ : ℝ) + 2 * (B₀ : ℝ)) * eta) / Q + 5 + (B₀ : ℝ) / Q ^ (2 : ℕ) := by
          field_simp
          ring

/-- Sum form of `menonHarmonicLadder_gapSummand_le`. -/
theorem sum_menonHarmonicLadder_gapSummand_le
    {A₀ B₀ : ℕ} {Q eta U : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta)
    {L : ℕ} (htop : Q * (1 + eta) ^ L ≤ U) :
    (∑ j ∈ Finset.range L, (Q * (1 + eta) ^ j * eta + 1) *
        (((A₀ : ℝ) + (B₀ : ℝ)) * eta / (Q * (1 + eta) ^ j) + 5 +
          (B₀ : ℝ) / (Q * (1 + eta) ^ j) ^ (2 : ℕ))) ≤
      (L : ℝ) * (((A₀ : ℝ) + (B₀ : ℝ)) * eta ^ (2 : ℕ) + 5 * eta * U +
        (((A₀ : ℝ) + 2 * (B₀ : ℝ)) * eta) / Q + 5 + (B₀ : ℝ) / Q ^ (2 : ℕ)) := by
  calc
    (∑ j ∈ Finset.range L, (Q * (1 + eta) ^ j * eta + 1) *
        (((A₀ : ℝ) + (B₀ : ℝ)) * eta / (Q * (1 + eta) ^ j) + 5 +
          (B₀ : ℝ) / (Q * (1 + eta) ^ j) ^ (2 : ℕ))) ≤
      ∑ _j ∈ Finset.range L,
        (((A₀ : ℝ) + (B₀ : ℝ)) * eta ^ (2 : ℕ) + 5 * eta * U +
          (((A₀ : ℝ) + 2 * (B₀ : ℝ)) * eta) / Q + 5 + (B₀ : ℝ) / Q ^ (2 : ℕ)) := by
            exact Finset.sum_le_sum fun j hj =>
              menonHarmonicLadder_gapSummand_le hQ heta (Finset.mem_range.1 hj) htop
    _ = (L : ℝ) * (((A₀ : ℝ) + (B₀ : ℝ)) * eta ^ (2 : ℕ) + 5 * eta * U +
        (((A₀ : ℝ) + 2 * (B₀ : ℝ)) * eta) / Q + 5 + (B₀ : ℝ) / Q ^ (2 : ℕ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]

/-- Closed ladder-defect budget with the actual geometric prime top retained. -/
theorem menonHarmonicLadderErrorBudget_le_top
    {A₀ B₀ : ℕ} {Q eta U W : ℝ} (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 0 ≤ W)
    {L : ℕ} (htop : Q * (1 + eta) ^ L ≤ U) :
    menonHarmonicLadderErrorBudget A₀ B₀ Q eta W L ≤
      ((1 + eta) / (A₀ : ℝ)) ^ (2 : ℕ) *
        (5 * Real.pi / 2 * W +
          5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ)) *
        (Real.log ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) / Real.log Q) *
        ((L : ℝ) * (((A₀ : ℝ) + (B₀ : ℝ)) * eta ^ (2 : ℕ) + 5 * eta * U +
          (((A₀ : ℝ) + 2 * (B₀ : ℝ)) * eta) / Q + 5 +
          (B₀ : ℝ) / Q ^ (2 : ℕ))) := by
  have hQ0 : 0 < Q := lt_trans zero_lt_one hQ
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ
  have hmean : 0 ≤ 5 * Real.pi / 2 * W +
      5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) := by positivity
  have hlogN : 0 ≤ Real.log ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) :=
    Real.log_natCast_nonneg _
  have hscale : 0 ≤ ((1 + eta) / (A₀ : ℝ)) ^ (2 : ℕ) := sq_nonneg _
  have hsum := sum_menonHarmonicLadder_gapSummand_le
    (A₀ := A₀) (B₀ := B₀) hQ0 heta htop
  rw [menonHarmonicLadderErrorBudget]
  have hK : 0 ≤ Real.log ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) / Real.log Q :=
    div_nonneg hlogN hlogQ.le
  calc
    ((1 + eta) / (A₀ : ℝ)) ^ (2 : ℕ) *
        ((5 * Real.pi / 2 * W +
            5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ)) *
          (Real.log ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) / Real.log Q *
            ∑ j ∈ Finset.range L, (Q * (1 + eta) ^ j * eta + 1) *
              (((A₀ : ℝ) + (B₀ : ℝ)) * eta / (Q * (1 + eta) ^ j) + 5 +
                (B₀ : ℝ) / (Q * (1 + eta) ^ j) ^ (2 : ℕ)))) =
      (((1 + eta) / (A₀ : ℝ)) ^ (2 : ℕ) *
        (5 * Real.pi / 2 * W +
          5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ)) *
        (Real.log ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) / Real.log Q)) *
        (∑ j ∈ Finset.range L, (Q * (1 + eta) ^ j * eta + 1) *
          (((A₀ : ℝ) + (B₀ : ℝ)) * eta / (Q * (1 + eta) ^ j) + 5 +
            (B₀ : ℝ) / (Q * (1 + eta) ^ j) ^ (2 : ℕ))) := by ring
    _ ≤ (((1 + eta) / (A₀ : ℝ)) ^ (2 : ℕ) *
        (5 * Real.pi / 2 * W +
          5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ)) *
        (Real.log ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) / Real.log Q)) *
        ((L : ℝ) * (((A₀ : ℝ) + (B₀ : ℝ)) * eta ^ (2 : ℕ) + 5 * eta * U +
          (((A₀ : ℝ) + 2 * (B₀ : ℝ)) * eta) / Q + 5 +
          (B₀ : ℝ) / Q ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (mul_nonneg hscale hmean) hK)
    _ = _ := by ring

end

end RHTower.Sieve
