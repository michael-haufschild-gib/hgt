import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDiagonalMeanSquare
import GaloisForLFunctions.RHTower.Sieve.InghamSmoothedDivisorMeanSquare

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- Literal diagonal dual summand in the exact square AFE. -/
def smoothAFEZetaSquareDualAFESummand (N : ℕ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, zetaChi (linePt t) ^ 2 *
    ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (linePt t - 1) *
    smoothAFEZetaSquareDualWeight t ((n + 1 : ℝ) * (N : ℝ))

theorem norm_smoothAFEZetaSquareDualAFESummand_eq_sourceField
    (N : ℕ) (t : ℝ) :
    ‖smoothAFEZetaSquareDualAFESummand N t‖ =
      ‖smoothAFEZetaSquareDualSourceField (N : ℝ) t t‖ := by
  rw [smoothAFEZetaSquareDualAFESummand,
    smoothAFEZetaSquareDual_tsum_eq_chiSq_mul_sourceField,
    norm_mul, norm_pow, norm_zetaChi_line]
  norm_num

/-- Complete literal dual AFE summand lies in the `N^(101/100)` Route-T budget. -/
theorem exists_integral_Icc_normSq_smoothAFEZetaSquareDualAFESummand_le_routeTBudget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualAFESummand N t‖ ^ 2) ≤
          C * (N : ℝ) ^ (101 / 100 : ℝ) := by
  obtain ⟨A, K, B, hA, hK, hB, hraw⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquareDualSourceField_diagonal_le
  let Q : ℝ := (401 : ℝ) ^ 4
  let C : ℝ :=
    10 * Real.pi * Real.exp 1 * B * Q +
      (5 * Real.pi / 2) * B * Q +
      10 * Real.pi * Real.exp 1 * K * Q +
      (5 * Real.pi / 2) * A
  have hC : 0 ≤ C := by dsimp only [C, Q]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hNR0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  let L : ℝ := 1 + Real.log (N : ℝ)
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    have := Real.log_nonneg hNR1
    linarith
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hlog4 : L ^ 4 ≤ Q * (N : ℝ) ^ (1 / 100 : ℝ) := by
    dsimp only [L, Q]
    exact RHTower.Sieve.one_add_log_nat_pow_four_le_rpow_one_hundredth N hN1
  have hlog3 : L ^ 3 ≤ L ^ 4 := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg hL0 3) hL1
  have hmulPow : (N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ) =
      (N : ℝ) ^ (101 / 100 : ℝ) := by
    calc
      (N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ) =
          (N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by
        congr 1
        exact (Real.rpow_one (N : ℝ)).symm
      _ = (N : ℝ) ^ ((1 / 100 : ℝ) + 1) :=
        (Real.rpow_add hNR0 _ _).symm
      _ = (N : ℝ) ^ (101 / 100 : ℝ) := by norm_num
  have hNlog4 : (N : ℝ) * L ^ 4 ≤
      Q * (N : ℝ) ^ (101 / 100 : ℝ) := by
    calc
      (N : ℝ) * L ^ 4 ≤ (N : ℝ) *
          (Q * (N : ℝ) ^ (1 / 100 : ℝ)) := by gcongr
      _ = Q * ((N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ)) := by ring
      _ = Q * (N : ℝ) ^ (101 / 100 : ℝ) := by rw [hmulPow]
  have hNlog3 : (N : ℝ) * L ^ 3 ≤
      Q * (N : ℝ) ^ (101 / 100 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hlog3 hNR0.le).trans hNlog4
  have h201 : (N : ℝ) ^ (201 / 200 : ℝ) ≤
      (N : ℝ) ^ (101 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNR1 (by norm_num)
  have hb := hraw hN
  have hb' :
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualAFESummand N t‖ ^ 2) ≤
      2 * (5 * Real.pi * Real.exp 1 *
          (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) +
        (5 * Real.pi / 2) *
          (B * (1 + Real.log (N : ℝ)) ^ 4) * ((N : ℝ) / 2)) +
      2 * (5 * Real.pi * Real.exp 1 * K * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ 3 +
        (5 * Real.pi / 4) * A * (N : ℝ) ^ (201 / 200 : ℝ)) := by
    simpa only [norm_smoothAFEZetaSquareDualAFESummand_eq_sourceField] using hb
  refine hb'.trans ?_
  change
    2 * (5 * Real.pi * Real.exp 1 * (B * (N : ℝ) * L ^ 3) +
      5 * Real.pi / 2 * (B * L ^ 4) * ((N : ℝ) / 2)) +
    2 * (5 * Real.pi * Real.exp 1 * K * (N : ℝ) * L ^ 3 +
      5 * Real.pi / 4 * A * (N : ℝ) ^ (201 / 200 : ℝ)) ≤
      C * (N : ℝ) ^ (101 / 100 : ℝ)
  calc
    2 * (5 * Real.pi * Real.exp 1 * (B * (N : ℝ) * L ^ 3) +
        5 * Real.pi / 2 * (B * L ^ 4) * ((N : ℝ) / 2)) +
      2 * (5 * Real.pi * Real.exp 1 * K * (N : ℝ) * L ^ 3 +
        5 * Real.pi / 4 * A * (N : ℝ) ^ (201 / 200 : ℝ)) =
      (10 * Real.pi * Real.exp 1 * B) * ((N : ℝ) * L ^ 3) +
        ((5 * Real.pi / 2) * B) * ((N : ℝ) * L ^ 4) +
        (10 * Real.pi * Real.exp 1 * K) * ((N : ℝ) * L ^ 3) +
        ((5 * Real.pi / 2) * A) * (N : ℝ) ^ (201 / 200 : ℝ) := by ring
    _ ≤ (10 * Real.pi * Real.exp 1 * B) *
          (Q * (N : ℝ) ^ (101 / 100 : ℝ)) +
        ((5 * Real.pi / 2) * B) *
          (Q * (N : ℝ) ^ (101 / 100 : ℝ)) +
        (10 * Real.pi * Real.exp 1 * K) *
          (Q * (N : ℝ) ^ (101 / 100 : ℝ)) +
        ((5 * Real.pi / 2) * A) *
          (N : ℝ) ^ (101 / 100 : ℝ) := by gcongr
    _ = C * (N : ℝ) ^ (101 / 100 : ℝ) := by
      dsimp only [C]
      ring

end RHTower
