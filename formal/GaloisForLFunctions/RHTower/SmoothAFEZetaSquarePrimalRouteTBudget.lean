import GaloisForLFunctions.RHTower.SmoothAFEZetaSquarePrimalAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.InghamSmoothedDivisorMeanSquare

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- Literal primal summand in the exact square AFE. -/
def smoothAFEZetaSquarePrimalAFESummand (N : ℕ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (-linePt t) *
      smoothAFECutoff ((n + 1 : ℝ) / (N : ℝ))

theorem smoothAFEZetaSquarePrimalAFESummand_eq_sourceField
    (N : ℕ) (t : ℝ) :
    smoothAFEZetaSquarePrimalAFESummand N t =
      smoothAFEZetaSquarePrimalSourceField N t := rfl

/-- Complete literal primal AFE summand lies in the `N^(101/100)` Route-T budget. -/
theorem exists_integral_Icc_normSq_smoothAFEZetaSquarePrimalAFESummand_le_routeTBudget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquarePrimalAFESummand N t‖ ^ 2) ≤
          C * (N : ℝ) ^ (101 / 100 : ℝ) := by
  obtain ⟨B, hB, hraw⟩ :=
    exists_integral_normSq_smoothAFEZetaSquarePrimalSourceField_le
  let Q : ℝ := (401 : ℝ) ^ 4
  let C : ℝ :=
    5 * Real.pi * Real.exp 1 * B * Q +
      (5 * Real.pi / 4) * B * Q
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
      Q * (N : ℝ) ^ (101 / 100 : ℝ) :=
    (mul_le_mul_of_nonneg_left hlog3 hNR0.le).trans hNlog4
  have hH : (1 : ℝ) ≤ (N : ℝ) / 2 := by
    have : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hb := hraw
    (center := (3 / 2 : ℝ) * (N : ℝ))
    (H := (N : ℝ) / 2) hN hH
  have hb' :
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquarePrimalAFESummand N t‖ ^ 2) ≤
      5 * Real.pi * Real.exp 1 *
          (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) +
        (5 * Real.pi / 2) *
          (B * (1 + Real.log (N : ℝ)) ^ 4) * ((N : ℝ) / 2) := by
    simpa only [smoothAFEZetaSquarePrimalAFESummand_eq_sourceField,
      show (3 / 2 : ℝ) * (N : ℝ) - (N : ℝ) / 2 = (N : ℝ) by ring,
      show (3 / 2 : ℝ) * (N : ℝ) + (N : ℝ) / 2 = 2 * (N : ℝ) by ring]
      using hb
  refine hb'.trans ?_
  change
    5 * Real.pi * Real.exp 1 * (B * (N : ℝ) * L ^ 3) +
      (5 * Real.pi / 2) * (B * L ^ 4) * ((N : ℝ) / 2) ≤
        C * (N : ℝ) ^ (101 / 100 : ℝ)
  calc
    5 * Real.pi * Real.exp 1 * (B * (N : ℝ) * L ^ 3) +
        (5 * Real.pi / 2) * (B * L ^ 4) * ((N : ℝ) / 2) =
      (5 * Real.pi * Real.exp 1 * B) * ((N : ℝ) * L ^ 3) +
        ((5 * Real.pi / 4) * B) * ((N : ℝ) * L ^ 4) := by ring
    _ ≤ (5 * Real.pi * Real.exp 1 * B) *
          (Q * (N : ℝ) ^ (101 / 100 : ℝ)) +
        ((5 * Real.pi / 4) * B) *
          (Q * (N : ℝ) ^ (101 / 100 : ℝ)) := by gcongr
    _ = C * (N : ℝ) ^ (101 / 100 : ℝ) := by
      dsimp only [C]
      ring

end RHTower
