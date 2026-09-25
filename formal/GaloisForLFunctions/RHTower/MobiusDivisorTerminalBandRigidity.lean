import GaloisForLFunctions.RHTower.MobiusDivisorFirstOmissionSourceLaw
import GaloisForLFunctions.RHTower.MobiusDivisorSquareRootTerminalOrder

/-!
# Terminal first-cell band rigidity

For an arbitrary processed-prime core, once all square-root primes are paid and
every unpaid active prime is in the first quotient cell, the unpaid mass in a
fixed interior band is bounded by the completed source and the square root of
the literal retained energy. This finite inequality makes no prime-prefix or
path assumption. It does not produce a quadratic path budget.
-/

noncomputable section
open Finset
namespace RHTower

private theorem terminal_head_abs_le_sqrt_energy (M : ℕ) (P : Finset ℕ)
    (hcover : ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P) :
    |mobiusDivisorSelectionFibre M P ∅| ≤
      Real.sqrt (mobiusDivisorSelectionEnergy M P) := by
  have hsmall : mobiusDivisorSmallSelectionPrimes M ⊆ P := by
    intro p hp
    have h := mem_filter.mp hp
    exact hcover p h.1 h.2.le
  have heq := mobiusDivisorSelectionEnergy_terminal M P hsmall
  have hnonneg : 0 ≤ ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
      (mobiusDivisorSelectionFibre M P {p}) ^ (2 : ℕ) :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hsq : (mobiusDivisorSelectionFibre M P ∅) ^ (2 : ℕ) ≤
      mobiusDivisorSelectionEnergy M P := by rw [heq]; linarith
  have henonneg : 0 ≤ mobiusDivisorSelectionEnergy M P :=
    (sq_nonneg _).trans hsq
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa only [sq_abs, Real.sq_sqrt henonneg] using hsq

/-- Unpaid first-cell mass cannot exceed the terminal head allowance plus the
complete arithmetic source. -/
theorem omitted_first_cell_mass_le_energy (M : ℕ) (P : Finset ℕ)
    (hM : 1 ≤ M)
    (hcover : ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P)
    (hcell : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P, M ≤ 2 * p) :
    (2 * Real.eulerMascheroniConstant - 1) *
        ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
          (Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ)) ≤
      |criticalContinuousAbel (M : ℝ)| +
        Real.sqrt (mobiusDivisorSelectionEnergy M P) := by
  have hhead := adaptive_terminal_head_first_cell M P hM hcover hcell
  have habs := terminal_head_abs_le_sqrt_energy M P hcover
  rw [hhead] at habs
  linarith [le_abs_self (criticalContinuousAbel (M : ℝ) +
      (2 * Real.eulerMascheroniConstant - 1) *
        ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
          (Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ))),
    neg_abs_le (criticalContinuousAbel (M : ℝ))]

/-- The number of unpaid primes between the half-cutoff and three-quarter
cutoff is controlled at the *same* cutoff, uniformly over terminal cores. -/
theorem omitted_middle_band_card_le_energy (M : ℕ) (P : Finset ℕ)
    (hM : 1 ≤ M)
    (hcover : ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P)
    (hcell : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P, M ≤ 2 * p) :
    (2 * Real.eulerMascheroniConstant - 1) *
        (Real.sqrt (M : ℝ) / 8) *
        (((mobiusDivisorSelectionPrimes M \ P).filter (fun p => 4 * p ≤ 3 * M)).card : ℝ) ≤
      |criticalContinuousAbel (M : ℝ)| +
        Real.sqrt (mobiusDivisorSelectionEnergy M P) := by
  let U := mobiusDivisorSelectionPrimes M \ P
  let B := U.filter (fun p => 4 * p ≤ 3 * M)
  have hκ : 0 ≤ 2 * Real.eulerMascheroniConstant - 1 := by
    have := Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hU : ∀ p ∈ U, 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ) := by
    intro p hp
    have hpM : p < M := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast hpM.le))
  have hB : ∀ p ∈ B,
      Real.sqrt (M : ℝ) / 8 ≤ Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ) := by
    intro p hp
    have hband : 4 * p ≤ 3 * M := (Finset.mem_filter.mp hp).2
    have hbandR : 4 * (p : ℝ) ≤ 3 * (M : ℝ) := by exact_mod_cast hband
    have hs : Real.sqrt (p : ℝ) ≤ (7 / 8 : ℝ) * Real.sqrt (M : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
        norm_num
        nlinarith
    linarith
  have hsumB : (B.card : ℝ) * (Real.sqrt (M : ℝ) / 8) ≤
      ∑ p ∈ B, (Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ)) := by
    simpa only [sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := B) (fun p hp => hB p hp))
  have hsumU : (∑ p ∈ B, (Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ))) ≤
      ∑ p ∈ U, (Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p hp _ => hU p hp)
  calc
    (2 * Real.eulerMascheroniConstant - 1) * (Real.sqrt (M : ℝ) / 8) * (B.card : ℝ) =
        (2 * Real.eulerMascheroniConstant - 1) *
          ((B.card : ℝ) * (Real.sqrt (M : ℝ) / 8)) := by ring
    _ ≤ (2 * Real.eulerMascheroniConstant - 1) *
          ∑ p ∈ B, (Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hsumB hκ
    _ ≤ (2 * Real.eulerMascheroniConstant - 1) *
          ∑ p ∈ U, (Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hsumU hκ
    _ ≤ _ := omitted_first_cell_mass_le_energy M P hM hcover hcell

end RHTower
