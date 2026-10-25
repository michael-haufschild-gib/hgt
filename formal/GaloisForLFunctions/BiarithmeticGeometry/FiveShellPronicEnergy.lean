import GaloisForLFunctions.BiarithmeticGeometry.DigitPronicBlocks
import GaloisForLFunctions.BiarithmeticGeometry.PronicEnergyDomain

/-!
# The intrinsic shell norm is the ordinary step-prefix pronic norm

A shell coefficient is constant on its base-five block. The exact
reciprocal telescope gives block mass `(4/5)5^(-M)`, including every
signed mixed pairing. Complete blocks and monotonicity then identify
finite shell energy with bounded ordinary pronic norms at all cutoffs.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Extend shell coefficients to their integer blocks, keeping the origin zero. -/
def fiveShellRow (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else v (Nat.log 5 n)

theorem fiveShellRow_zero (v : ℕ → ℝ) : fiveShellRow v 0 = 0 := by
  simp only [fiveShellRow, ite_true]

/-- The zero-origin shell extension is linear in its coefficient sequence. -/
theorem fiveShellRow_linear (s : ℝ) (v w : ℕ → ℝ) (n : ℕ) :
    fiveShellRow (fun M => s * v M + w M) n =
      s * fiveShellRow v n + fiveShellRow w n := by
  by_cases hn : n = 0
  · simp only [hn, fiveShellRow_zero, mul_zero, add_zero]
  · simp only [fiveShellRow, if_neg hn]

/-- A complete shell reads exactly one coefficient. -/
theorem fiveShellRow_on_block (v : ℕ → ℝ) (M n : ℕ)
    (hlo : 5 ^ M ≤ n) (hhi : n < 5 ^ (M + 1)) : fiveShellRow v n = v M := by
  have hn : n ≠ 0 := by have hp : 0 < 5 ^ M := pow_pos (by omega) M; omega
  have hlog : Nat.log 5 n = M :=
    (Nat.log_eq_iff (Or.inr ⟨by omega, hn⟩)).mpr ⟨hlo, hhi⟩
  rw [fiveShellRow, if_neg hn, hlog]

/-- The signed pairing on every complete shell has its exact geometric weight. -/
theorem fiveShell_pronicBlock_pairing (v w : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Ico ((5 : ℕ) ^ M) (5 ^ (M + 1)),
      fiveShellRow v n * fiveShellRow w n / ((n : ℝ) * ((n : ℝ) + 1))) =
        (4 / 5 : ℝ) * (v M * w M / (5 : ℝ) ^ M) := by
  calc
    _ = (v M * w M) *
        ∑ n ∈ Ico ((5 : ℕ) ^ M) (5 ^ (M + 1)), 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [fiveShellRow_on_block v M n (mem_Ico.mp hn).1 (mem_Ico.mp hn).2,
        fiveShellRow_on_block w M n (mem_Ico.mp hn).1 (mem_Ico.mp hn).2]
      ring
    _ = _ := by rw [fiveBlock_pronic_mass]; ring

private theorem fiveShell_pronicBlock_sq (v : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Ico ((5 : ℕ) ^ M) (5 ^ (M + 1)),
      fiveShellRow v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
        (4 / 5 : ℝ) * (v M ^ 2 / (5 : ℝ) ^ M) := by
  simpa only [pow_two] using fiveShell_pronicBlock_pairing v v M

/-- Energy of the step-prefix shell row below an ordinary integer cutoff. -/
def fiveShellPronicEnergyTo (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ico 1 N, fiveShellRow v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- Every complete prefix is exactly four fifths of the finite shell energy. -/
theorem fiveShellPronicEnergyTo_complete (v : ℕ → ℝ) (R : ℕ) :
    fiveShellPronicEnergyTo v (5 ^ (R + 1)) =
      (4 / 5 : ℝ) * ∑ M ∈ range (R + 1), v M ^ 2 / (5 : ℝ) ^ M := by
  induction R with
  | zero => simpa only [fiveShellPronicEnergyTo, zero_add, pow_zero, sum_range_one] using
      fiveShell_pronicBlock_sq v 0
  | succ R ih =>
    have hsplit : fiveShellPronicEnergyTo v (5 ^ (R + 1 + 1)) =
        fiveShellPronicEnergyTo v (5 ^ (R + 1)) +
          ∑ n ∈ Ico ((5 : ℕ) ^ (R + 1)) (5 ^ (R + 1 + 1)),
            fiveShellRow v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      symm
      apply sum_Ico_consecutive
      · have hp : 0 < (5 : ℕ) ^ (R + 1) := pow_pos (by omega) _
        omega
      · rw [pow_succ]
        omega
    rw [hsplit, ih, fiveShell_pronicBlock_sq,
      Finset.sum_range_succ (fun M => v M ^ 2 / (5 : ℝ) ^ M) (R + 1)]
    ring

theorem fiveShellPronicEnergyTo_monotone (v : ℕ → ℝ) :
    Monotone (fiveShellPronicEnergyTo v) := by
  intro N M hNM
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact mem_Ico.mpr ⟨(mem_Ico.mp hn).1, lt_of_lt_of_le (mem_Ico.mp hn).2 hNM⟩
  · intro n _ _
    positivity

/-- The shell square sum is finite exactly when all ordinary prefix energies are bounded. -/
theorem bounded_fiveShellPronicEnergy_iff (v : ℕ → ℝ) :
    (∃ B : ℝ, ∀ N : ℕ, fiveShellPronicEnergyTo v N ≤ B) ↔
      Summable (fun M : ℕ => v M ^ 2 / (5 : ℝ) ^ M) := by
  constructor
  · rintro ⟨B, hB⟩
    refine summable_of_sum_range_le (fun M => by positivity) (c := (5 / 4 : ℝ) * B) fun R => ?_
    have hb := hB (5 ^ (R + 1))
    rw [fiveShellPronicEnergyTo_complete] at hb
    have hs : (∑ M ∈ range R, v M ^ 2 / (5 : ℝ) ^ M) ≤
        ∑ M ∈ range (R + 1), v M ^ 2 / (5 : ℝ) ^ M := by
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (by positivity)
    linarith only [hb, hs]
  · intro hv
    refine ⟨(4 / 5 : ℝ) * ∑' M : ℕ, v M ^ 2 / (5 : ℝ) ^ M, fun N => ?_⟩
    let R := Nat.log 5 N
    have hN : N ≤ 5 ^ (R + 1) :=
      (Nat.lt_pow_succ_log_self (by omega : 1 < 5) N).le
    calc
      _ ≤ fiveShellPronicEnergyTo v (5 ^ (R + 1)) := fiveShellPronicEnergyTo_monotone v hN
      _ = _ := fiveShellPronicEnergyTo_complete v R
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_hasSum _ (fun M _ => by positivity) hv.hasSum) (by norm_num)

/-- The prefix convention agrees exactly with the ordinary pronic norm. -/
theorem fiveShellPronicEnergyTo_succ (v : ℕ → ℝ) (T : ℕ) :
    fiveShellPronicEnergyTo v (T + 1) =
      GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm (fiveShellRow v) T ^ 2 := by
  have hset : Ico 1 (T + 1) = Icc 1 T := by ext n; simp only [mem_Ico, mem_Icc]; omega
  rw [fiveShellPronicEnergyTo, hset,
    GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm,
    Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]

/-- Every partial final shell is controlled: finite shell energy is the full pronic domain. -/
theorem bounded_pronicNorm_fiveShellRow_iff (v : ℕ → ℝ) :
    (∃ C : ℝ, ∀ T : ℕ,
      GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm (fiveShellRow v) T ≤ C) ↔
      Summable (fun M : ℕ => v M ^ 2 / (5 : ℝ) ^ M) := by
  rw [← bounded_fiveShellPronicEnergy_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C ^ 2, fun N => ?_⟩
    calc
      _ ≤ fiveShellPronicEnergyTo v (N + 1) :=
        fiveShellPronicEnergyTo_monotone v (Nat.le_succ N)
      _ = _ := fiveShellPronicEnergyTo_succ v N
      _ ≤ C ^ 2 := pow_le_pow_left₀
        (GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm_nonneg _ _) (hC N) 2
  · rintro ⟨B, hB⟩
    refine ⟨Real.sqrt B, fun T => ?_⟩
    apply Real.le_sqrt_of_sq_le
    rw [← fiveShellPronicEnergyTo_succ]
    exact hB (T + 1)

end GaloisForLFunctions.BiarithmeticGeometry

