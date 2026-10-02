import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadFiniteSource
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadNegativeEscape

/-!
# Integer escape of the complete moving prime head

Late-prime cancellation controls the variation on each half-open integer
cell. The continuum sign obstruction therefore reaches literal integer
cutoffs, including the exact prime-square admission convention.
-/

noncomputable section
open Finset ArithmeticFunction
namespace RHTower

private theorem critical_defect_linear_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → |psiDefect k| ≤ C * k := by
  let C := Real.log 4 + 6 + 2 * |Real.eulerMascheroniConstant|
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro k hk
  have hpsi : chebyshevPsi k ≤ (Real.log 4 + 4) * (k : ℝ) :=
    Mertens.sum_vonMangoldt_Icc_le k
  have hpsi0 : 0 ≤ chebyshevPsi k :=
    sum_nonneg fun _ _ => vonMangoldt_nonneg
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  dsimp [C]
  rw [psiDefect]
  apply abs_le.mpr
  constructor <;> nlinarith [le_abs_self Real.eulerMascheroniConstant,
    neg_abs_le Real.eulerMascheroniConstant,
    mul_nonneg (abs_nonneg Real.eulerMascheroniConstant) (sub_nonneg.mpr hkr)]

/-- Uniform linear cell variation, after exact old-prime cancellation.
The bound is only used to transfer unbounded negative linear escape. -/
theorem criticalMovingPrimeHead_cell_variation :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : ℝ,
      (N : ℝ) ≤ x → x < (N + 1 : ℕ) →
      |criticalMovingPrimeHead x - criticalMovingPrimeHead N| ≤ D * N := by
  obtain ⟨C, hC, hb⟩ := critical_defect_linear_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN x hNx hxN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hx0 : 0 ≤ x := hN0.trans hNx
  have hsqN := Real.sq_sqrt hN0
  have hsqx := Real.sq_sqrt hx0
  have hsN := Real.sqrt_nonneg (N : ℝ)
  have hsx := Real.sqrt_nonneg x
  have hδ : 0 ≤ Real.sqrt x - Real.sqrt N := sub_nonneg.mpr (Real.sqrt_le_sqrt hNx)
  have hxN' : x < (N : ℝ) + 1 := by exact_mod_cast hxN
  have hδN : (Real.sqrt x - Real.sqrt N) * Real.sqrt N ≤ 1 := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt N)]
  have hsN1 : 1 ≤ Real.sqrt N := by nlinarith
  have hδ1 : Real.sqrt x - Real.sqrt N ≤ 1 := by nlinarith
  have hbase : (Real.sqrt x - Real.sqrt N) * |psiDefect N| ≤ C * N := by
    calc
      _ ≤ (Real.sqrt x - Real.sqrt N) * (C * N) :=
        mul_le_mul_of_nonneg_left (hb N (by omega)) hδ
      _ ≤ C * N := by nlinarith [mul_nonneg hC hN0]
  have hchild (p : ℕ) (hp : p ∈ criticalMovingLatePrimes N) :
      (Real.sqrt x - Real.sqrt N) * |psiDefect (N / p)| ≤ C := by
    obtain ⟨hpI, hpp, hpsq⟩ := mem_filter.mp hp
    have hpN := (mem_Icc.mp hpI).2
    have hk : 1 ≤ N / p := (Nat.le_div_iff_mul_le hpp.pos).mpr (by simpa using hpN)
    have hkp : N / p < p :=
      (Nat.div_lt_iff_lt_mul hpp.pos).mpr (by simpa [mul_comm] using hpsq)
    have hkm : N / p * p ≤ N := Nat.div_mul_le_self N p
    have hkk : (N / p) * (N / p) ≤ N := by nlinarith
    have hkkR : ((N / p : ℕ) : ℝ) ^ 2 ≤ N := by
      exact_mod_cast (by simpa [pow_two] using hkk : (N / p) ^ 2 ≤ N)
    have hkroot : ((N / p : ℕ) : ℝ) ≤ Real.sqrt N :=
      (Real.le_sqrt (Nat.cast_nonneg _) hN0).mpr hkkR
    calc
      _ ≤ (Real.sqrt x - Real.sqrt N) * (C * (N / p : ℕ)) :=
        mul_le_mul_of_nonneg_left (hb _ hk) hδ
      _ ≤ (Real.sqrt x - Real.sqrt N) * (C * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkroot hC) hδ
      _ ≤ C := by nlinarith [mul_le_mul_of_nonneg_left hδN hC]
  have hcard : (criticalMovingLatePrimes N).card ≤ N := by
    have h := card_le_card (filter_subset (fun p => p.Prime ∧ N < p * p) (Icc 1 N))
    simpa [criticalMovingLatePrimes] using h
  have hprime : (Real.sqrt x - Real.sqrt N) *
      |∑ p ∈ criticalMovingLatePrimes N, psiDefect (N / p)| ≤ C * N := by
    calc
      _ ≤ (Real.sqrt x - Real.sqrt N) *
          ∑ p ∈ criticalMovingLatePrimes N, |psiDefect (N / p)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hδ
      _ = ∑ p ∈ criticalMovingLatePrimes N,
          (Real.sqrt x - Real.sqrt N) * |psiDefect (N / p)| := mul_sum _ _ _
      _ ≤ ∑ _p ∈ criticalMovingLatePrimes N, C := sum_le_sum hchild
      _ = (criticalMovingLatePrimes N).card * C := by simp
      _ ≤ C * N := by
        have hcardR : ((criticalMovingLatePrimes N).card : ℝ) ≤ N := by exact_mod_cast hcard
        nlinarith
  rw [criticalMovingPrimeHead_cell hN hNx hxN]
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hδ]
  calc
    _ ≤ (Real.sqrt x - Real.sqrt N) *
        (|psiDefect N| + |∑ p ∈ criticalMovingLatePrimes N, psiDefect (N / p)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hδ
    _ ≤ 2 * C * N := by nlinarith

/-- Arbitrarily large negative linear excursions occur at integer cutoffs. -/
theorem criticalMovingPrimeHead_integer_negative_escape (C : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧ criticalMovingPrimeHead N < -C * N := by
  obtain ⟨D, hD, hd⟩ := criticalMovingPrimeHead_cell_variation
  let K : ℝ := max C 0 + D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨x, hxX, hx1, hxneg⟩ := criticalMovingPrimeHead_cofinal_negative_linear_escape
    K ((max N₀ 2 : ℕ) + 1)
  let N := ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N + 1 : ℕ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have hlarge : max N₀ 2 ≤ N := (Nat.le_floor_iff hx0).mpr (by linarith)
  have hN2 : 2 ≤ N := (le_max_right N₀ 2).trans hlarge
  refine ⟨N, (le_max_left N₀ 2).trans hlarge, hN2, ?_⟩
  have hvariation := hd N hN2 x hNx hxN
  have hdiff := neg_abs_le (criticalMovingPrimeHead x - criticalMovingPrimeHead N)
  have hmul := mul_le_mul_of_nonneg_left hNx hK
  have hC : C ≤ max C 0 := le_max_left C 0
  have hNr : (0 : ℝ) ≤ N := by positivity
  have hCN := mul_le_mul_of_nonneg_right hC hNr
  dsimp [K] at hxneg hmul
  linarith

end RHTower
