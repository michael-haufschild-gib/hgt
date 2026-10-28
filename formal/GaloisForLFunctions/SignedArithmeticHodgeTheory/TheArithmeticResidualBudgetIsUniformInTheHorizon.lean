import GaloisForLFunctions.SignedArithmeticHodgeTheory.OneArithmeticRemainderControlsEveryRamanujanResidual
import GaloisForLFunctions.RHTower.MertensConstantAndCesaroIntegerLagBridge
import GaloisForLFunctions.PNTPlus.Wiener

/-!
# A horizon-uniform arithmetic residual budget

Quantitative Mertens decay gives one logarithmic envelope for the actual row
remainder. Floor roundoff transfers its square to the summable Wiener kernel.
The resulting bound is uniform in the horizon, conductors and coefficients.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open RenormalizedArithmeticPotentialTheory

private theorem exp_sqrt_weight_le {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L) :
    Real.exp (-c * Real.sqrt L) * (1 + L) ≤ 1 + 2 / c ^ 2 := by
  have hx : 0 ≤ c * Real.sqrt L := mul_nonneg hc.le (Real.sqrt_nonneg L)
  have hquad : c ^ 2 * L / 2 ≤ Real.exp (c * Real.sqrt L) := by
    have h := Real.pow_div_factorial_le_exp (c * Real.sqrt L) hx 2
    simpa only [mul_pow, Real.sq_sqrt hL, Nat.factorial_two, Nat.cast_ofNat] using h
  have hexp : Real.exp (c * Real.sqrt L) * Real.exp (-c * Real.sqrt L) = 1 := by
    rw [← Real.exp_add]
    simp only [neg_mul, add_neg_cancel, Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_right hquad (Real.exp_pos (-c * Real.sqrt L)).le
  rw [hexp] at hmul
  have hweighted : L * Real.exp (-c * Real.sqrt L) ≤ 2 / c ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    nlinarith only [hmul]
  have hsmall : Real.exp (-c * Real.sqrt L) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [hx])
  nlinarith only [hweighted, hsmall]

/-- The actual common remainder has a global inverse-logarithmic envelope. -/
theorem exists_primeMertensRemainder_log_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 0 < y →
      primeMertensRemainderProfile y ≤ C / (1 + Real.log y) := by
  obtain ⟨c, hc, A, hA, hbound⟩ :=
    GaloisForLFunctions.RHTower.exists_global_mertensDeviation_exp_sqrt_log_bound
  refine ⟨A * (1 + 2 / c ^ 2) + 1, by positivity, ?_⟩
  intro y hy
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hlog : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
  have hden : 0 < 1 + Real.log (y : ℝ) := by positivity
  have hM := hbound y hy
  change |mertensSum y - Real.log y + Real.eulerMascheroniConstant| ≤
    A * Real.exp (-c * Real.sqrt (Real.log y)) at hM
  have hinv : 1 / (y : ℝ) * (1 + Real.log y) ≤ 1 := by
    calc
      _ = (1 + Real.log y) / (y : ℝ) := by ring
      _ ≤ 1 := (div_le_one hy0).mpr (by linarith [Real.log_le_sub_one_of_pos hy0])
  apply (le_div_iff₀ hden).mpr
  calc
    primeMertensRemainderProfile y * (1 + Real.log y) =
        |mertensSum y - Real.log y + Real.eulerMascheroniConstant| * (1 + Real.log y) +
          1 / (y : ℝ) * (1 + Real.log y) := by
      rw [primeMertensRemainderProfile, add_mul]
    _ ≤ A * Real.exp (-c * Real.sqrt (Real.log y)) * (1 + Real.log y) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_right hM hden.le) hinv
    _ = A * (Real.exp (-c * Real.sqrt (Real.log y)) * (1 + Real.log y)) + 1 := by ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (exp_sqrt_weight_le hc hlog) hA) le_rfl

private theorem floor_log_kernel_comparison {N n : ℕ} (hn : n ∈ Icc 1 N) :
    1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2 ≤
      2 * (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 := by
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  have hnN : n ≤ N := (mem_Icc.mp hn).2
  have hN0 : 0 < N := hn0.trans_le hnN
  have hy : 0 < N / n := Nat.div_pos hnN hn0
  have hyn : (1 : ℝ) ≤ ((N / n : ℕ) : ℝ) := by exact_mod_cast hy
  have hinv : 1 / ((N / n : ℕ) : ℝ) ≤ 1 := div_le_self zero_le_one hyn
  have hr := roundoff_le hn0 hnN
  have hlog : 0 ≤ Real.log ((N / n : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hquot : Real.log ((n : ℝ) / N) = Real.log n - Real.log N :=
    Real.log_div (by exact_mod_cast hn0.ne') (by exact_mod_cast hN0.ne')
  have hnonpos : Real.log ((n : ℝ) / N) ≤ 0 := by
    rw [hquot]
    linarith only [hr.1, hlog]
  have habs : |Real.log ((n : ℝ) / N)| ≤ 1 + Real.log ((N / n : ℕ) : ℝ) := by
    rw [abs_of_nonpos hnonpos, hquot]
    linarith only [hr.2, hinv]
  have hα0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hα1 : 1 / (2 * Real.pi) ≤ 1 := one_div_two_pi_mem_Ioo.2.le
  have hα : |1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)| ≤
      1 + Real.log ((N / n : ℕ) : ℝ) := by
    rw [abs_mul, abs_of_nonneg hα0]
    exact (mul_le_mul_of_nonneg_right hα1 (abs_nonneg _)).trans (by simpa using habs)
  have hsq := mul_le_mul hα hα (abs_nonneg _) (by positivity)
  rw [← sq, sq_abs, ← sq] at hsq
  nlinarith only [hsq, hlog]

private theorem wiener_constant_kernel_sum_le {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Icc 1 N, 1 / (n : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) ≤
        1 + 2 * Real.pi ^ 2 := by
  have hcheby : chebyWith 1 (fun _ : ℕ => (1 : ℂ)) := by
    intro n
    simp [cumsum]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) := by
    simpa only [norm_one, one_div] using
      limiting_fourier_lim1_aux ⟨1, hcheby⟩ hN0 1 zero_le_one
  have hfull : (∑' n : ℕ, 1 / (n : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) ≤
        1 + 2 * Real.pi ^ 2 := by
    simpa only [norm_one, one_mul] using bound_sum_log' hcheby hN1
  exact (Summable.sum_le_tsum (Icc 1 N) (fun n _ => by positivity) hsum).trans hfull

/-- One absolute constant pays the arithmetic remainder at every horizon. -/
theorem exists_uniform_primeMertensSquareBudget :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, primeMertensSquareBudget N ≤ B := by
  obtain ⟨C, hC, hbound⟩ := exists_primeMertensRemainder_log_envelope
  refine ⟨2 * C ^ 2 * (1 + 2 * Real.pi ^ 2), by positivity, ?_⟩
  intro N
  by_cases hN : N = 0
  · subst N
    simp only [primeMertensSquareBudget, Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), sum_empty]
    positivity
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have hrow : ∀ n ∈ Icc 1 N,
      primeMertensRemainderProfile (N / n) ^ 2 / (n : ℝ) ≤
        2 * C ^ 2 * (1 / (n : ℝ) *
          (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) := by
    intro n hn
    have hn0 : 0 < n := (mem_Icc.mp hn).1
    have hy : 0 < N / n := Nat.div_pos (mem_Icc.mp hn).2 hn0
    have hlog : 0 ≤ Real.log ((N / n : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hden : 0 < 1 + Real.log ((N / n : ℕ) : ℝ) := by positivity
    have hf0 : 0 ≤ primeMertensRemainderProfile (N / n) := by
      unfold primeMertensRemainderProfile
      positivity
    have hf := hbound (N / n) hy
    have hfsq := mul_le_mul hf hf hf0 (by positivity)
    rw [← sq, ← sq, div_pow] at hfsq
    have hk := floor_log_kernel_comparison hn
    have hkpos : 0 < 1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2 := by positivity
    have hratio : C ^ 2 / (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 ≤
        2 * C ^ 2 / (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hden) hkpos).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hk (sq_nonneg C)]
    calc
      _ ≤ (2 * C ^ 2 /
          (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)) / (n : ℝ) :=
        div_le_div_of_nonneg_right (hfsq.trans hratio) (Nat.cast_nonneg n)
      _ = _ := by ring
  calc
    primeMertensSquareBudget N ≤ ∑ n ∈ Icc 1 N,
        2 * C ^ 2 * (1 / (n : ℝ) *
          (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) :=
      sum_le_sum hrow
    _ = 2 * C ^ 2 * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) *
        (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹ := by
      rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (wiener_constant_kernel_sum_le hN0) (by positivity)

/-- All finite Ramanujan families share a horizon-independent residual constant. -/
theorem exists_uniform_ramanujanPrimeResidual_family_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (S : Finset ℕ+) (c : ℕ+ → ℝ) (N : ℕ),
      (∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPrimeResidual m N n) ^ 2) ≤
        B * (∑ m ∈ S, ramanujanResidualConductorCost m ^ 2) *
          (∑ m ∈ S, c m ^ 2) := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_primeMertensSquareBudget
  refine ⟨B, hB, fun S c N => ?_⟩
  calc
    _ ≤ (∑ m ∈ S, c m ^ 2) * (∑ m ∈ S, ramanujanResidualConductorCost m ^ 2) *
        primeMertensSquareBudget N := ramanujanPrimeResidual_family_sq_le S c N
    _ ≤ (∑ m ∈ S, c m ^ 2) * (∑ m ∈ S, ramanujanResidualConductorCost m ^ 2) * B :=
      mul_le_mul_of_nonneg_left (hbound N)
        (mul_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _))
    _ = _ := by ring

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_primeMertensRemainder_log_envelope
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_uniform_primeMertensSquareBudget
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_uniform_ramanujanPrimeResidual_family_bound
