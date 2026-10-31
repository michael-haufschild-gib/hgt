import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramLogarithmicPlateau
import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheArithmeticResidualBudgetIsUniformInTheHorizon
import GaloisForLFunctions.RHTower.VonMangoldtMinusOneAbscissa

/-!
# A logarithmic packet cost for the scalar prime residual

Bounded harmonic Gram discrepancy transfers increasing scalar weights to
conductor packets by Abel summation. The common Mertens remainder has a
summable logarithmic envelope, giving a norm bound uniform in the horizon.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory SignedArithmeticHodgeTheory ArithmeticElectrostatics

private theorem sum_range_succ_eq_Icc (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, f (n + 1)) = ∑ n ∈ Icc 1 N, f n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- Increasing weights bounded by one preserve a logarithmic packet Gram discrepancy. -/
theorem abs_harmonicPacket_monotone_weight_le {Q : ℕ} (hQ : 2 ≤ Q)
    (N : ℕ) (a w : ℕ → ℝ)
    (hw0 : ∀ n, 1 ≤ n → 0 ≤ w n)
    (hwmono : ∀ n, 1 ≤ n → w n ≤ w (n + 1))
    (hw1 : ∀ n, 1 ≤ n → w n ≤ 1) :
    |∑ n ∈ Icc 1 N, w n *
      (((∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 -
        ∑ m ∈ Icc 1 Q, a m ^ 2) / (n : ℝ))| ≤
      32 * (1 + Real.log Q) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let M : ℝ := ∑ m ∈ Icc 1 Q, a m ^ 2
  let F : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n
  let L : ℝ := 6 * Real.log Q + Real.log 4 + 5
  let T := torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))
  have hM : 0 ≤ M := sum_nonneg fun m _ => sq_nonneg (a m)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hT : |T| ≤ L * M := by
    have h := abs_harmonicGram_torsion_remainder_le_log hQ 0 a
    simpa only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty, harmonic_zero,
      Rat.cast_zero, zero_mul, sub_zero, zero_add] using h
  have hpartial (k : ℕ) :
      |∑ j ∈ range k, (F (j + 1) ^ 2 - M) / ((j + 1 : ℕ) : ℝ)| ≤ 2 * L * M := by
    have hR := abs_harmonicGram_torsion_remainder_le_log hQ k a
    change |(∑ n ∈ Icc 1 k, F n ^ 2 / (n : ℝ)) - (harmonic k : ℝ) * M + T| ≤ L * M at hR
    have hconst : (∑ n ∈ Icc 1 k, M / (n : ℝ)) = (harmonic k : ℝ) * M := by
      calc
        _ = (∑ n ∈ Icc 1 k, 1 / (n : ℝ)) * M := by
          rw [sum_mul]
          apply sum_congr rfl
          intro n _
          ring
        _ = _ := by rw [_root_.RHTower.Sieve.sum_Icc_one_div_eq_harmonic]
    rw [sum_range_succ_eq_Icc (fun n => (F n ^ 2 - M) / (n : ℝ)) k]
    simp only [sub_div, sum_sub_distrib]
    rw [hconst]
    calc
      _ = |((∑ n ∈ Icc 1 k, F n ^ 2 / (n : ℝ)) - (harmonic k : ℝ) * M + T) - T| := by
        rw [add_sub_cancel_right]
      _ ≤ |(∑ n ∈ Icc 1 k, F n ^ 2 / (n : ℝ)) - (harmonic k : ℝ) * M + T| + |T| := abs_sub _ _
      _ ≤ L * M + L * M := add_le_add hR hT
      _ = _ := by ring
  have h := _root_.RHTower.abs_sum_mul_le_of_bounded_partial_mono
    (g := fun j => (F (j + 1) ^ 2 - M) / ((j + 1 : ℕ) : ℝ))
    (w := fun j => w (j + 1)) N hpartial
    (fun j => hw0 (j + 1) (by omega)) (fun j => hwmono (j + 1) (by omega))
  rw [sum_range_succ_eq_Icc (fun n => w n * ((F n ^ 2 - M) / (n : ℝ))) N] at h
  have hend : 2 * (2 * L * M) * w (N - 1 + 1) ≤ 4 * L * M := by
    have h := mul_le_mul_of_nonneg_left (hw1 (N - 1 + 1) (by omega))
      (show 0 ≤ 2 * (2 * L * M) by positivity)
    nlinarith only [h]
  have hfour := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
  have hcoef : 4 * L ≤ 32 * (1 + Real.log Q) := by
    dsimp only [L]
    linarith only [hfour, Real.log_natCast_nonneg Q]
  exact (h.trans hend).trans (mul_le_mul_of_nonneg_right hcoef hM)

private def primeLogKernel (N n : ℕ) : ℝ :=
  (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹

private theorem primeLogKernel_nonneg (N n : ℕ) : 0 ≤ primeLogKernel N n := by
  unfold primeLogKernel
  positivity

private theorem primeLogKernel_le_one (N n : ℕ) : primeLogKernel N n ≤ 1 := by
  unfold primeLogKernel
  exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _))

private theorem primeLogKernel_mono {N m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hnN : n ≤ N) :
    primeLogKernel N m ≤ primeLogKernel N n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hm.trans hmn
  have hNR : (0 : ℝ) < N := by exact_mod_cast (hm.trans hmn).trans hnN
  have hlog : Real.log ((m : ℝ) / N) ≤ Real.log ((n : ℝ) / N) :=
    Real.log_le_log (div_pos hmR hNR)
      (div_le_div_of_nonneg_right (by exact_mod_cast hmn) hNR.le)
  have htop : Real.log ((n : ℝ) / N) ≤ 0 :=
    Real.log_nonpos (div_nonneg hnR.le hNR.le) ((div_le_one hNR).mpr (by exact_mod_cast hnN))
  have hα : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hab := mul_le_mul_of_nonneg_left hlog hα
  have hb := mul_nonpos_of_nonneg_of_nonpos hα htop
  have hsq : (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2 ≤
      (1 / (2 * Real.pi) * Real.log ((m : ℝ) / N)) ^ 2 := by
    nlinarith only [hab, hb]
  unfold primeLogKernel
  exact inv_anti₀ (by positivity) (add_le_add (le_refl 1) hsq)

/-- Wiener's logarithmic kernel has uniformly bounded scalar harmonic mass. -/
private theorem primeLogKernel_sum_le {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Icc 1 N, primeLogKernel N n / (n : ℝ)) ≤ 1 + 2 * Real.pi ^ 2 := by
  have hcheby : chebyWith 1 (fun _ : ℕ => (1 : ℂ)) := by
    intro n
    simp [cumsum]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) * primeLogKernel N n) := by
    simpa only [norm_one, one_div, primeLogKernel] using
      limiting_fourier_lim1_aux ⟨1, hcheby⟩ hN0 1 zero_le_one
  have hfull : (∑' n : ℕ, 1 / (n : ℝ) * primeLogKernel N n) ≤
      1 + 2 * Real.pi ^ 2 := by
    simpa only [norm_one, one_mul, primeLogKernel] using bound_sum_log' hcheby hN1
  have h := (Summable.sum_le_tsum (Icc 1 N)
    (fun n _ => mul_nonneg (by positivity) (primeLogKernel_nonneg N n)) hsum).trans hfull
  simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_one] using h

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

private theorem scalarPrimeError_sq_le_kernel {C : ℝ}
    (hbound : ∀ y : ℕ, 0 < y → primeMertensRemainderProfile y ≤ C / (1 + Real.log y))
    {N n : ℕ} (hn : n ∈ Icc 1 N) :
    (mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) ^ 2 ≤
      2 * C ^ 2 * primeLogKernel N n := by
  have hn0 := (mem_Icc.mp hn).1
  have hy : 0 < N / n := Nat.div_pos (mem_Icc.mp hn).2 hn0
  have hr := roundoff_le hn0 (mem_Icc.mp hn).2
  have herr : |mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)| ≤
      primeMertensRemainderProfile (N / n) := by
    have he := abs_sub
      (mertensSum (N / n) - Real.log (N / n : ℕ) + Real.eulerMascheroniConstant)
      (Real.log N - Real.log (N / n : ℕ) - Real.log n)
    rw [abs_of_nonneg hr.1] at he
    unfold primeMertensRemainderProfile
    have hid : mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant) =
        (mertensSum (N / n) - Real.log (N / n : ℕ) + Real.eulerMascheroniConstant) -
          (Real.log N - Real.log (N / n : ℕ) - Real.log n) := by ring
    rw [hid]
    exact he.trans (add_le_add le_rfl hr.2)
  have hden : 0 < 1 + Real.log ((N / n : ℕ) : ℝ) := by positivity
  have hs := mul_self_le_mul_self (abs_nonneg _ ) (herr.trans (hbound _ hy))
  rw [← sq, sq_abs, ← sq, div_pow] at hs
  have hk := floor_log_kernel_comparison hn
  have hkpos : 0 < 1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2 := by positivity
  have hratio : C ^ 2 / (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 ≤
      2 * C ^ 2 / (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hden) hkpos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hk (sq_nonneg C)]
  simpa only [primeLogKernel, div_eq_mul_inv] using hs.trans hratio

/-- The actual scalar prime-row residual has only a logarithmic conductor cost, uniformly in every horizon. -/
theorem exists_scalarPrimeResidual_packet_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q N : ℕ, 2 ≤ Q → 2 ≤ N → ∀ a : ℕ → ℝ,
      (∑ n ∈ Icc 1 N,
        (mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) ^ 2 *
          (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) / Real.log N ≤
        C * (1 + Real.log Q) / Real.log N * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_primeMertensRemainder_log_envelope
  refine ⟨2 * C ^ 2 * (33 + 2 * Real.pi ^ 2), by positivity, ?_⟩
  intro Q N hQ hN a
  let M : ℝ := ∑ m ∈ Icc 1 Q, a m ^ 2
  let F : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n
  -- Clipping makes the kernel increasing on all natural indices without changing its horizon values.
  let w : ℕ → ℝ := fun n => primeLogKernel N (min (max n 1) N)
  have hM : 0 ≤ M := sum_nonneg fun m _ => sq_nonneg (a m)
  have hw (n : ℕ) (hn : n ∈ Icc 1 N) : w n = primeLogKernel N n := by
    simp only [w, max_eq_left (mem_Icc.mp hn).1, min_eq_left (mem_Icc.mp hn).2]
  have hmono (n : ℕ) (_hn : 1 ≤ n) : w n ≤ w (n + 1) := by
    apply primeLogKernel_mono
    · exact le_min (le_max_right _ _) (by omega)
    · exact min_le_min (max_le_max (Nat.le_succ n) le_rfl) le_rfl
    · exact min_le_right _ _
  have habel := (abs_le.mp (abs_harmonicPacket_monotone_weight_le hQ N a w
    (fun n _ => primeLogKernel_nonneg _ _) hmono
    (fun n _ => primeLogKernel_le_one _ _))).2
  have hident : (∑ n ∈ Icc 1 N, w n * ((F n ^ 2 - M) / (n : ℝ))) =
      (∑ n ∈ Icc 1 N, primeLogKernel N n * F n ^ 2 / (n : ℝ)) -
        (∑ n ∈ Icc 1 N, primeLogKernel N n / (n : ℝ)) * M := by
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    rw [hw n hn]
    ring
  change (∑ n ∈ Icc 1 N, w n * ((F n ^ 2 - M) / (n : ℝ))) ≤
    32 * (1 + Real.log Q) * M at habel
  rw [hident] at habel
  have hscalar := mul_le_mul_of_nonneg_right (primeLogKernel_sum_le (by omega : 0 < N)) hM
  have hkernel : (∑ n ∈ Icc 1 N, primeLogKernel N n * F n ^ 2 / (n : ℝ)) ≤
      (33 + 2 * Real.pi ^ 2) * (1 + Real.log Q) * M := by
    have hlogM := mul_nonneg (Real.log_natCast_nonneg Q) hM
    have hextra := mul_nonneg (show 0 ≤ 1 + 2 * Real.pi ^ 2 by positivity) hlogM
    nlinarith only [habel, hscalar, hextra]
  have hsum : (∑ n ∈ Icc 1 N,
      (mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) ^ 2 *
        F n ^ 2 / (n : ℝ)) ≤
      2 * C ^ 2 * ((33 + 2 * Real.pi ^ 2) * (1 + Real.log Q) * M) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, 2 * C ^ 2 * primeLogKernel N n * F n ^ 2 / (n : ℝ) := by
        apply sum_le_sum
        intro n hn
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (scalarPrimeError_sq_le_kernel hbound hn) (sq_nonneg _))
          (Nat.cast_nonneg n)
      _ = 2 * C ^ 2 * (∑ n ∈ Icc 1 N, primeLogKernel N n * F n ^ 2 / (n : ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hkernel (by positivity)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  exact (div_le_div_of_nonneg_right hsum hlog.le).trans_eq (by ring)

#print axioms abs_harmonicPacket_monotone_weight_le
#print axioms exists_scalarPrimeResidual_packet_sq_le

end GaloisForLFunctions.SuccessorShellArithmetic
