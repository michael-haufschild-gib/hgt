import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory

/-!
# Prime-cell sign for the critical FU Mertens coordinate

The completed FU reporter requires cancellation in a moving triangular window.  This file records
an unconditional obstruction to cellwise estimates: at every prime `p ≥ 27`, the literal
Mertens--Gamma coordinate has a positive jump of size at least `log p / (2p)`.  Thus any valid
FU producer must transport this atomic excess against later cells; neither absolute variation nor
same-cell prime--log cancellation can close the reporter.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact critical Mertens--Gamma coordinate underlying the FU checkpoint reporter.  It is kept
in this narrow module so its local arithmetic increments can be used without importing the full
variation criterion. -/
def suzukiCheckpointCriticalMertensDeviationCore (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 (N + 2),
      ArithmeticFunction.vonMangoldt k / (k : ℝ)) -
    Real.log ((N + 2 : ℕ) : ℝ) + Real.eulerMascheroniConstant

/-- One-cell increment of the literal critical Mertens--Gamma coordinate. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_succ_sub (N : ℕ) :
    suzukiCheckpointCriticalMertensDeviationCore (N + 1) -
        suzukiCheckpointCriticalMertensDeviationCore N =
      ArithmeticFunction.vonMangoldt (N + 3) / ((N + 3 : ℕ) : ℝ) -
        (Real.log ((N + 3 : ℕ) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ)) := by
  unfold suzukiCheckpointCriticalMertensDeviationCore
  rw [show N + 1 + 2 = N + 2 + 1 by omega,
    Finset.sum_Icc_succ_top (a := 1) (b := N + 2) (by omega)
      (fun k : ℕ => ArithmeticFunction.vonMangoldt k / (k : ℝ))]
  ring

private theorem three_le_log_of_twentySeven_le {p : ℕ} (hp : 27 ≤ p) :
    (3 : ℝ) ≤ Real.log p := by
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hlog27 : (3 : ℝ) < Real.log 27 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith
  exact (le_of_lt hlog27).trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hp))

/-- At every sufficiently large prime, the actual critical Mertens coordinate has a positive
atomic cell which dominates its simultaneous logarithmic counterjump.  Consequently, any uniform
FU bound must use genuinely cross-cell signed transport. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_cell_lower
    {p : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p) :
    Real.log (p : ℝ) / (2 * p) ≤
      suzukiCheckpointCriticalMertensDeviationCore (p - 2) -
        suzukiCheckpointCriticalMertensDeviationCore (p - 3) := by
  have hp1 : 1 ≤ p := hp.one_le
  have hlog : (3 : ℝ) ≤ Real.log p :=
    three_le_log_of_twentySeven_le hp27
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hratio : 2 * (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log p := by
    rw [div_le_iff₀ hden]
    have hthree : 2 * (p : ℝ) ≤ 3 * ((p : ℝ) - 1) := by
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
      nlinarith
    exact hthree.trans
      (mul_le_mul_of_nonneg_right hlog hden.le)
  have hcontinuum :
      Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) ≤
        1 / ((p - 1 : ℕ) : ℝ) := by
    have h := log_succ_sub_log_le (j := p - 1) (by omega)
    rw [Nat.cast_sub hp1] at h
    norm_num at h
    rw [Nat.cast_sub hp1]
    norm_num [one_div] at h ⊢
    linarith
  have hcomp : 1 / ((p - 1 : ℕ) : ℝ) ≤
      Real.log (p : ℝ) / (2 * p) := by
    rw [Nat.cast_sub hp1]
    norm_num
    rw [← one_div]
    apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 2 * p)).2
    exact (div_le_iff₀ hden).mp (by simpa using hratio)
  have hstep : Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) ≤
      Real.log (p : ℝ) / (2 * p) := hcontinuum.trans hcomp
  rw [show p - 2 = p - 3 + 1 by omega,
    suzukiCheckpointCriticalMertensDeviationCore_succ_sub (p - 3),
    show p - 3 + 3 = p by omega,
    show p - 3 + 2 = p - 1 by omega,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  calc
    Real.log (p : ℝ) / (2 * p) =
        Real.log (p : ℝ) / p - Real.log (p : ℝ) / (2 * p) := by
          field_simp
          ring
    _ ≤ Real.log (p : ℝ) / p -
        (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) :=
      sub_le_sub_left hstep _

/-- Prime critical-Mertens cells are strictly positive beyond the fixed threshold. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_cell_pos
    {p : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p) :
    0 < suzukiCheckpointCriticalMertensDeviationCore (p - 2) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) := by
  have hpReal : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 1 < p by omega)
  apply lt_of_lt_of_le
    (div_pos (Real.log_pos hpReal)
      (by positivity : (0 : ℝ) < 2 * p))
  exact suzukiCheckpointCriticalMertensDeviationCore_prime_cell_lower hp hp27

end

end RHTower
