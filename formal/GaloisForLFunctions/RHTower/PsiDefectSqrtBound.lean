import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory
import GaloisForLFunctions.RHTower.DirichletDivisorAsymptotic

/-!
# The square-root bound for the floor summatory of the `ψ` defect

For the defect `F₀(j) = ψ(j) − j + 2γ`, the floor summatory obeys

`|∑_{d ≤ k} F₀(⌊k/d⌋)| ≤ 24·√k`:

the `ψ` part telescopes to `∑_{m ≤ k} log m` (Stirling sandwich, error
`≤ 1 + log(k+1)`), the linear part is Dirichlet's divisor summatory
(error `≤ 20√k`), and the main terms `k log k − k` and
`k log k + (2γ−1)k − 2γk` cancel exactly.  With `log(k+1) ≤ 3√k` the
total is `24√k`.  This pointwise bound is the input the Tatuzawa–Iseki
identity converts into Selberg's symmetry formula.
-/

noncomputable section

namespace RHTower

open Finset

/-- The `ψ` defect `F₀(j) = ψ(j) − j + 2γ`. -/
def psiDefect (j : ℕ) : ℝ :=
  chebyshevPsi j - (j : ℝ) + 2 * Real.eulerMascheroniConstant

/-- `log(k+1) ≤ 3√k` for `k ≥ 1`. -/
theorem log_add_one_le_three_sqrt (k : ℕ) (hk : 1 ≤ k) :
    Real.log ((k : ℝ) + 1) ≤ 3 * Real.sqrt k := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hsq : Real.log ((k : ℝ) + 1)
      = 2 * Real.log (Real.sqrt ((k : ℝ) + 1)) := by
    rw [Real.log_sqrt hpos.le]
    ring
  have hlog : Real.log (Real.sqrt ((k : ℝ) + 1))
      ≤ Real.sqrt ((k : ℝ) + 1) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hpos)
  have hmono : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt k := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrt2 : Real.sqrt 2 ≤ 1.5 := by
    rw [show (1.5 : ℝ) = Real.sqrt (1.5 * 1.5) from
      (Real.sqrt_mul_self (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrtk : (0 : ℝ) ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hcomb : Real.sqrt 2 * Real.sqrt k ≤ 1.5 * Real.sqrt k :=
    mul_le_mul_of_nonneg_right hsqrt2 hsqrtk
  nlinarith [hsq, hlog, hmono, hcomb]

/-- **Square-root bound for the `ψ`-defect floor summatory**:
`|∑_{d ≤ k} (ψ − id + 2γ)(⌊k/d⌋)| ≤ 24√k`. -/
theorem abs_floorSummatory_psiDefect_le (k : ℕ) (hk : 1 ≤ k) :
    |floorSummatory psiDefect k| ≤ 24 * Real.sqrt k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt k := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  -- linear split of the floor summatory
  have hsplit : floorSummatory psiDefect k
      = (∑ m ∈ Finset.Icc 1 k, Real.log m)
        - (∑ d ∈ Finset.Icc 1 k, ((k / d : ℕ) : ℝ))
        + 2 * Real.eulerMascheroniConstant * (k : ℝ) := by
    have hpsi := floorSummatory_chebyshevPsi k
    simp only [floorSummatory, psiDefect] at hpsi ⊢
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Nat.card_Icc, show k + 1 - 1 = k from by omega, nsmul_eq_mul, hpsi]
    ring
  -- Stirling sandwich error
  have hstep : Real.log ((k : ℝ) + 1) ≤ Real.log k + 1 / k := by
    have hdiv := Real.log_le_sub_one_of_pos
      (x := ((k : ℝ) + 1) / k) (by positivity)
    rw [Real.log_div (by positivity) hkR.ne'] at hdiv
    have heq : ((k : ℝ) + 1) / k - 1 = 1 / k := by
      field_simp
      ring
    linarith
  have hmulstep : (k : ℝ) * Real.log ((k : ℝ) + 1)
      ≤ (k : ℝ) * Real.log k + 1 := by
    have := mul_le_mul_of_nonneg_left hstep hkR.le
    have hone : (k : ℝ) * (1 / k) = 1 := by
      field_simp
    nlinarith [this, hone]
  have hup := sum_log_le_stirling k hk
  have hlo := stirling_le_sum_log k hk
  have hlog3 := log_add_one_le_three_sqrt k hk
  -- Dirichlet divisor error
  have hdir := abs_le.1 (abs_sum_div_sub_dirichlet_le k hk)
  -- assemble
  rw [hsplit, abs_le]
  have hexp : ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)
      = (k : ℝ) * Real.log ((k : ℝ) + 1) + Real.log ((k : ℝ) + 1) := by
    ring
  constructor
  · nlinarith [hup, hlo, hdir.2, hlog3, hmulstep, hexp, hsqrt1]
  · nlinarith [hup, hlo, hdir.1, hlog3, hmulstep, hexp, hsqrt1]

end RHTower
