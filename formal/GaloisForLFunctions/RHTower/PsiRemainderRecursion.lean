import GaloisForLFunctions.RHTower.SelbergSymmetryFormula

/-!
# The remainder recursion of the Erdős–Selberg bootstrap

For `R(j) = ψ(j) − j`, the Tatuzawa–Iseki core bound sheds its
Euler–Mascheroni shift and becomes

`|R(N)·log N + ∑_{k ≤ N} Λ(k)·R(⌊N/k⌋)| ≤ 400·N`:

`ψ − id + 2γ = R + 2γ`, and the two shift terms `2γ·log N ≤ 4N` and
`2γ·ψ(N) ≤ 10N` are absorbed into the constant.  This is the seed
recursion of the Erdős–Selberg iteration: the weighted average of `R`
over the floor fibers controls `R(N)·log N`, so any uniform bound on
`|R|` improves under the `Λ`-average.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The `ψ` remainder `R(j) = ψ(j) − j`. -/
def psiRemainder (j : ℕ) : ℝ :=
  chebyshevPsi j - (j : ℝ)

theorem psiDefect_eq_psiRemainder_add (j : ℕ) :
    psiDefect j = psiRemainder j + 2 * Real.eulerMascheroniConstant := by
  simp only [psiDefect, psiRemainder]

/-- **Remainder recursion**:
`|R(N)·log N + ∑_{k ≤ N} Λ(k)·R(⌊N/k⌋)| ≤ 400·N`. -/
theorem abs_psiRemainder_recursion (N : ℕ) (hN : 1 ≤ N) :
    |psiRemainder N * Real.log N
        + ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiRemainder (N / k)|
      ≤ 400 * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- shed the Euler–Mascheroni shift from the core bound
  have hsum : ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiDefect (N / k)
      = (∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiRemainder (N / k))
        + 2 * Real.eulerMascheroniConstant * chebyshevPsi N := by
    have hexp : ∀ k ∈ Finset.Icc 1 N,
        vonMangoldt k * psiDefect (N / k)
          = vonMangoldt k * psiRemainder (N / k)
            + 2 * Real.eulerMascheroniConstant * vonMangoldt k := by
      intro k _
      rw [psiDefect_eq_psiRemainder_add]
      ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.mul_sum,
      show (∑ k ∈ Finset.Icc 1 N, vonMangoldt k) = chebyshevPsi N from rfl]
  have habs := abs_psiDefect_selberg_core N hN
  rw [psiDefect_eq_psiRemainder_add, hsum] at habs
  have hcore := abs_le.1 habs
  -- shift-term bounds
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hsqrtN : Real.sqrt N ≤ (N : ℝ) := by
    nlinarith [Real.sq_sqrt hN0.le, hsqrt1, Real.sqrt_nonneg (N : ℝ)]
  have hlog3 := log_add_one_le_three_sqrt N hN
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlNle : Real.log N ≤ 3 * Real.sqrt N := by
    have hmono : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log hN0 (by linarith)
    linarith
  have hγu : Real.eulerMascheroniConstant ≤ 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds.le
  have hγl : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hψ0 : 0 ≤ chebyshevPsi N :=
    Finset.sum_nonneg fun m _ => vonMangoldt_nonneg
  have hψu : chebyshevPsi N ≤ 7 * (N : ℝ) := by
    have hch := Mertens.sum_vonMangoldt_Icc_le N
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
      linarith
    have hbound : (Real.log 4 + 4) * (N : ℝ) ≤ 7 * (N : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hN0.le
      linarith
    calc chebyshevPsi N = ∑ d ∈ Finset.Icc 1 N, vonMangoldt d := rfl
      _ ≤ (Real.log 4 + 4) * (N : ℝ) := hch
      _ ≤ 7 * (N : ℝ) := hbound
  have h2glN_u : 2 * Real.eulerMascheroniConstant * Real.log N
      ≤ 4 * (N : ℝ) := by
    have h1 : 2 * Real.eulerMascheroniConstant * Real.log N
        ≤ 2 * (2 / 3) * Real.log N := by
      apply mul_le_mul_of_nonneg_right _ hlN0
      linarith
    nlinarith [hlNle, hsqrtN, hsqrt1]
  have h2glN_l : 0 ≤ 2 * Real.eulerMascheroniConstant * Real.log N := by
    positivity
  have h2gP_u : 2 * Real.eulerMascheroniConstant * chebyshevPsi N
      ≤ 10 * (N : ℝ) := by
    have h1 : 2 * Real.eulerMascheroniConstant * chebyshevPsi N
        ≤ 2 * (2 / 3) * chebyshevPsi N := by
      apply mul_le_mul_of_nonneg_right _ hψ0
      linarith
    nlinarith [hψu]
  have h2gP_l : 0 ≤ 2 * Real.eulerMascheroniConstant * chebyshevPsi N := by
    positivity
  -- assemble
  rw [abs_le]
  constructor
  · nlinarith [hcore.1, h2glN_u, h2glN_l, h2gP_u, h2gP_l]
  · nlinarith [hcore.2, h2glN_u, h2glN_l, h2gP_u, h2gP_l]

end RHTower
