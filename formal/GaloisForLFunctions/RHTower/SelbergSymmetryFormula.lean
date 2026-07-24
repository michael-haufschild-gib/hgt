import GaloisForLFunctions.RHTower.SelbergSymmetryCore
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Selberg's symmetry formula

`|ψ(N)·log N + ∑_{k ≤ N} Λ(k)·ψ(⌊N/k⌋) − 2N·log N| ≤ 410·N`.

Unfolding `F₀ = ψ − id + 2γ` in the Tatuzawa–Iseki core bound: the linear
part becomes `∑_{m ≤ N} log m` through the von Mangoldt divisor swap, the
constant part becomes `2γ·ψ(N)`, and the Stirling sandwich, the Chebyshev
bound `ψ(N) ≤ (log 4 + 4)N`, and `1/2 < γ < 2/3` absorb every residual
into `26·N` on top of the core's `384·N`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- **Selberg's symmetry formula** with explicit constant:
`|ψ(N)log N + ∑_{k≤N} Λ(k)ψ(⌊N/k⌋) − 2N log N| ≤ 410N`. -/
theorem selberg_symmetry_formula (N : ℕ) (hN : 1 ≤ N) :
    |chebyshevPsi N * Real.log N
        + (∑ k ∈ Finset.Icc 1 N, vonMangoldt k * chebyshevPsi (N / k))
        - 2 * N * Real.log N|
      ≤ 410 * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- unfold the defect inside the core bound
  have hpsiN : psiDefect N = chebyshevPsi N - (N : ℝ)
      + 2 * Real.eulerMascheroniConstant := by
    simp only [psiDefect]
  have hsum : ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiDefect (N / k)
      = (∑ k ∈ Finset.Icc 1 N, vonMangoldt k * chebyshevPsi (N / k))
        - (∑ m ∈ Finset.Icc 1 N, Real.log m)
        + 2 * Real.eulerMascheroniConstant * chebyshevPsi N := by
    have hexp : ∀ k ∈ Finset.Icc 1 N,
        vonMangoldt k * psiDefect (N / k)
          = (vonMangoldt k * chebyshevPsi (N / k)
              - vonMangoldt k * ((N / k : ℕ) : ℝ))
            + 2 * Real.eulerMascheroniConstant * vonMangoldt k := by
      intro k _
      simp only [psiDefect]
      ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Mertens.log_summatory_eq N, ← Finset.mul_sum,
      show (∑ k ∈ Finset.Icc 1 N, vonMangoldt k) = chebyshevPsi N from rfl]
  have habs := abs_psiDefect_selberg_core N hN
  rw [hpsiN, hsum] at habs
  have hcore := abs_le.1 habs
  -- Stirling sandwich error
  have hlog3 := log_add_one_le_three_sqrt N hN
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hsqrtN : Real.sqrt N ≤ (N : ℝ) := by
    nlinarith [Real.sq_sqrt hN0.le, hsqrt1, Real.sqrt_nonneg (N : ℝ)]
  have hstep : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 / N := by
    have hdiv := Real.log_le_sub_one_of_pos
      (x := ((N : ℝ) + 1) / N) (by positivity)
    rw [Real.log_div (by positivity) hN0.ne'] at hdiv
    have heq : ((N : ℝ) + 1) / N - 1 = 1 / N := by
      field_simp
      ring
    linarith
  have hmulstep : (N : ℝ) * Real.log ((N : ℝ) + 1)
      ≤ (N : ℝ) * Real.log N + 1 := by
    have := mul_le_mul_of_nonneg_left hstep hN0.le
    have hone : (N : ℝ) * (1 / N) = 1 := by field_simp
    nlinarith [this, hone]
  have hEu : (∑ m ∈ Finset.Icc 1 N, Real.log m)
      - ((N : ℝ) * Real.log N - N) ≤ 4 * (N : ℝ) := by
    have hup := sum_log_le_stirling N hN
    have hexp : ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1)
        = (N : ℝ) * Real.log ((N : ℝ) + 1) + Real.log ((N : ℝ) + 1) := by
      ring
    nlinarith [hup, hexp, hmulstep, hlog3, hsqrt1, hsqrtN]
  have hEl : (1 : ℝ) ≤ (∑ m ∈ Finset.Icc 1 N, Real.log m)
      - ((N : ℝ) * Real.log N - N) := by
    have := stirling_le_sum_log N hN
    linarith
  -- Euler–Mascheroni and Chebyshev bounds
  have hγu : Real.eulerMascheroniConstant ≤ 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds.le
  have hγl : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlNle : Real.log N ≤ 3 * Real.sqrt N := by
    have hmono : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log hN0 (by linarith)
    linarith
  have hψ0 : 0 ≤ chebyshevPsi N :=
    Finset.sum_nonneg fun m _ => vonMangoldt_nonneg
  have hψu : chebyshevPsi N ≤ 7 * (N : ℝ) := by
    have hch := Mertens.sum_vonMangoldt_Icc_le N
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
      linarith
    have : (Real.log 4 + 4) * (N : ℝ) ≤ 7 * (N : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hN0.le
      linarith
    calc chebyshevPsi N = ∑ d ∈ Finset.Icc 1 N, vonMangoldt d := rfl
      _ ≤ (Real.log 4 + 4) * (N : ℝ) := hch
      _ ≤ 7 * (N : ℝ) := this
  -- bounded product terms
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
  · nlinarith [hcore.1, hEu, hEl, h2glN_u, h2glN_l, h2gP_u, h2gP_l, hN0]
  · nlinarith [hcore.2, hEu, hEl, h2glN_u, h2glN_l, h2gP_u, h2gP_l, hN0]

end RHTower
