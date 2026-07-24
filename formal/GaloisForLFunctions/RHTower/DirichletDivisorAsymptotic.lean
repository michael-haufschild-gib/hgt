import GaloisForLFunctions.RHTower.SymmetricHyperbolaFloorCount
import GaloisForLFunctions.RHTower.HarmonicLogMascheroni

/-!
# Dirichlet's divisor asymptotic with square-root error

`|∑_{d ≤ N} ⌊N/d⌋ − N·log N − (2γ − 1)·N| ≤ 20·√N`.

The symmetric hyperbola count reflects the summatory into twice the strip
`d ≤ ⌊√N⌋` minus the square `⌊√N⌋²`; on the strip each floor is within `1`
of the real quotient, the harmonic sum carries the Euler–Mascheroni error
`O(1/⌊√N⌋)`, and `2·log⌊√N⌋` differs from `log N` by at most `2/⌊√N⌋`.
Every error source is `O(√N)` with the explicit constant `20`.
-/

noncomputable section

namespace RHTower

open Finset

/-- **Dirichlet's divisor asymptotic**:
`|∑_{d ≤ N} ⌊N/d⌋ − N log N − (2γ−1)N| ≤ 20√N`. -/
theorem abs_sum_div_sub_dirichlet_le (N : ℕ) (hN : 1 ≤ N) :
    |(∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ)) - (N : ℝ) * Real.log N
        - (2 * Real.eulerMascheroniConstant - 1) * N| ≤ 20 * Real.sqrt N := by
  have hs1 : 1 ≤ Nat.sqrt N := by
    by_contra hcon
    have hlt := Nat.lt_succ_sqrt N
    have hs0 : Nat.sqrt N = 0 := by omega
    rw [hs0] at hlt
    omega
  set s := Nat.sqrt N with hsdef
  have hsq : s * s ≤ N := Nat.sqrt_le N
  have hsq' : N ≤ s * s + 2 * s := by
    have hlt : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
    have hexp : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by ring
    omega
  have hs0R : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hcastsq : (s : ℝ) * s ≤ (N : ℝ) := by exact_mod_cast hsq
  have hcastsq' : (N : ℝ) ≤ (s : ℝ) * s + 2 * s := by exact_mod_cast hsq'
  have hsqrts : (s : ℝ) ≤ Real.sqrt N := by
    rw [show (s : ℝ) = Real.sqrt ((s : ℝ) * s) from
      (Real.sqrt_mul_self hs0R.le).symm]
    exact Real.sqrt_le_sqrt hcastsq
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hNs : (N : ℝ) / s ≤ Real.sqrt N + 3 := by
    rw [div_le_iff₀ hs0R]
    have hss : (s : ℝ) * s ≤ (s : ℝ) * Real.sqrt N :=
      mul_le_mul_of_nonneg_left hsqrts hs0R.le
    nlinarith [hss, hcastsq', hs0R.le]
  -- the symmetric hyperbola identity, cast to ℝ
  have hidR : (∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ)) + (s : ℝ) * s
      = 2 * ∑ d ∈ Finset.Icc 1 s, ((N / d : ℕ) : ℝ) := by
    exact_mod_cast sum_div_add_sqrt_sq N
  -- each floor on the strip is within 1 of the real quotient
  have hfloor : ∀ d ∈ Finset.Icc 1 s,
      |((N / d : ℕ) : ℝ) - (N : ℝ) / d| ≤ 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0R : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hkey : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast Nat.div_add_mod N d
    have hsplit : (N : ℝ) / d = ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) / d := by
      rw [← hkey, add_div, mul_div_cancel_left₀ _ hd0R.ne']
    have heq : ((N / d : ℕ) : ℝ) - (N : ℝ) / d
        = -(((N % d : ℕ) : ℝ) / d) := by
      rw [hsplit]
      ring
    rw [heq, abs_neg, abs_div,
      abs_of_nonneg (a := ((N % d : ℕ) : ℝ)) (Nat.cast_nonneg _),
      abs_of_pos hd0R, div_le_one hd0R]
    have hmod : N % d < d := Nat.mod_lt N (by omega)
    exact_mod_cast hmod.le
  -- strip sum vs harmonic sum
  have hNHs : ∑ d ∈ Finset.Icc 1 s, (N : ℝ) / d
      = (N : ℝ) * ∑ i ∈ Finset.Icc 1 s, ((i : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [div_eq_mul_inv]
  have hSsum : |(∑ d ∈ Finset.Icc 1 s, ((N / d : ℕ) : ℝ))
      - (N : ℝ) * ∑ i ∈ Finset.Icc 1 s, ((i : ℝ))⁻¹| ≤ (s : ℝ) := by
    rw [← hNHs, ← Finset.sum_sub_distrib]
    calc |∑ d ∈ Finset.Icc 1 s, (((N / d : ℕ) : ℝ) - (N : ℝ) / d)|
        ≤ ∑ d ∈ Finset.Icc 1 s, |((N / d : ℕ) : ℝ) - (N : ℝ) / d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Finset.Icc 1 s, (1 : ℝ) := Finset.sum_le_sum hfloor
      _ = (s : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc]
          simp
  have hSu := (abs_le.1 hSsum).2
  have hSl := (abs_le.1 hSsum).1
  -- harmonic sum with Euler–Mascheroni error, multiplied by N
  have habsH := abs_le.1 (abs_sum_inv_sub_log_sub_mascheroni_le s hs1)
  have hNH_u : (N : ℝ) * (∑ i ∈ Finset.Icc 1 s, ((i : ℝ))⁻¹)
      - (N : ℝ) * Real.log s - (N : ℝ) * Real.eulerMascheroniConstant
        ≤ (N : ℝ) / s := by
    have hmul := mul_le_mul_of_nonneg_left habsH.2
      (Nat.cast_nonneg (α := ℝ) N)
    have hexp : (N : ℝ) * ((∑ i ∈ Finset.Icc 1 s, ((i : ℝ))⁻¹)
        - Real.log s - Real.eulerMascheroniConstant)
        = (N : ℝ) * (∑ i ∈ Finset.Icc 1 s, ((i : ℝ))⁻¹)
          - (N : ℝ) * Real.log s
          - (N : ℝ) * Real.eulerMascheroniConstant := by ring
    rw [hexp, mul_one_div] at hmul
    exact hmul
  have hNH_l : -((N : ℝ) / s)
      ≤ (N : ℝ) * (∑ i ∈ Finset.Icc 1 s, ((i : ℝ))⁻¹)
        - (N : ℝ) * Real.log s - (N : ℝ) * Real.eulerMascheroniConstant := by
    have hmul := mul_le_mul_of_nonneg_left habsH.1
      (Nat.cast_nonneg (α := ℝ) N)
    have hexp : (N : ℝ) * ((∑ i ∈ Finset.Icc 1 s, ((i : ℝ))⁻¹)
        - Real.log s - Real.eulerMascheroniConstant)
        = (N : ℝ) * (∑ i ∈ Finset.Icc 1 s, ((i : ℝ))⁻¹)
          - (N : ℝ) * Real.log s
          - (N : ℝ) * Real.eulerMascheroniConstant := by ring
    rw [hexp] at hmul
    have hneg : (N : ℝ) * -(1 / s) = -((N : ℝ) / s) := by
      rw [mul_neg, mul_one_div]
    rw [hneg] at hmul
    exact hmul
  -- log reconciliation: 2·N·log s vs N·log N
  have hlogl : 2 * ((N : ℝ) * Real.log s) ≤ (N : ℝ) * Real.log N := by
    have hll : Real.log ((s : ℝ) * s) ≤ Real.log N :=
      Real.log_le_log (by positivity) hcastsq
    rw [Real.log_mul hs0R.ne' hs0R.ne'] at hll
    have hmul := mul_le_mul_of_nonneg_left hll (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [hmul]
  have hlogu : (N : ℝ) * Real.log N
      ≤ 2 * ((N : ℝ) * Real.log s) + 2 * ((N : ℝ) / s) := by
    have hstep : Real.log ((s : ℝ) + 1) ≤ Real.log s + 1 / s := by
      have hdiv := Real.log_le_sub_one_of_pos
        (x := ((s : ℝ) + 1) / s) (by positivity)
      rw [Real.log_div (by positivity) hs0R.ne'] at hdiv
      have heq : ((s : ℝ) + 1) / s - 1 = 1 / s := by
        field_simp
        ring
      linarith
    have hNle : (N : ℝ) ≤ ((s : ℝ) + 1) * ((s : ℝ) + 1) := by
      have : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
      exact_mod_cast this.le
    have hlu : Real.log N ≤ Real.log (((s : ℝ) + 1) * ((s : ℝ) + 1)) :=
      Real.log_le_log (by positivity) hNle
    rw [Real.log_mul (by positivity) (by positivity)] at hlu
    have hcomb : Real.log N ≤ 2 * Real.log s + 2 * (1 / s) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcomb (Nat.cast_nonneg (α := ℝ) N)
    have hfin : (N : ℝ) * (2 * Real.log s + 2 * (1 / s))
        = 2 * ((N : ℝ) * Real.log s) + 2 * ((N : ℝ) / s) := by
      field_simp
    rw [hfin] at hmul
    exact hmul
  -- assemble
  rw [show (2 * Real.eulerMascheroniConstant - 1) * (N : ℝ)
    = 2 * ((N : ℝ) * Real.eulerMascheroniConstant) - N from by ring]
  rw [abs_le]
  constructor
  · nlinarith [hidR, hSl, hNH_l, hlogu, hNs, hsqrts, hsqrt1,
      hcastsq, hcastsq']
  · nlinarith [hidR, hSu, hNH_u, hlogl, hNs, hsqrts, hsqrt1,
      hcastsq, hcastsq']

end RHTower
