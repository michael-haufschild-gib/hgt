import GaloisForLFunctions.ArithmeticEffectivityTheory.TheArchimedeanComputationOfTheLogTorsion
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheTangentIsADilationAverageOfTheSource

/-!
# The q-deformation of the horizon period

The **horizon polynomial** `P_N = Π_{2 ≤ n ≤ N} Φ_n ∈ ℤ[X]` has the torsion characteristics of
order `2, …, N` as its roots — its degree is their number `Σ_{n ≤ N} φ(n)` (`natDegree_horizonPoly`)
— and its value at the arithmetic point is the horizon period, `P_N(1) = lcm(1, …, N)`
(`horizonPoly_eval_one`). It is the q-deformation of the period: `P_N(q)` is defined for every `q`,
and `q = 1` is the arithmetic specialization.

* **The Möbius formula** (`sum_log_cyclotomic_eq_mertens`). For `q > 0`,
  `log P_N(q) = Σ_{d ≤ N} M(⌊N/d⌋) log [d]_q`, `[d]_q = 1 + q + ⋯ + q^{d−1}`, with the Mertens
  function `M` as coefficients. It is Möbius inversion of `Π_{n ∣ d, n ≥ 2} Φ_n = [d]_q`. For a prime
  power `q`, `[d]_q` is the number of points of `ℙ^{d−1}(𝔽_q)`.
* **The arithmetic point** (`psi_eq_sum_mertens_log`, `sum_mertens_floor_eq_one`). At `q = 1`,
  `[d]_1 = d` and `ψ(N) = Σ_{d ≤ N} M(⌊N/d⌋) log d`; the coefficients sum to one.

So the log-torsion of the horizon is the value at `q = 1` of a q-count whose coefficients are the
Möbius sums: the signs that carry RH (the Mertens function, gauge charged) are the coefficients of the
deformation, and the log-torsion is their pairing with the logarithms of the q-integers at the
arithmetic point. Away from `q = 1` the same polynomial has degree `Σ φ(n) ≍ N²` — the scale of a
dimension — while at `q = 1` it carries the linear scale `ψ(N) ≍ N`.
-/

noncomputable section

open Polynomial Finset

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The **horizon polynomial** `Π_{2 ≤ n ≤ N} Φ_n`. -/
def horizonPoly (N : ℕ) : ℤ[X] := ∏ n ∈ Icc 2 N, cyclotomic n ℤ

/-- Its degree is the number of torsion characteristics of order `2, …, N`. -/
theorem natDegree_horizonPoly (N : ℕ) :
    (horizonPoly N).natDegree = ∑ n ∈ Icc 2 N, Nat.totient n := by
  rw [horizonPoly, natDegree_prod _ _ fun n _ => cyclotomic_ne_zero n ℤ]
  exact sum_congr rfl fun n _ => natDegree_cyclotomic n ℤ

/-- The q-integer `[d]_q = 1 + q + ⋯ + q^{d−1}`. -/
def qInt (d : ℕ) (q : ℝ) : ℝ := ∑ i ∈ range d, q ^ i

theorem qInt_pos {d : ℕ} (hd : 0 < d) {q : ℝ} (hq : 0 < q) : 0 < qInt d q :=
  sum_pos (fun i _ => pow_pos hq i) (nonempty_range_iff.mpr hd.ne')

theorem qInt_one (d : ℕ) : qInt d 1 = d := by simp [qInt]

/-- `Φ_n(q) > 0` for `n ≥ 2` and `q > 0`. -/
theorem eval_cyclotomic_pos {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    0 < eval q (cyclotomic n ℝ) := by
  rcases eq_or_lt_of_le hn with rfl | h
  · rw [cyclotomic_two]; simp; linarith
  · exact cyclotomic_pos h q

/-- The cyclotomic potential, with the factor `Φ_1` removed. -/
def cycloLog (q : ℝ) (n : ℕ) : ℝ := if n = 1 then 0 else Real.log (eval q (cyclotomic n ℝ))

/-- `Σ_{n ∣ d} log Φ_n(q) = log [d]_q` (the factor `n = 1` removed). -/
theorem sum_divisors_cycloLog {q : ℝ} (hq : 0 < q) {d : ℕ} (hd : 0 < d) :
    ∑ n ∈ d.divisors, cycloLog q n = Real.log (qInt d q) := by
  have hprod := congrArg (eval q) (prod_cyclotomic_eq_geom_sum hd ℝ)
  rw [eval_prod] at hprod
  have hgeom : eval q (∑ i ∈ range d, (X : ℝ[X]) ^ i) = qInt d q := by simp [qInt, eval_finsetSum]
  rw [hgeom] at hprod
  have hmem : ∀ n ∈ d.divisors.erase 1, 2 ≤ n := fun n hn => by
    obtain ⟨hn1, hnd⟩ := mem_erase.mp hn
    have := Nat.pos_of_mem_divisors hnd; omega
  rw [← hprod, Real.log_prod fun n hn => (eval_cyclotomic_pos (hmem n hn) hq).ne',
    ← sum_erase_add _ _ (Nat.one_mem_divisors.mpr hd.ne')]
  simp only [cycloLog, if_pos, add_zero]
  exact sum_congr rfl fun n hn => if_neg (mem_erase.mp hn).1

/-- The Mertens function `M(k) = Σ_{m ≤ k} μ(m)`. -/
def mertens (k : ℕ) : ℝ := ∑ m ∈ Icc 1 k, (ArithmeticFunction.moebius m : ℝ)

/-- **The Möbius formula for the q-deformed horizon period**:
`Σ_{2 ≤ n ≤ N} log Φ_n(q) = Σ_{d ≤ N} M(⌊N/d⌋) log [d]_q` for `q > 0`. -/
theorem sum_log_cyclotomic_eq_mertens {q : ℝ} (hq : 0 < q) (N : ℕ) :
    ∑ n ∈ Icc 2 N, Real.log (eval q (cyclotomic n ℝ)) =
      ∑ d ∈ Icc 1 N, Real.log (qInt d q) * mertens (N / d) := by
  have hinv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun d hd => sum_divisors_cycloLog hq hd)
  have hleft : ∑ n ∈ Icc 2 N, Real.log (eval q (cyclotomic n ℝ)) = ∑ n ∈ Icc 1 N, cycloLog q n := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ N), sum_insert (by simp)]
    simp only [cycloLog, if_pos, zero_add]
    exact (sum_congr rfl fun n hn => if_neg (by simp at hn; omega)).symm
  simp only [mertens]
  rw [hleft, ← ArithmeticContinuationAndCriticalEnergy.sum_Icc_divisor_convolution_eq_dilation]
  refine sum_congr rfl fun k hk => ?_
  rw [← hinv k (by simp at hk; omega), Nat.sum_divisorsAntidiagonal' (fun a b =>
    (ArithmeticFunction.moebius a : ℝ) * Real.log (qInt b q))]
  exact sum_congr rfl fun j _ => mul_comm _ _

/-- Real and complex evaluations of `Φ_n` at real points agree. -/
theorem eval_cyclotomic_complex_ofReal (n : ℕ) (q : ℝ) :
    eval (q : ℂ) (cyclotomic n ℂ) = ((eval q (cyclotomic n ℝ) : ℝ) : ℂ) := by
  rw [← map_cyclotomic n (algebraMap ℝ ℂ), eval_map, ← Complex.coe_algebraMap, eval₂_hom]

/-- `log Φ_n(1) = Λ(n)` over `ℝ`, for `n ≥ 2`. -/
theorem log_eval_one_cyclotomic_real {n : ℕ} (hn : 2 ≤ n) :
    Real.log (eval 1 (cyclotomic n ℝ)) = ArithmeticFunction.vonMangoldt n := by
  rw [← log_norm_eval_one_cyclotomic hn, show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp,
    eval_cyclotomic_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (eval_cyclotomic_pos hn one_pos).le]

/-- **The arithmetic point**: `ψ(N) = Σ_{d ≤ N} M(⌊N/d⌋) log d`. -/
theorem psi_eq_sum_mertens_log (N : ℕ) :
    Chebyshev.psi N = ∑ d ∈ Icc 1 N, Real.log d * mertens (N / d) := by
  rw [psi_eq_fareySum]
  have h := sum_log_cyclotomic_eq_mertens one_pos N
  simp only [qInt_one] at h
  rw [← h]
  refine sum_congr rfl fun n hn => ?_
  rw [log_eval_one_cyclotomic_real (mem_Icc.mp hn).1, vonMangoldt_eq_torsionLogSum (mem_Icc.mp hn).1]

/-- `Σ_{d ∣ k} μ(d) = [k = 1]`. -/
theorem sum_antidiagonal_moebius {k : ℕ} (hk : 0 < k) :
    ∑ x ∈ k.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * 1 =
      if k = 1 then 1 else 0 :=
  (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := fun i => if i = 1 then (1 : ℝ) else 0)
    (g := fun _ => 1)).mp (fun n hn => by
    rw [sum_ite_eq', if_pos (Nat.one_mem_divisors.mpr hn.ne')]) k hk

/-- The Möbius coefficients of the deformation sum to one. -/
theorem sum_mertens_floor_eq_one {N : ℕ} (hN : 1 ≤ N) :
    ∑ d ∈ Icc 1 N, mertens (N / d) = 1 := by
  have h := ArithmeticContinuationAndCriticalEnergy.sum_Icc_divisor_convolution_eq_dilation
    (fun _ => (1 : ℝ)) (fun m => (ArithmeticFunction.moebius m : ℝ)) N
  simp only [one_mul] at h
  simp only [mertens]
  rw [← h]
  rw [sum_congr rfl fun k hk => by
    rw [← Nat.sum_divisorsAntidiagonal' (fun a _ => (ArithmeticFunction.moebius a : ℝ)),
      show ∑ x ∈ k.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) =
        ∑ x ∈ k.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * 1 by simp,
      sum_antidiagonal_moebius (by simp at hk; omega)]]
  rw [sum_ite_eq', if_pos (by simp; omega)]

/-- **The horizon period is the value of the horizon polynomial at the arithmetic point.** -/
theorem horizonPoly_eval_one (N : ℕ) : (horizonPoly N).eval 1 = Nat.lcmUpto N := by
  have hR : (((horizonPoly N).eval 1 : ℤ) : ℝ) = ∏ n ∈ Icc 2 N, eval 1 (cyclotomic n ℝ) := by
    rw [horizonPoly, eval_prod, Int.cast_prod]
    refine prod_congr rfl fun n _ => ?_
    rw [← map_cyclotomic_int n ℝ, eval_map, eval₂_at_one]
    rfl
  have hpos : 0 < ∏ n ∈ Icc 2 N, eval 1 (cyclotomic n ℝ) :=
    prod_pos fun n hn => eval_cyclotomic_pos (mem_Icc.mp hn).1 one_pos
  have hlog : Real.log (∏ n ∈ Icc 2 N, eval 1 (cyclotomic n ℝ)) = Real.log (Nat.lcmUpto N) := by
    rw [Real.log_prod fun n hn => (eval_cyclotomic_pos (mem_Icc.mp hn).1 one_pos).ne',
      ← Chebyshev.psi_eq_log_lcmUpto, psi_eq_fareySum]
    exact sum_congr rfl fun n hn => by
      rw [log_eval_one_cyclotomic_real (mem_Icc.mp hn).1,
        vonMangoldt_eq_torsionLogSum (mem_Icc.mp hn).1]
  have hreal : (((horizonPoly N).eval 1 : ℤ) : ℝ) = (Nat.lcmUpto N : ℝ) := by
    rw [hR]
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hpos)
      (Set.mem_Ioi.mpr (by exact_mod_cast Nat.lcmUpto_pos N)) hlog
  exact_mod_cast hreal

end GaloisForLFunctions.ArithmeticEffectivityTheory
