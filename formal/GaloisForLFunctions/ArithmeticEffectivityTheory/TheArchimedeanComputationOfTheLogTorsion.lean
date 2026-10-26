import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHorizonTorsion
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The archimedean computation of the log-torsion

The log-torsion of the horizon has a second computation at the archimedean place. Each transition
kernel of the horizon period has log-order `Λ(n) = log Φ_n(1)`, and `Φ_n(1) = Π_μ (1 − μ)` over the
primitive `n`-th roots of unity: `Λ(n)` is the archimedean size of the cyclotomic integer `1 − ζ_n`,
summed over its Galois orbit — the product formula in `ℚ(ζ_n)`.

* **The product formula** (`vonMangoldt_eq_sum_log_norm_one_sub`). For `n ≥ 2`,
  `Λ(n) = Σ_{μ primitive n-th root} log |1 − μ|`.
* **The torsion sum** (`psi_eq_fareySum`). The primitive roots of order `n` are the torsion
  characteristics `k/n`, `k` coprime to `n`, of the characteristic circle, and
  `|1 − e(k/n)| = 2 sin(πk/n)`, so
  `ψ(N) = Σ_{2 ≤ n ≤ N} Σ_{(k,n)=1} log(2 sin(πk/n))`:
  the log-torsion of the horizon is the sum of `log |1 − e(a)|` over the Farey points `a` of order
  `≤ N`. The function `log |1 − e(a)|` has mean zero on the circle; the sum is its Riemann sum on
  the torsion characteristics, i.e. minus their logarithmic potential at the arithmetic point `0`.
* **The sign as a potential** (`riemannHypothesis_iff_fareySum`). RH holds iff this torsion sum is
  `N + O(√N log² N)`.

So the two computations of the box Euler characteristic meet on the torsion characteristics: the
finite side counts the order of `ℤ/lcm(1..N)ℤ`, the archimedean side measures how the Farey points
sit against the logarithmic kernel at `0`. The sign of `ζ` is a statement about the distribution of
rational points, read through the potential of the arithmetic point.
-/

noncomputable section

open Polynomial Finset Complex Filter Asymptotics
open scoped Real

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- `log |Φ_n(1)| = Λ(n)` for `n ≥ 2`: `Φ_{p^k}(1) = p` and `Φ_n(1) = 1` otherwise. -/
theorem log_norm_eval_one_cyclotomic {n : ℕ} (hn : 2 ≤ n) :
    Real.log ‖eval 1 (cyclotomic n ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    haveI := Fact.mk hp
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [eval_one_cyclotomic_prime_pow, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, Complex.norm_natCast]
  · rw [eval_one_cyclotomic_not_prime_pow, norm_one, Real.log_one,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    intro p hp k hpk
    have hk : k ≠ 0 := by rintro rfl; rw [pow_zero] at hpk; omega
    exact hpp (hpk ▸ hp.isPrimePow.pow hk)

/-- `Φ_n(1) = Π_μ (1 − μ)` over the primitive `n`-th roots of unity. -/
theorem eval_one_cyclotomic_eq_prod {n : ℕ} (hn : 0 < n) :
    eval 1 (cyclotomic n ℂ) = ∏ μ ∈ primitiveRoots n ℂ, (1 - μ) := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp n hn.ne'), eval_prod]
  simp

/-- **The product formula in `ℚ(ζ_n)`**: `Λ(n) = Σ_μ log |1 − μ|` over primitive `n`-th roots. -/
theorem vonMangoldt_eq_sum_log_norm_one_sub {n : ℕ} (hn : 2 ≤ n) :
    ArithmeticFunction.vonMangoldt n = ∑ μ ∈ primitiveRoots n ℂ, Real.log ‖1 - μ‖ := by
  rw [← log_norm_eval_one_cyclotomic hn, eval_one_cyclotomic_eq_prod (by omega), norm_prod,
    Real.log_prod]
  intro μ hμ
  have hprim := (mem_primitiveRoots (by omega)).mp hμ
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hprim.ne_one (by omega)).symm)

/-- The primitive `n`-th roots are `e(k/n)` with `k < n` coprime to `n`. -/
theorem sum_primitiveRoots_eq_sum_coprime {n : ℕ} (hn : 0 < n) (f : ℂ → ℝ) :
    ∑ μ ∈ primitiveRoots n ℂ, f μ =
      ∑ k ∈ (range n).filter (·.Coprime n), f (Complex.exp (2 * π * I / n) ^ k) := by
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  have himage : primitiveRoots n ℂ =
      ((range n).filter (·.Coprime n)).image fun k => Complex.exp (2 * π * I / n) ^ k := by
    ext μ
    simp only [mem_image, mem_filter, mem_range, mem_primitiveRoots hn]
    constructor
    · intro hμ
      haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
      exact ⟨i, ⟨hi, (hζ.pow_iff_coprime hn i).mp hμ⟩, rfl⟩
    · rintro ⟨k, ⟨-, hk⟩, rfl⟩
      exact hζ.pow_of_coprime k hk
  rw [himage, sum_image]
  intro a ha b hb hab
  simp only [coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
  exact hζ.pow_inj ha.1 hb.1 hab

/-- `|1 − e(k/n)| = 2 sin(πk/n)` for `0 < k < n`. -/
theorem norm_one_sub_exp_pow {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    ‖1 - Complex.exp (2 * π * I / n) ^ k‖ = 2 * Real.sin (π * k / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hkn)
  have harg : Complex.exp (2 * π * I / n) ^ k = Complex.exp (I * ((2 * π * k / n : ℝ) : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [harg, norm_sub_rev, norm_exp_I_mul_ofReal_sub_one,
    show 2 * π * k / n / 2 = π * k / n by ring, Real.norm_eq_abs, abs_of_nonneg]
  refine mul_nonneg two_pos.le (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_)
  rw [div_le_iff₀ hn]
  have : (k : ℝ) ≤ n := by exact_mod_cast hkn.le
  nlinarith [Real.pi_pos]

/-- The **torsion sum** of order `n`: `Σ_{(k,n)=1} log(2 sin(πk/n))`. -/
def torsionLogSum (n : ℕ) : ℝ :=
  ∑ k ∈ (range n).filter (·.Coprime n), Real.log (2 * Real.sin (π * k / n))

/-- **`Λ(n)` as a sum over the torsion characteristics of order `n`.** -/
theorem vonMangoldt_eq_torsionLogSum {n : ℕ} (hn : 2 ≤ n) :
    ArithmeticFunction.vonMangoldt n = torsionLogSum n := by
  rw [vonMangoldt_eq_sum_log_norm_one_sub hn, sum_primitiveRoots_eq_sum_coprime (by omega),
    torsionLogSum]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_filter, mem_range] at hk
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [Nat.coprime_zero_left] at hk; omega
    · exact h
  rw [norm_one_sub_exp_pow hk0 hk.1]

/-- **The log-torsion of the horizon is the Farey sum** `Σ_{2 ≤ n ≤ N} Σ_{(k,n)=1} log(2 sin(πk/n))`. -/
theorem psi_eq_fareySum (N : ℕ) :
    Chebyshev.psi N = ∑ n ∈ Icc 2 N, torsionLogSum n := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rw [← sum_subset (Icc_subset_Icc_left (by norm_num : 0 ≤ 2)) fun n hn hn2 => by
    simp only [mem_Icc] at hn hn2
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp]
  exact sum_congr rfl fun n hn => vonMangoldt_eq_torsionLogSum (mem_Icc.mp hn).1

/-- **The sign as a potential at the arithmetic point.** RH holds iff the Farey sum of
`log(2 sin πa)` over the torsion characteristics of order `≤ N` is `N + O(√N log² N)`. -/
theorem riemannHypothesis_iff_fareySum :
    RiemannHypothesis ↔ (fun N : ℕ => (∑ n ∈ Icc 2 N, torsionLogSum n) - N) =O[atTop]
      (fun N : ℕ => Real.sqrt N * Real.log N ^ 2) := by
  rw [riemannHypothesis_iff_logTorsion_sub_isBigO]
  simp only [logTorsion_eq_psi, psi_eq_fareySum]

end GaloisForLFunctions.ArithmeticEffectivityTheory
