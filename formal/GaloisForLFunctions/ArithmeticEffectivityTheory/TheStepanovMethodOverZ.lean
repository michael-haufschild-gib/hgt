import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The Stepanov method over `ℤ`: auxiliary polynomials and the log-torsion of the horizon

Over `𝔽_q` Stepanov's method counts points by an auxiliary polynomial whose forced vanishing
contradicts its degree. Over `ℤ` the forcing is integrality: a positive integer is at least `1`.
The method has three parts, each a theorem here.

* **Integrality** (`exists_int_eq_lcmUpto_mul_integral`). For `P ∈ ℤ[X]` of degree `≤ n`,
  `lcm(1, …, n + 1) · ∫₀¹ P` is an integer: `∫₀¹ x^k = 1/(k + 1)` and `k + 1` divides the
  horizon period.
* **The integrality floor** (`log_inv_integral_le_psi`). If `∫₀¹ P > 0`, the integer is `≥ 1`, so
  the log-torsion of the horizon is bounded below by the auxiliary section:
  `log (1 / ∫₀¹ P) ≤ ψ(n + 1) = log |ℤ / lcm(1, …, n + 1) ℤ|`.
* **The analytic ceiling** (`nair_four_pow_le_lcmUpto`, `nair_psi_ge`). For `P = X^m (1 − X)^m`,
  `0 < ∫₀¹ P ≤ 4^{−m}` since `x (1 − x) ≤ 1/4`. Hence `lcm(1, …, 2m + 1) ≥ 4^m` and
  `ψ(2m + 1) ≥ m log 4` (Nair).

Together with the opposite bound `θ(x) ≤ x log 4` (a nonzero integer carries at most its own size
in torsion: the primes in `(m, 2m]` divide `C(2m, m) ≤ 4^m`), the method shows that the
log-torsion of the horizon and its degree are comparable (`horizon_logTorsion_comparable`). This
is the effectivity of the base. The sign of `ψ(x) − x` at square-root scale is not reached: the
auxiliary sections are integer polynomials on `[0, 1]`, and how close `log (1/∫₀¹ P)` can come to
`ψ(n + 1)` is the integer Chebyshev problem.
-/

noncomputable section

open Real Finset Polynomial intervalIntegral

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- `k + 1` divides the horizon period `lcm(1, …, n + 1)` for `k ≤ n`. -/
theorem succ_dvd_lcmUpto {k n : ℕ} (hk : k ≤ n) : k + 1 ∣ Nat.lcmUpto (n + 1) :=
  Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨by omega, by omega⟩)

/-- The integral over `[0, 1]` of an integer polynomial is the sum of `a_k / (k + 1)`. -/
theorem integral_aeval_eq_sum (P : ℤ[X]) :
    ∫ x in (0 : ℝ)..1, aeval x P =
      ∑ i ∈ range (P.natDegree + 1), (P.coeff i : ℝ) * (1 / (i + 1)) := by
  simp_rw [aeval_eq_sum_range, zsmul_eq_mul]
  rw [integral_finsetSum (f := fun i x => (P.coeff i : ℝ) * x ^ i)
    fun i _ => (continuous_const.mul (continuous_pow i)).intervalIntegrable _ _]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_pow]
  norm_num

/-- **Integrality.** `lcm(1, …, n + 1) · ∫₀¹ P ∈ ℤ` for `P ∈ ℤ[X]` of degree `≤ n`. -/
theorem exists_int_eq_lcmUpto_mul_integral (P : ℤ[X]) {n : ℕ} (hP : P.natDegree ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto (n + 1) : ℝ) * ∫ x in (0 : ℝ)..1, aeval x P = z := by
  refine ⟨∑ i ∈ range (P.natDegree + 1), P.coeff i * (Nat.lcmUpto (n + 1) / (i + 1) : ℕ), ?_⟩
  rw [integral_aeval_eq_sum, mul_sum, Int.cast_sum]
  refine sum_congr rfl fun i hi => ?_
  have hdvd := succ_dvd_lcmUpto (k := i) (n := n) (by
    have := mem_range.mp hi; omega)
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd (by positivity)]
  push_cast
  ring

/-- **The integrality floor.** A positive integral of an integer polynomial of degree `≤ n` is at
least `1 / lcm(1, …, n + 1)`. -/
theorem one_le_lcmUpto_mul_integral (P : ℤ[X]) {n : ℕ} (hP : P.natDegree ≤ n)
    (hpos : 0 < ∫ x in (0 : ℝ)..1, aeval x P) :
    1 ≤ (Nat.lcmUpto (n + 1) : ℝ) * ∫ x in (0 : ℝ)..1, aeval x P := by
  obtain ⟨z, hz⟩ := exists_int_eq_lcmUpto_mul_integral P hP
  have hlpos : (0 : ℝ) < Nat.lcmUpto (n + 1) := by exact_mod_cast Nat.lcmUpto_pos _
  have hz0 : (0 : ℝ) < z := hz ▸ mul_pos hlpos hpos
  have hz1 : (1 : ℤ) ≤ z := by exact_mod_cast hz0
  rw [hz]; exact_mod_cast hz1

/-- **The auxiliary section bounds the log-torsion of the horizon**:
`log (1 / ∫₀¹ P) ≤ ψ(n + 1)`. -/
theorem log_inv_integral_le_psi (P : ℤ[X]) {n : ℕ} (hP : P.natDegree ≤ n)
    (hpos : 0 < ∫ x in (0 : ℝ)..1, aeval x P) :
    Real.log (1 / ∫ x in (0 : ℝ)..1, aeval x P) ≤ Chebyshev.psi (n + 1 : ℕ) := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  refine Real.log_le_log (by positivity) ?_
  rw [div_le_iff₀ hpos]
  exact one_le_lcmUpto_mul_integral P hP hpos

/-- Nair's auxiliary section `X^m (1 − X)^m`. -/
def nairPoly (m : ℕ) : ℤ[X] := X ^ m * (1 - X) ^ m

theorem nairPoly_natDegree_le (m : ℕ) : (nairPoly m).natDegree ≤ 2 * m := by
  have h1 : (1 - X : ℤ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans ?_
    simp
  calc (nairPoly m).natDegree ≤ (X ^ m : ℤ[X]).natDegree + ((1 - X) ^ m : ℤ[X]).natDegree :=
        natDegree_mul_le
    _ ≤ m + m * 1 := add_le_add (natDegree_X_pow_le m) (natDegree_pow_le_of_le m h1)
    _ = 2 * m := by ring

theorem aeval_nairPoly (m : ℕ) (x : ℝ) : aeval x (nairPoly m) = (x * (1 - x)) ^ m := by
  simp [nairPoly, mul_pow]

/-- **The analytic ceiling**: `0 < ∫₀¹ x^m (1 − x)^m ≤ 4^{−m}`. -/
theorem integral_nairPoly_pos_le (m : ℕ) :
    0 < ∫ x in (0 : ℝ)..1, aeval x (nairPoly m) ∧
      ∫ x in (0 : ℝ)..1, aeval x (nairPoly m) ≤ (1 / 4) ^ m := by
  simp_rw [aeval_nairPoly]
  have hcont : Continuous fun x : ℝ => (x * (1 - x)) ^ m := by fun_prop
  refine ⟨intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
    (fun x hx => pow_pos (mul_pos hx.1 (by linarith [hx.2])) m) one_pos, ?_⟩
  calc ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ m ≤ ∫ _ in (0 : ℝ)..1, (1 / 4 : ℝ) ^ m :=
        integral_mono_on zero_le_one (hcont.intervalIntegrable _ _) intervalIntegrable_const
          fun x hx => pow_le_pow_left₀ (mul_nonneg hx.1 (by linarith [hx.2]))
            (by nlinarith [sq_nonneg (x - 1 / 2)]) m
    _ = (1 / 4) ^ m := by simp

/-- **Nair's bound.** `4^m ≤ lcm(1, …, 2m + 1)`. -/
theorem nair_four_pow_le_lcmUpto (m : ℕ) : 4 ^ m ≤ Nat.lcmUpto (2 * m + 1) := by
  obtain ⟨hpos, hle⟩ := integral_nairPoly_pos_le m
  have h1 := one_le_lcmUpto_mul_integral (nairPoly m) (nairPoly_natDegree_le m) hpos
  have hl : (0 : ℝ) ≤ Nat.lcmUpto (2 * m + 1) := Nat.cast_nonneg _
  have h4 : (4 : ℝ) ^ m * (1 / 4) ^ m = 1 := by rw [← mul_pow]; norm_num
  have : (4 : ℝ) ^ m ≤ Nat.lcmUpto (2 * m + 1) := by
    have h2 : (Nat.lcmUpto (2 * m + 1) : ℝ) * ∫ x in (0 : ℝ)..1, aeval x (nairPoly m) ≤
        (Nat.lcmUpto (2 * m + 1) : ℝ) * (1 / 4) ^ m := mul_le_mul_of_nonneg_left hle hl
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) m]
  exact_mod_cast this

/-- **Nair's bound for the log-torsion**: `ψ(2m + 1) ≥ m log 4`. -/
theorem nair_psi_ge (m : ℕ) : m * Real.log 4 ≤ Chebyshev.psi (2 * m + 1 : ℕ) := by
  rw [Chebyshev.psi_eq_log_lcmUpto, ← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast nair_four_pow_le_lcmUpto m)

/-- **The effectivity of the base**: the log-torsion of the horizon is comparable with its degree,
`m log 4 ≤ ψ(2m + 1)` and `θ(x) ≤ x log 4`. -/
theorem horizon_logTorsion_comparable :
    (∀ m : ℕ, m * Real.log 4 ≤ Chebyshev.psi (2 * m + 1 : ℕ)) ∧
      ∀ x : ℝ, 0 ≤ x → Chebyshev.theta x ≤ Real.log 4 * x :=
  ⟨nair_psi_ge, fun _ hx => Chebyshev.theta_le_log4_mul_x hx⟩

end GaloisForLFunctions.ArithmeticEffectivityTheory
