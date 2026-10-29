import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheStirlingErrorSplits

/-!
# The smooth term inverts to the Möbius moments; the sawtooth is linear

After the Stirling split (`abs_psi_sub_smooth_sub_sawtooth_le`) two inversions remain.

* **The smooth term** (`inversionOp_stirlingMain`): for `x > 0`,
  `I_x(F) = x ((log x − 1) m(x) − ℓ(x))` with the Möbius moments `m(x) = Σ_{k ≤ x} μ(k)/k` and
  `ℓ(x) = Σ_{k ≤ x} μ(k) log k / k`. Its precision is exactly that of these two moments.
* **The sawtooth** (`abs_inversionOp_sawtooth_lt`): `|I_n(h)| ≤ n log n − log n! < n`, the trivial
  linear size; all cancellation in it must come from `μ`.

**The arithmetic Chebyshev ledger** (`abs_psi_sub_moments_sub_sawtooth_le`): if `|M(k)| ≤ K` for
`k ≤ n`, then

`|ψ(n) − n ((log n − 1) m(n) − ℓ(n)) − I_n(h)| ≤ 3 (1 + ½ log n) K`.

So `ψ(n)` is computed from three arithmetic quantities: the two Möbius moments (the smooth term),
the sawtooth inversion, and the Mertens function (the monotone part). Every route to the count
through Chebyshev's identity is a statement about these three.
-/

noncomputable section

open Real Finset
open ArithmeticFunction (moebius)

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The Möbius moment `m(x) = Σ_{k ≤ x} μ(k)/k`. -/
def moebiusMoment (x : ℝ) : ℝ := ∑ k ∈ Ioc 0 ⌊x⌋₊, (moebius k : ℝ) / k

/-- The logarithmic Möbius moment `ℓ(x) = Σ_{k ≤ x} μ(k) log k / k`. -/
def logMoebiusMoment (x : ℝ) : ℝ := ∑ k ∈ Ioc 0 ⌊x⌋₊, (moebius k : ℝ) * Real.log k / k

/-- **The smooth term inverts to the Möbius moments**:
`I_x(F) = x ((log x − 1) m(x) − ℓ(x))` for `x > 0`. -/
theorem inversionOp_stirlingMain {x : ℝ} (hx : 0 < x) :
    inversionOp stirlingMain x = x * ((Real.log x - 1) * moebiusMoment x - logMoebiusMoment x) := by
  unfold inversionOp stirlingMain moebiusMoment logMoebiusMoment
  rw [mul_sub, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Ioc.mp hk).1
  rw [Real.log_div hx.ne' hk0.ne']
  field_simp
  ring

/-- `Σ_{k ≤ n} log(n/k) = n log n − log n!`. -/
theorem sum_log_div_eq (n : ℕ) :
    ∑ k ∈ Ioc 0 n, Real.log ((n : ℝ) / k) = n * Real.log n - Real.log (n.factorial : ℕ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sum_log_eq_log_factorial, sum_congr rfl fun k hk => Real.log_div hn0.ne'
      (by have := (mem_Ioc.mp hk).1; positivity : ((k : ℕ) : ℝ) ≠ 0), sum_sub_distrib,
      sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

/-- **The sawtooth inversion is at most linear**: `|I_n(h)| ≤ n log n − log n! < n`. -/
theorem abs_inversionOp_sawtooth_lt {n : ℕ} (hn : 1 ≤ n) :
    |inversionOp stirlingSawtooth n| ≤ n * Real.log n - Real.log (n.factorial : ℕ) ∧
      n * Real.log n - Real.log (n.factorial : ℕ) < n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, by linarith [(log_factorial_sub_bounds hn).1]⟩
  unfold inversionOp
  rw [Nat.floor_natCast, ← sum_log_div_eq]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  obtain ⟨h1, h2⟩ := mem_Ioc.mp hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast h1
  have hy : 1 ≤ (n : ℝ) / k := (one_le_div hk0).mpr (by exact_mod_cast h2)
  obtain ⟨hlo, hhi⟩ := sawtooth_bounds hy
  rw [abs_mul]
  calc |(moebius k : ℝ)| * |stirlingSawtooth ((n : ℝ) / k)|
      ≤ 1 * Real.log ((n : ℝ) / k) := by
        refine mul_le_mul (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
          (abs_le.mpr ⟨hlo, by linarith [Real.log_nonneg hy]⟩) (abs_nonneg _) zero_le_one
    _ = Real.log ((n : ℝ) / k) := one_mul _

/-- **The arithmetic Chebyshev ledger.** If `|M(k)| ≤ K` for `k ≤ n`, then
`|ψ(n) − n ((log n − 1) m(n) − ℓ(n)) − I_n(h)| ≤ 3 (1 + ½ log n) K`. -/
theorem abs_psi_sub_moments_sub_sawtooth_le {n : ℕ} (hn : 1 ≤ n) {K : ℝ}
    (hK : ∀ k : ℕ, k ≤ n → |mertens k| ≤ K) :
    |Chebyshev.psi n - n * ((Real.log n - 1) * moebiusMoment n - logMoebiusMoment n) -
        inversionOp stirlingSawtooth n| ≤ 3 * (1 + Real.log n / 2) * K := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← inversionOp_stirlingMain hn0]
  exact abs_psi_sub_smooth_sub_sawtooth_le hn hK

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
