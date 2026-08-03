import GaloisForLFunctions.RHTower.Sieve.ChernoffTails
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# A Chebyshev lower bound for the primes of a wide window

Mertens' first theorem localises to a window: subtracting the two bounds gives

`∑_{M < p ≤ N} (log p)/p ≥ log(N/M) - 2c₁`,

with `c₁` the explicit constant of `MertensFirst.lean`.  Since `x ↦ (log x)/x` decreases beyond `e`,
every term of that sum is at most `(log M)/M`, so the window contains at least

`(log(N/M) - 2c₁) · M / log M`

primes.  The bound is positive as soon as the ratio `N/M` exceeds `exp(2c₁)`; it is the uniform
prime input for growing dyadic marker blocks, where only the *count* in each block matters and the
block ratio may be taken as large as one likes.

Nothing here is asymptotic: the constant is the one already carried by Mertens' first theorem.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The window prime set is the difference of two initial prime sets. -/
theorem sum_logDiv_bigPrimeSet (z b : ℕ) (hzb : z ≤ b) :
    ∑ p ∈ bigPrimeSet z b, Real.log p / (p : ℝ) = mertensA b - mertensA z := by
  classical
  have hsub : Nat.primesLE z ⊆ Nat.primesLE b := by
    intro p hp
    obtain ⟨hpz, hprime⟩ := Nat.mem_primesLE.1 hp
    exact Nat.mem_primesLE.2 ⟨by omega, hprime⟩
  rw [bigPrimeSet_eq_sdiff z b hzb, Finset.sum_sdiff_eq_sub hsub]
  rfl

/-- Beyond `e` the weight `(log p)/p` is maximised at the left endpoint of the window. -/
theorem logDiv_le_of_lt {M p : ℕ} (hM : 3 ≤ M) (hp : M < p) :
    Real.log p / (p : ℝ) ≤ Real.log M / (M : ℝ) := by
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hMR : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hpR : (M : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.le
  refine Real.log_div_self_antitoneOn ?_ ?_ hpR
  · exact Set.mem_Ici.2 (by linarith)
  · exact Set.mem_Ici.2 (by linarith)

/-- **Window prime count.**  Explicit Chebyshev-type lower bound from Mertens' first theorem. -/
theorem card_bigPrimeSet_ge {M N : ℕ} (hM : 3 ≤ M) (hMN : M ≤ N) :
    (Real.log N - Real.log M - 2 * mertensFirstConst) * (M : ℝ) / Real.log M
      ≤ ((bigPrimeSet M N).card : ℝ) := by
  classical
  have hMR : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hM1 : 1 ≤ M := by omega
  have hN1 : 1 ≤ N := by omega
  have hsum := sum_logDiv_bigPrimeSet M N hMN
  have hupN := abs_mertensA_sub_log_le hN1
  have hupM := abs_mertensA_sub_log_le hM1
  have hlow : Real.log N - Real.log M - 2 * mertensFirstConst
      ≤ ∑ p ∈ bigPrimeSet M N, Real.log p / (p : ℝ) := by
    rw [hsum]
    have h1 := (abs_le.1 hupN).1
    have h2 := (abs_le.1 hupM).2
    linarith
  have hterm : ∀ p ∈ bigPrimeSet M N, Real.log p / (p : ℝ) ≤ Real.log M / (M : ℝ) := by
    intro p hp
    obtain ⟨hmem, -⟩ := Finset.mem_filter.1 hp
    have := (Finset.mem_Icc.1 hmem).1
    exact logDiv_le_of_lt hM (by omega)
  have hupper : ∑ p ∈ bigPrimeSet M N, Real.log p / (p : ℝ)
      ≤ ((bigPrimeSet M N).card : ℝ) * (Real.log M / (M : ℝ)) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hchain : Real.log N - Real.log M - 2 * mertensFirstConst
      ≤ ((bigPrimeSet M N).card : ℝ) * (Real.log M / (M : ℝ)) := le_trans hlow hupper
  have hmul := mul_le_mul_of_nonneg_right hchain hMpos.le
  have hcancel : ((bigPrimeSet M N).card : ℝ) * (Real.log M / (M : ℝ)) * (M : ℝ)
      = ((bigPrimeSet M N).card : ℝ) * Real.log M := by
    field_simp
  rw [hcancel] at hmul
  rw [div_le_iff₀ hlogM]
  exact hmul

/-- **Dyadic-type corollary.**  A window of ratio `Q` contains a positive proportion of
`M / log M` primes as soon as `log Q` exceeds twice the Mertens constant. -/
theorem card_bigPrimeSet_ratio_ge {M Q : ℕ} (hM : 3 ≤ M) (hQ : 1 ≤ Q) :
    (Real.log Q - 2 * mertensFirstConst) * (M : ℝ) / Real.log M
      ≤ ((bigPrimeSet M (Q * M)).card : ℝ) := by
  have hMR : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hMN : M ≤ Q * M := Nat.le_mul_of_pos_left M (by omega)
  have hbase := card_bigPrimeSet_ge hM hMN
  have hlog : Real.log ((Q * M : ℕ) : ℝ) = Real.log Q + Real.log M := by
    push_cast
    rw [Real.log_mul (by linarith) (by linarith)]
  rw [hlog] at hbase
  have hrw : Real.log Q + Real.log M - Real.log M - 2 * mertensFirstConst
      = Real.log Q - 2 * mertensFirstConst := by ring
  rw [hrw] at hbase
  exact hbase

end RHTower.Sieve
