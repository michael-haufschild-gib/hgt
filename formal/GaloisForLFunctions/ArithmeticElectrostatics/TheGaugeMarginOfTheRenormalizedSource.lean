import GaloisForLFunctions.ArithmeticElectrostatics.QuantizationTurnsWindowsIntoPoints
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSelfConvLogBound
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The gauge margin of the renormalized source

A sign twin of `ζ` replaces the Euler vacuum by a completely multiplicative gauge `ω` with
`ω(p) = ±1`; its von Mangoldt weight is `ωΛ` and its renormalized Rankin–Selberg source is `ωΛ₂`
(`selbergSource_twist`). The electrostatic quantities of a divisor are blind to every archimedean
twist, and the positivity of the circle holds for every charge configuration; the gauge charge
enters through the source. This file measures how strongly.

* **Margin at the first flipped prime** (`twistedSelbergSource_prime`, `gaugeMargin_of_flip`): if
  `ω(p) = −1`, the twin's source at `p` is `−log² p`, while `ζ`'s is `+log² p`: the margin
  `Λ₂(p) − ωΛ₂(p) = 2 log² p`.
* **The margin law on prime windows** (`gaugeMargin_window`): for every window `N` and every sign
  gauge differing from the vacuum at some prime `p ≤ N`, some `n ≤ N` has `ωΛ₂(n) ≤ −log² 2` while
  `Λ₂ ≥ 0` everywhere. The margin does not collapse as primes enter: it is fixed by the smallest
  flipped prime, independently of the window.
* **The L-series margin** (`LSeries_gaugeMargin`): for real `σ > 1`,
  `L(Λ₂, σ) − L(ωΛ₂, σ) ≥ 2 log² p · p^{−σ}` at a flipped prime `p`.

This is a margin law for positivity of coefficients. Positivity of the corresponding forms on tests
reading the first `N` primes — the margin law of the frontier's Q3 — is not supplied by it: forms of
`ωΛ₂` on nonnegative tests inherit the margin, signed tests do not.
-/

noncomputable section

open ArithmeticFunction Finset

namespace GaloisForLFunctions.ArithmeticElectrostatics

/-- The twin's source at a prime is `ω(p) log² p`. -/
theorem twistedSelbergSource_prime (ω : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    (selbergSource.pmul ω) p = ω p * Real.log p ^ 2 := by
  have h := selbergSource_prime_pow hp (le_refl 1)
  rw [pow_one, Nat.cast_one, show (2 * (1 : ℝ) - 1) = 1 by norm_num, one_mul] at h
  rw [pmul_apply, h, mul_comm]

/-- **Margin at a flipped prime**: `Λ₂(p) − ωΛ₂(p) = 2 log² p` and `ωΛ₂(p) = −log² p`. -/
theorem gaugeMargin_of_flip (ω : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (hflip : ω p = -1) :
    (selbergSource.pmul ω) p = -Real.log p ^ 2 ∧
      selbergSource p - (selbergSource.pmul ω) p = 2 * Real.log p ^ 2 := by
  have h := selbergSource_prime_pow hp (le_refl 1)
  rw [pow_one, Nat.cast_one, show (2 * (1 : ℝ) - 1) = 1 by norm_num, one_mul] at h
  rw [twistedSelbergSource_prime ω hp, hflip, h]
  constructor <;> ring

/-- **The margin law on prime windows**: a sign gauge differing from the Euler vacuum at a prime
`p ≤ N` has a source coefficient `≤ −log² 2` at some `n ≤ N`, while `Λ₂ ≥ 0`. -/
theorem gaugeMargin_window (ω : ArithmeticFunction ℝ) {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hflip : ω p = -1) :
    (∀ n, 0 ≤ selbergSource n) ∧
      ∃ n ∈ Icc 1 N, (selbergSource.pmul ω) n ≤ -Real.log 2 ^ 2 := by
  refine ⟨selbergSource_nonneg, p, mem_Icc.mpr ⟨hp.one_le, hpN⟩, ?_⟩
  rw [(gaugeMargin_of_flip ω hp hflip).1, neg_le_neg_iff]
  have h2 : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  exact pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) h2 2

/-- `Λ₂(n) ≤ 3 log² n`. -/
theorem selbergSource_le (n : ℕ) : selbergSource n ≤ 3 * Real.log n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [selbergSource, ArithmeticFunction.add_apply, pmul_apply, log_apply]
  have h1 := RHTower.Sieve.vonMangoldtSelfConv_le_two_mul_log_sq n hn
  have h2 : vonMangoldt n ≤ Real.log n := vonMangoldt_le_log
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  nlinarith

/-- `Σ Λ₂(n) n^{−σ}` converges for `σ > 1`. -/
theorem summable_selbergSource_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => selbergSource n * (n : ℝ) ^ (-σ) := by
  set α := (σ - 1) / 4
  have hα : 0 < α := by simp only [α]; linarith
  have hg : Summable fun n : ℕ => 3 / α ^ 2 * (n : ℝ) ^ (2 * α - σ) :=
    (Real.summable_nat_rpow.mpr (by simp only [α]; linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [selbergSource, ArithmeticFunction.add_apply, pmul_apply, mul_apply, log_apply]
        exact add_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n))
          (sum_nonneg fun x _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (fun n => ?_) hg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ArithmeticFunction.map_zero, zero_mul]
    exact mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := RHTower.Mertens.log_le_rpow hn0 hα
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hsq : Real.log n ^ 2 ≤ (1 / α) ^ 2 * (n : ℝ) ^ (2 * α) := by
    rw [show (2 * α) = α + α by ring, Real.rpow_add hn0]
    nlinarith
  have hpow : (n : ℝ) ^ (2 * α) * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (2 * α - σ) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hpos : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hn0.le _
  calc selbergSource n * (n : ℝ) ^ (-σ) ≤ 3 * Real.log n ^ 2 * (n : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (selbergSource_le n) hpos
    _ ≤ 3 * ((1 / α) ^ 2 * (n : ℝ) ^ (2 * α)) * (n : ℝ) ^ (-σ) := by gcongr
    _ = 3 / α ^ 2 * (n : ℝ) ^ (2 * α - σ) := by rw [← hpow]; field_simp

/-- **The L-series margin**: for real `σ > 1` and a flipped prime `p` of a sign gauge,
`L(Λ₂, σ) − L(ωΛ₂, σ) ≥ 2 log² p · p^{−σ}`. -/
theorem LSeries_gaugeMargin (ω : ArithmeticFunction ℝ) (hsign : ∀ n, ω n = 1 ∨ ω n = -1 ∨ ω n = 0)
    {σ : ℝ} (hσ : 1 < σ) {p : ℕ} (hp : p.Prime) (hflip : ω p = -1) :
    2 * Real.log p ^ 2 * (p : ℝ) ^ (-σ) ≤
      ∑' n : ℕ, (selbergSource n - (selbergSource.pmul ω) n) * (n : ℝ) ^ (-σ) := by
  -- each term of the difference is nonnegative: `(1 − ω(n)) Λ₂(n) n^{−σ} ≥ 0`
  have hterm : ∀ n : ℕ, 0 ≤ (selbergSource n - (selbergSource.pmul ω) n) * (n : ℝ) ^ (-σ) := by
    intro n
    rw [pmul_apply]
    have hΛ := selbergSource_nonneg n
    have hpow : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    rcases hsign n with h | h | h <;> rw [h] <;> nlinarith
  have hdom : ∀ n : ℕ, (selbergSource n - (selbergSource.pmul ω) n) * (n : ℝ) ^ (-σ) ≤
      2 * (selbergSource n * (n : ℝ) ^ (-σ)) := by
    intro n
    rw [pmul_apply]
    have hΛ := selbergSource_nonneg n
    have hpow : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    rcases hsign n with h | h | h <;> rw [h] <;> nlinarith
  have hsum' : Summable fun n : ℕ => (selbergSource n - (selbergSource.pmul ω) n) * (n : ℝ) ^ (-σ) :=
    Summable.of_nonneg_of_le hterm hdom ((summable_selbergSource_rpow hσ).mul_left 2)
  have hle := hsum'.le_tsum p fun n _ => hterm n
  rw [(gaugeMargin_of_flip ω hp hflip).2] at hle
  exact hle

end GaloisForLFunctions.ArithmeticElectrostatics
