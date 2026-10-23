import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Decay of coprime Möbius–divisor-sum sums

Write `w(n) = μ(n)/σ(n)`. For `δ ≥ 1` the coprime partial sums
`T_δ(Y) = Σ_{a ≤ Y, (a,δ)=1} w(a)` and the coprime pair sum
`S(X) = Σ_{a,b ≤ X, (a,b)=1} w(a) w(b)` decay logarithmically:

* `abs_coprimeMoebiusSigmaSum_le`: `|T_δ(Y)| ≤ C δ^{1/4} (1 + log Y)^{-2}`;
* `abs_coprimePairMoebiusSigmaSum_le`: `|S(X)| ≤ C (1 + log X)^{-4}`.

Mechanism. On coprime-to-`δ` arguments `w = β_δ * (μ/id)` with the nonnegative multiplicative
kernel `β_δ(p^k) = p^{-k}` for `p ∣ δ` and `p^{-k}/(p+1)` for `p ∤ δ`, so
`T_δ(Y) = Σ_{d ≤ Y} β_δ(d) m(Y/d)`, `m(z) = Σ_{n ≤ z} μ(n)/n = O(log^{-4} z)`. The kernel mass
`Σ_d β_δ(d)(1 + log d)²` is an Euler product of size `≪ δ^{1/4}`. The coprimality sieve gives
`S(X) = Σ_δ μ(δ) w(δ)² T_δ(X/δ)²`.
-/

open Finset Filter Topology ArithmeticFunction

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### The weight `μ/σ` and its coprime sums -/

/-- `w(n) = μ(n)/σ(n)`. -/
def moebiusSigma (n : ℕ) : ℝ := (moebius n : ℝ) / (sigma 1 n : ℝ)

/-- `T_δ(Y) = Σ_{a ≤ Y, (a,δ)=1} μ(a)/σ(a)`. -/
def coprimeMoebiusSigmaSum (δ Y : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Y, if Nat.Coprime a δ then moebiusSigma a else 0

/-- `S(X) = Σ_{a,b ≤ X, (a,b)=1} w(a) w(b)`. -/
def coprimePairMoebiusSigmaSum (X : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, if Nat.Coprime a b then moebiusSigma a * moebiusSigma b else 0

theorem sigma_one_pos {n : ℕ} (hn : n ≠ 0) : 0 < (sigma 1 n : ℝ) := by
  have : 0 < sigma 1 n := by
    rw [sigma_one_apply]
    exact Finset.sum_pos (fun d hd => Nat.pos_of_mem_divisors hd)
      ⟨1, Nat.one_mem_divisors.mpr hn⟩
  exact_mod_cast this

theorem le_sigma_one (n : ℕ) : (n : ℝ) ≤ (sigma 1 n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : n ≤ sigma 1 n := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (fun d _ => Nat.zero_le d) (Nat.mem_divisors_self n hn.ne')
  exact_mod_cast this

theorem abs_moebiusSigma_le (n : ℕ) : |moebiusSigma n| ≤ (n : ℝ)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [moebiusSigma]
  have hσ := sigma_one_pos hn.ne'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold moebiusSigma
  rw [abs_div, abs_of_pos hσ]
  have hμ : |(moebius n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  calc |(moebius n : ℝ)| / (sigma 1 n : ℝ) ≤ 1 / (sigma 1 n : ℝ) :=
        div_le_div_of_nonneg_right hμ hσ.le
    _ ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hn' (le_sigma_one n)
    _ = (n : ℝ)⁻¹ := one_div _

theorem moebiusSigma_mul {m n : ℕ} (h : Nat.Coprime m n) :
    moebiusSigma (m * n) = moebiusSigma m * moebiusSigma n := by
  unfold moebiusSigma
  rw [isMultiplicative_moebius.map_mul_of_coprime h, isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  rw [mul_div_mul_comm]

/-- Off coprime cofactors the weight vanishes at multiples of a squarefree `δ`. -/
theorem moebiusSigma_mul_of_not_coprime {δ a : ℕ} (h : ¬ Nat.Coprime a δ) :
    moebiusSigma (δ * a) = 0 := by
  obtain ⟨p, hp, hpa, hpδ⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hsq : ¬ Squarefree (δ * a) := by
    intro hs
    have := hs p (Nat.mul_dvd_mul hpδ hpa)
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  simp [moebiusSigma, moebius_eq_zero_of_not_squarefree hsq]

end

end GaloisForLFunctions.BezoutValuationIncidence
