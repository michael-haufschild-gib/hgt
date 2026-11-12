import GaloisForLFunctions.LogarithmicChowla.CircleBound
import GaloisForLFunctions.PrimeExponentialSums.PrimesOffMajorArcs

/-!
# (PRIME): the prime kernel off the major arcs

`K_k(β) = |𝐏_k|⁻¹ Σ_{p ∈ 𝐏_k} e(pβ)`, `𝐏_k` the primes in `(2^k, 2^{k+1}]`.

* `exists_norm_primeKernel_le`: for every `0 < η ≤ 1` there are `Q₀`, `W > 0` and `k₁` with
  `|K_k(β)| ≤ η` for `k ≥ k₁`, unless `|β − a/q| ≤ W/2^k` for some `a ∈ ℤ`, `q ≤ Q₀`
  (`PrimeExponentialSums.exists_off_major_arcs` at `N = 2^k`).
* `exists_abs_avg_corr_le`: with the circle bound, for every `0 < η ≤ 1` there are `Q₀`, `W`,
  `k₁` such that for `k ≥ k₁` and `T ≥ 1` with `4TW ≤ 2^k`:
  `|avg_{p ∈ 𝐏_k} c(ph)| ≤ η + 4 Σ_{s ≤ hQ₀} Σ_{b < s} V(b/s, T)`.
-/

open Finset Filter
open GaloisForLFunctions.PrimeExponentialSums

namespace GaloisForLFunctions.LogarithmicChowla

noncomputable section
set_option autoImplicit false

variable {U : Ultrafilter ℝ}

theorem primesAt_eq (k : ℕ) : primesAt k = (Ioc (2 ^ k) (2 * 2 ^ k)).filter Nat.Prime := by
  rw [primesAt, pow_succ, mul_comm]

/-- **(PRIME).** The prime kernel is small off the major arcs of bounded denominator. -/
theorem exists_norm_primeKernel_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ Q₀ : ℕ, ∃ W : ℝ, 0 < W ∧ ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ β : ℝ,
      (∀ q ∈ Icc 1 Q₀, ∀ a : ℤ, W / 2 ^ k < |β - a / q|) → ‖primeKernel k β‖ ≤ η := by
  obtain ⟨Q₀, W, hW, hev⟩ := exists_off_major_arcs hη hη1
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)).eventually hev)
  refine ⟨Q₀, W, hW, k₁, fun k hk β hβ => ?_⟩
  have h := hk₁ k hk β (fun q hq a => by
    have := hβ q hq a
    push_cast
    exact this)
  rw [← primesAt_eq] at h
  have hc : (0 : ℝ) < (primesAt k).card := by exact_mod_cast card_primesAt_pos k
  have hs : ∑ p : primesAt k, ex ((p : ℕ) * β) = ∑ p ∈ primesAt k, ex (p * β) :=
    Finset.sum_coe_sort (s := primesAt k) (f := fun p : ℕ => ex (p * β))
  rw [primeKernel, norm_div, Complex.norm_natCast, div_le_iff₀ hc, hs]
  exact h

/-- **The circle bound with (PRIME).** For every `0 < η ≤ 1` there are `Q₀`, `W > 0`, `k₁` such
that for `k ≥ k₁` and every `T ≥ 1` with `4TW ≤ 2^k`:
`|avg_{p ∈ 𝐏_k} c(ph)| ≤ η + 4 Σ_{s ≤ hQ₀} Σ_{b < s} V(b/s, T)`. -/
theorem exists_abs_avg_corr_le (hU : (U : Filter ℝ) ≤ atTop) (h : ℕ) (hh : 0 < h) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ Q₀ : ℕ, ∃ W : ℝ, 0 < W ∧ ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ T : ℕ, 0 < T → 4 * T * W ≤ 2 ^ k →
      |(∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card|
        ≤ η + 4 * ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s, twistVar U (b / s) T := by
  obtain ⟨Q₀, W, hW, k₁, hK⟩ := exists_norm_primeKernel_le hη hη1
  exact ⟨Q₀, W, hW, k₁, fun k hk T hT hTW =>
    abs_avg_corr_le hU h k Q₀ T hh hT hη.le hTW (hK k hk)⟩

end

end GaloisForLFunctions.LogarithmicChowla
