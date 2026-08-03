import GaloisForLFunctions.RHTower.Sieve.GeometricSumBound

/-!
# Gram rows of a separated frequency family

The Gram matrix of the exponential rows `n ↦ ξ_r^n`, `n < N`, has entries

`⟪φ_r, φ_t⟫ = ∑_{n < N} conj(ξ_r)^n ξ_t^n = ∑_{n < N} (conj(ξ_r) ξ_t)^n`.

On the diagonal the ratio is `1` and the entry is exactly `N`; off the diagonal the ratio is a
unimodular number different from one, and the geometric sum bound caps the entry by twice the
reciprocal separation.  So a row of the Gram matrix is bounded by

`N + ∑_{t ≠ r} 2 / ‖conj(ξ_r) ξ_t - 1‖`.

This is the only analytic input a large sieve inequality needs: `AlmostOrthogonality.lean` turns a
row bound into the bilinear inequality, and `LargeSieveDuality.lean` turns that into the Bessel
form.  The remaining `log` loss against the sharp constant `N + δ^{-1}` sits entirely in the
harmonic sum of reciprocal separations, not in any of these steps.
-/

namespace RHTower.Sieve

open Finset

/-- The diagonal Gram entry of a unimodular frequency is the length. -/
theorem sum_conj_pow_mul_pow_self {ξ : ℂ} (hξ : ‖ξ‖ = 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, (starRingEnd ℂ) (ξ ^ n) * ξ ^ n = (N : ℂ) := by
  have hone : (starRingEnd ℂ) ξ * ξ = 1 := by
    rw [conj_mul_self, hξ]
    norm_num
  rw [sum_conj_pow_mul_pow ξ ξ N, hone]
  simp

/-- Its norm is the length. -/
theorem norm_sum_conj_pow_mul_pow_self {ξ : ℂ} (hξ : ‖ξ‖ = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) (ξ ^ n) * ξ ^ n‖ = (N : ℝ) := by
  rw [sum_conj_pow_mul_pow_self hξ N]
  simp

/-- **Gram row of a separated frequency family.**  The diagonal contributes the length, each
off-diagonal entry at most twice the reciprocal separation. -/
theorem gram_row_le {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι) (ξ : ι → ℂ)
    (hξ : ∀ r ∈ s, ‖ξ r‖ = 1)
    (hne : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → (starRingEnd ℂ) (ξ r) * ξ t ≠ 1)
    {r : ι} (hr : r ∈ s) :
    ∑ t ∈ s, ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) ((ξ r) ^ n) * (ξ t) ^ n‖
      ≤ (N : ℝ) + ∑ t ∈ s.erase r, 2 / ‖(starRingEnd ℂ) (ξ r) * ξ t - 1‖ := by
  have hsplit : ∑ t ∈ s, ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) ((ξ r) ^ n) * (ξ t) ^ n‖
      = ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) ((ξ r) ^ n) * (ξ r) ^ n‖
        + ∑ t ∈ s.erase r, ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) ((ξ r) ^ n) * (ξ t) ^ n‖ :=
    (Finset.add_sum_erase s
      (fun t => ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) ((ξ r) ^ n) * (ξ t) ^ n‖) hr).symm
  rw [hsplit, norm_sum_conj_pow_mul_pow_self (hξ r hr) N]
  have hstep : ∑ t ∈ s.erase r, ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) ((ξ r) ^ n) * (ξ t) ^ n‖
      ≤ ∑ t ∈ s.erase r, 2 / ‖(starRingEnd ℂ) (ξ r) * ξ t - 1‖ := by
    refine Finset.sum_le_sum ?_
    intro t ht
    obtain ⟨htr, hts⟩ := Finset.mem_erase.1 ht
    exact norm_sum_conj_pow_mul_pow_le (hξ r hr) (le_of_eq (hξ t hts))
      (hne r hr t hts fun hcon => htr hcon.symm) N
  linarith

end RHTower.Sieve
