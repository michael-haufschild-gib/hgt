import GaloisForLFunctions.RHTower.Sieve.FrequencyGramRow

/-!
# The large sieve inequality, weak form

Assembling the three preceding modules.  The exponential rows `n ↦ ξ_r^n`, `n < N`, form a family in
`EuclideanSpace ℂ (Fin N)` whose Gram rows are bounded by `FrequencyGramRow.lean`; almost
orthogonality converts that into the bilinear inequality and duality into the Bessel one.  So for
unimodular frequencies `ξ_r`, pairwise distinct, and any `Δ` dominating every

`N + ∑_{t ≠ r} 2 / ‖conj(ξ_r) ξ_t - 1‖`,

both shapes hold:

`‖∑_r c_r φ_r‖² ≤ Δ ∑_r |c_r|²`  and  `∑_r |⟪φ_r, a⟫|² ≤ Δ ‖a‖²`.

For `δ`-separated frequencies the admissible `Δ` is `N + O(δ^{-1} log δ^{-1})`.  The sharp constant
`N + δ^{-1}` is *not* obtained here: the logarithm is the harmonic sum of reciprocal separations,
and removing it is Montgomery–Vaughan's refinement of Hilbert's inequality for the Toeplitz kernel
`1/(m-n)`, which the corpus does not yet own.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The exponential row of a frequency, as a vector of length `N`. -/
noncomputable def expRow (N : ℕ) (ξ : ℂ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun n : Fin N => ξ ^ (n : ℕ))

/-- The Gram entry of two exponential rows is the truncated geometric correlation. -/
theorem inner_expRow (N : ℕ) (ξ η : ℂ) :
    ⟪expRow N ξ, expRow N η⟫_ℂ
      = ∑ n ∈ Finset.range N, (starRingEnd ℂ) (ξ ^ n) * η ^ n := by
  rw [PiLp.inner_apply,
    ← Fin.sum_univ_eq_sum_range (fun n => (starRingEnd ℂ) (ξ ^ n) * η ^ n) N]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [expRow, RCLike.inner_apply]
  ring

/-- The Gram rows of a separated unimodular frequency family. -/
theorem expRow_gram_row_le {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι) (ξ : ι → ℂ)
    (hξ : ∀ r ∈ s, ‖ξ r‖ = 1)
    (hne : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → (starRingEnd ℂ) (ξ r) * ξ t ≠ 1)
    {Δ : ℝ}
    (hΔ : ∀ r ∈ s, (N : ℝ) + ∑ t ∈ s.erase r, 2 / ‖(starRingEnd ℂ) (ξ r) * ξ t - 1‖ ≤ Δ)
    (r : ι) (hr : r ∈ s) :
    ∑ t ∈ s, ‖⟪expRow N (ξ r), expRow N (ξ t)⟫_ℂ‖ ≤ Δ := by
  have hrw : ∀ t ∈ s, ‖⟪expRow N (ξ r), expRow N (ξ t)⟫_ℂ‖
      = ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) ((ξ r) ^ n) * (ξ t) ^ n‖ := by
    intro t _
    rw [inner_expRow]
  rw [Finset.sum_congr rfl hrw]
  exact le_trans (gram_row_le N s ξ hξ hne hr) (hΔ r hr)

/-- **Large sieve, bilinear form.** -/
theorem largeSieve_bilinear {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι) (ξ : ι → ℂ)
    (hξ : ∀ r ∈ s, ‖ξ r‖ = 1)
    (hne : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → (starRingEnd ℂ) (ξ r) * ξ t ≠ 1)
    {Δ : ℝ}
    (hΔ : ∀ r ∈ s, (N : ℝ) + ∑ t ∈ s.erase r, 2 / ‖(starRingEnd ℂ) (ξ r) * ξ t - 1‖ ≤ Δ)
    (c : ι → ℂ) :
    ‖∑ r ∈ s, c r • expRow N (ξ r)‖ ^ 2 ≤ Δ * ∑ r ∈ s, ‖c r‖ ^ 2 :=
  norm_sum_smul_sq_le_of_schur s (fun r => expRow N (ξ r))
    (fun r hr => expRow_gram_row_le N s ξ hξ hne hΔ r hr) c

/-- **Large sieve, Bessel form.** -/
theorem largeSieve_bessel {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι) (ξ : ι → ℂ)
    (hξ : ∀ r ∈ s, ‖ξ r‖ = 1)
    (hne : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → (starRingEnd ℂ) (ξ r) * ξ t ≠ 1)
    {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ r ∈ s, (N : ℝ) + ∑ t ∈ s.erase r, 2 / ‖(starRingEnd ℂ) (ξ r) * ξ t - 1‖ ≤ Δ)
    (a : EuclideanSpace ℂ (Fin N)) :
    ∑ r ∈ s, ‖⟪expRow N (ξ r), a⟫_ℂ‖ ^ 2 ≤ Δ * ‖a‖ ^ 2 :=
  sum_norm_inner_sq_le_of_schur s (fun r => expRow N (ξ r)) hΔ0
    (fun r hr => expRow_gram_row_le N s ξ hξ hne hΔ r hr) a

end RHTower.Sieve
