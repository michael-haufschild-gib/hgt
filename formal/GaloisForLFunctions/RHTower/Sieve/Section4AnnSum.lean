import GaloisForLFunctions.RHTower.Sieve.Section4AnnPiece

/-!
# The annulus sum over the long ladder

Summing the exceptional-annulus bound over the long ladder.  In each term the block scale cancels
between the Route-T bound for the prime polynomial and the Halász–Montgomery bound for the
cofactor, except in the cross term, where one factor of the block's left endpoint survives and is
majorised by the ladder's top.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The annulus sum over the long ladder.** -/
theorem sum_annulus_terms_le {Vk Iann : ℕ → ℝ} {RQ ηQ ρ' B₁ Cw Ej Qtop : ℝ} {LQ : ℕ}
    (hRQ : 0 < RQ) (hηQ : 0 ≤ ηQ) (hB₁ : 0 ≤ B₁) (hCw : 0 ≤ Cw) (hEj : 0 ≤ Ej)
    (hQtop : ∀ k ∈ Finset.range LQ, RQ * (1 + ηQ) ^ k ≤ Qtop)
    (hV : ∀ k ∈ Finset.range LQ, Vk k ≤ ρ' * (RQ * (1 + ηQ) ^ k))
    (hV0 : ∀ k ∈ Finset.range LQ, 0 ≤ Vk k)
    (hI : ∀ k ∈ Finset.range LQ, Iann k
      ≤ (2 * Real.pi)⁻¹ * (2 * (B₁ / (RQ * (1 + ηQ) ^ k)) + Cw * Ej)
          * (B₁ / (RQ * (1 + ηQ) ^ k)))
    (hI0 : ∀ k ∈ Finset.range LQ, 0 ≤ Iann k) :
    (∑ k ∈ Finset.range LQ, Vk k ^ 2 * Iann k)
      ≤ (LQ : ℝ) * (ρ' ^ 2 * ((2 * Real.pi)⁻¹ * (2 * B₁ ^ 2 + Cw * Ej * B₁ * Qtop))) := by
  classical
  have hstep : ∀ k ∈ Finset.range LQ, Vk k ^ 2 * Iann k
      ≤ ρ' ^ 2 * ((2 * Real.pi)⁻¹ * (2 * B₁ ^ 2 + Cw * Ej * B₁ * Qtop)) := by
    intro k hk
    have hbase : (0 : ℝ) < RQ * (1 + ηQ) ^ k := by positivity
    have hterm := ann_term_le (Vk := Vk k) (Qk0 := RQ * (1 + ηQ) ^ k) (B₁ := B₁) (ρ' := ρ')
      (Cw := Cw) (Ej := Ej) (Iann := Iann k) hbase (hV k hk) (hV0 k hk) (hI k hk) (hI0 k hk)
    refine hterm.trans ?_
    have hmono : Cw * Ej * B₁ * (RQ * (1 + ηQ) ^ k) ≤ Cw * Ej * B₁ * Qtop := by
      have hc : (0 : ℝ) ≤ Cw * Ej * B₁ := by positivity
      exact mul_le_mul_of_nonneg_left (hQtop k hk) hc
    have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
    have hinner : (2 * Real.pi)⁻¹ * (2 * B₁ ^ 2 + Cw * Ej * B₁ * (RQ * (1 + ηQ) ^ k))
        ≤ (2 * Real.pi)⁻¹ * (2 * B₁ ^ 2 + Cw * Ej * B₁ * Qtop) :=
      mul_le_mul_of_nonneg_left (by linarith) hpi
    exact mul_le_mul_of_nonneg_left hinner (sq_nonneg _)
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end RHTower.Sieve
