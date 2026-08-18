import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedBlockCover
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma41ThresholdLoss

/-!
# Lemma 4.1 for the raised branch of Matomäki--Teräväinen Proposition 4.2

This closes the density-count assembly after raising the shorter Type-II factor. Every one of the
`ell+1` literal dyadic blocks is passed through Lemma 4.1 with the exact pigeonhole exponent loss;
the block counts are then summed without a point-dependent choice. The result exposes only the
published length, coefficient, separation, threshold, and exponent-range checks.
-/

namespace RHTower.Sieve

open Finset

/-- Lemma 4.1 on a raised dyadic factor, including finite-block pigeonholing and summation. -/
theorem exists_lemma41_huxley_raised
    {eps D : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) (hD1 : 1 ≤ D) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ) (N A ell : ℕ) (rho kappa : ℝ)
        (a : Fin N → ℂ) (S : Finset ℝ),
      T₀ ≤ T → 1 ≤ A → 0 < ell → 0 ≤ rho →
      (∀ r : Fin (ell + 1), 2 ≤ A ^ ell * 2 ^ (r : ℕ)) →
      (∀ r : Fin (ell + 1),
        T ^ ((9 : ℝ) / 11) ≤ ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) →
      (∀ r : Fin (ell + 1),
        ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ≤ T ^ (1 - eps)) →
      (∀ r : Fin (ell + 1),
        5 * eps ≤ huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ)) →
      (∀ r : Fin (ell + 1),
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) ≤ 7 / 32 - 5 * eps) →
      (∀ r : Fin (ell + 1),
        2400 * D ^ 2 ≤ ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ^
          ((1 : ℝ) / 2 - 2 * huxleyThresholdLossSigma
            (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ))) →
      (∀ r : Fin (ell + 1),
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) ≤ rho + kappa) →
      (∀ n : Fin N, a n ≠ 0 →
        A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A) →
      (∀ r : Fin (ell + 1), ∀ n ∈ Finset.Ico
        (A ^ ell * 2 ^ (r : ℕ)) (2 * (A ^ ell * 2 ^ (r : ℕ))),
        ‖anchoredCoeff (N ^ ell) (convPow N ell a) n‖ ≤ D) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ t ∈ S, ((A ^ ell : ℕ) : ℝ) ^ (-rho) ≤
        ‖raisedDirichletValue N ell a 1 t‖) →
      (S.card : ℝ) ≤ (ell + 1 : ℝ) *
        T ^ (2 * (rho + kappa) - eps ^ 2 / 5) := by
  obtain ⟨T₀, hT₀1, hbase⟩ :=
    exists_lemma41_huxley_threshold_loss heps hepss hD1
  refine ⟨T₀, hT₀1, ?_⟩
  intro T N A ell rho kappa a S hT hA hell hrho hN hNlo hNhi hsl hsh hthr
    hcorr hsupp hc hsep hspread hlarge
  have hT1 : 1 ≤ T := hT₀1.trans hT
  have hcard := card_raised_large_set_le_sum_block_counts hA hell a hsupp hrho S hlarge
  calc
    (S.card : ℝ) ≤ ∑ r : Fin (ell + 1),
        ((raisedDyadicBlockLargeSet S N A ell a rho r).card : ℝ) := hcard
    _ ≤ ∑ _r : Fin (ell + 1),
        T ^ (2 * (rho + kappa) - eps ^ 2 / 5) := by
      apply Finset.sum_le_sum
      intro r _hr
      have hcount := hbase T (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ)
        (anchoredCoeff (N ^ ell) (convPow N ell a))
        (raisedDyadicBlockLargeSet S N A ell a rho r)
        hT (hN r) (by norm_num) (hNlo r) (hNhi r) (hsl r) (hsh r)
        (hthr r) (hc r)
        (by
          intro x hx y hy hxy
          exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy)
        (by
          intro x hx y hy
          exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1)
        (by
          intro x hx
          exact (Finset.mem_filter.1 hx).2)
      exact hcount.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by
        have := hcorr r
        linarith))
    _ = (ell + 1 : ℝ) * T ^ (2 * (rho + kappa) - eps ^ 2 / 5) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rfl

end RHTower.Sieve
