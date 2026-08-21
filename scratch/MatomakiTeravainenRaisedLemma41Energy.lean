import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedLemma41

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

theorem scratch_exists_lemma41_huxley_raised_energy
    {eps : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ) (N A ell : ℕ) (rho kappa Q : ℝ)
        (a : Fin N → ℂ) (S : Finset ℝ),
      T₀ ≤ T → 1 ≤ Q → Q ^ 3 ≤ T ^ (eps ^ 2) →
      1 ≤ A → 0 < ell → 0 ≤ rho →
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
        2400 * Q ≤ ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ^
          ((1 : ℝ) / 2 - 2 * huxleyThresholdLossSigma
            (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ))) →
      (∀ r : Fin (ell + 1),
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) ≤ rho + kappa) →
      (∀ n : Fin N, a n ≠ 0 →
        A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A) →
      (∀ r : Fin (ell + 1),
        ‖dyadicWeightedCoeff (N ^ ell) (convPow N ell a) 1
          (A ^ ell * 2 ^ (r : ℕ))‖ ^ 2 ≤
            Q / ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ t ∈ S, ((A ^ ell : ℕ) : ℝ) ^ (-rho) ≤
        ‖raisedDirichletValue N ell a 1 t‖) →
      (S.card : ℝ) ≤ (ell + 1 : ℝ) *
        T ^ (2 * (rho + kappa) - eps ^ 2 / 5) := by
  obtain ⟨T₀, hT₀1, hlargeT⟩ :=
    exists_lemma41_largeness (eps := eps) (D := (1 : ℝ)) heps
  refine ⟨T₀, hT₀1, ?_⟩
  intro T N A ell rho kappa Q a S hT hQ1 hQ3 hA hell hrho hN hNlo hNhi
    hsl hsh hthr hcorr hsupp hmass hsep hspread hlarge
  have hT1 : 1 ≤ T := hT₀1.trans hT
  obtain ⟨hConst, hLog, _hOne⟩ := hlargeT T hT
  have hcard := card_raised_large_set_le_sum_block_counts hA hell a hsupp hrho S hlarge
  calc
    (S.card : ℝ) ≤ ∑ r : Fin (ell + 1),
        ((raisedDyadicBlockLargeSet S N A ell a rho r).card : ℝ) := hcard
    _ ≤ ∑ _r : Fin (ell + 1),
        T ^ (2 * (rho + kappa) - eps ^ 2 / 5) := by
      apply Finset.sum_le_sum
      intro r _hr
      have hcount := lemma41_huxley_energy
        (dyadicWeightedCoeff (N ^ ell) (convPow N ell a) 1
          (A ^ ell * 2 ^ (r : ℕ)))
        (raisedDyadicBlockLargeSet S N A ell a rho r)
        (le_trans (by norm_num) (hN r)) heps hepss hT1 hConst hLog hQ1 hQ3
        (hNlo r) (hNhi r) (hsl r) (hsh r) (hmass r) (hthr r)
        (by
          intro x hx y hy hxy
          exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy)
        (by
          intro x hx y hy
          exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1)
        (by
          intro x hx
          rw [inner_dyadicDirRow_dyadicWeightedCoeff_eq_blockPoly]
          rw [rpow_neg_huxleyThresholdLossSigma (hN r) (by positivity)]
          exact (Finset.mem_filter.1 hx).2)
      exact hcount.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by
        have := hcorr r
        linarith))
    _ = (ell + 1 : ℝ) * T ^ (2 * (rho + kappa) - eps ^ 2 / 5) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rfl

end RHTower.Sieve
