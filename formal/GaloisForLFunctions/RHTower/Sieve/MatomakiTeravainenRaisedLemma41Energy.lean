import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedLemma41
import GaloisForLFunctions.RHTower.Sieve.MaynardWeightedEnergy
import GaloisForLFunctions.RHTower.Sieve.EnergyLargeValuesBound

/-!
# Energy-form raised Lemma 4.1 for Matomäki--Teräväinen Proposition 4.2

The fixed pointwise coefficient bound in the first raised Lemma 4.1 assembler is too restrictive
for the divisor-bounded coefficients of the published Type-II theorem. This module instead uses
the intrinsic weighted Hilbert mass. A common subpower factor `Q` may grow with `T`, provided
`Q³ ≤ T^(ε²)`, exactly matching Huxley's cubic energy term.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- Raw convolution energy `≤ Q A^ell` gives the normalized weighted mass `≤ Q/D` on every
literal raised block `D = A^ell 2^r`. -/
theorem raised_dyadic_block_mass_le_of_raw_energy
    {N A ell : ℕ} (hA : 1 ≤ A) (a : Fin N → ℂ)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (henergy : ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
      Q * ((A ^ ell : ℕ) : ℝ))
    (r : Fin (ell + 1)) :
    ‖dyadicWeightedCoeff (N ^ ell) (convPow N ell a) 1
      (A ^ ell * 2 ^ (r : ℕ))‖ ^ 2 ≤
        Q / ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) := by
  let D : ℕ := A ^ ell * 2 ^ (r : ℕ)
  have hD : 1 ≤ D := by
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero ell (by omega)) (pow_ne_zero (r : ℕ) (by norm_num)))
  have hbase := norm_dyadicWeightedCoeff_sq_le_edge_weight
    (N ^ ell) D (convPow N ell a) (sigma := (1 : ℝ)) (by norm_num) hD
  have hweighted :
      ‖dyadicWeightedCoeff (N ^ ell) (convPow N ell a) 1 D‖ ^ 2 ≤
        (((D : ℝ) ^ (-(1 : ℝ))) ^ 2) *
          (Q * ((A ^ ell : ℕ) : ℝ)) :=
    hbase.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg _))
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hAD : (((A ^ ell : ℕ) : ℝ)) ≤ (D : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right (A ^ ell) (pow_pos (by omega) (r : ℕ))
  rw [Real.rpow_neg_one] at hweighted
  refine hweighted.trans ?_
  change (D : ℝ)⁻¹ ^ 2 * (Q * ((A ^ ell : ℕ) : ℝ)) ≤ Q / (D : ℝ)
  have hfrac : ((A ^ ell : ℕ) : ℝ) / (D : ℝ) ^ 2 ≤ 1 / (D : ℝ) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hD0) hD0]
    nlinarith
  calc
    (D : ℝ)⁻¹ ^ 2 * (Q * ((A ^ ell : ℕ) : ℝ)) =
        Q * (((A ^ ell : ℕ) : ℝ) / (D : ℝ) ^ 2) := by field_simp
    _ ≤ Q * (1 / (D : ℝ)) := mul_le_mul_of_nonneg_left hfrac hQ
    _ = Q / (D : ℝ) := by ring

/-- Raised Lemma 4.1 with subpower coefficient energy, exact block cover, threshold loss, and
summation over the `ell+1` literal dyadic blocks, from Lemma 4.1 up to any exponent `cap`. -/
theorem exists_lemma41_raised_energy {cap : ℝ} (hLV : EnergyLargeValuesBound cap)
    {eps : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ) (N A ell : ℕ) (rho kappa Q : ℝ)
        (a : Fin N → ℂ) (S : Finset ℝ),
      T₀ ≤ T → 1 ≤ Q → Q ^ 3 ≤ T ^ (eps ^ 2) →
      1 ≤ A → 0 < ell → 0 ≤ rho →
      (∀ r : Fin (ell + 1), 2 ≤ A ^ ell * 2 ^ (r : ℕ)) →
      (∀ r : Fin (ell + 1),
        T ^ ((9 : ℝ) / 11 - 10 * eps) ≤
          ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) →
      (∀ r : Fin (ell + 1),
        ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ≤ T ^ (1 - eps)) →
      (∀ r : Fin (ell + 1),
        5 * eps ≤ huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ)) →
      (∀ r : Fin (ell + 1),
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) ≤ cap - 5 * eps) →
      (∀ r : Fin (ell + 1),
        2400 * Q ≤ ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ^
          ((1 : ℝ) / 2 - 2 * huxleyThresholdLossSigma
            (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ))) →
      (∀ r : Fin (ell + 1),
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) ≤ rho + kappa) →
      (∀ n : Fin N, a n ≠ 0 →
        A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A) →
      (∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
        Q * ((A ^ ell : ℕ) : ℝ)) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ t ∈ S, ((A ^ ell : ℕ) : ℝ) ^ (-rho) ≤
        ‖raisedDirichletValue N ell a 1 t‖) →
      (S.card : ℝ) ≤ (ell + 1 : ℝ) *
        T ^ (2 * (rho + kappa) - eps ^ 2 / 5) := by
  obtain ⟨T₀, hT₀1, hLVT⟩ := hLV eps heps hepss
  refine ⟨T₀, hT₀1, ?_⟩
  intro T N A ell rho kappa Q a S hT hQ1 hQ3 hA hell hrho hN hNlo hNhi
    hsl hsh hthr hcorr hsupp henergy hsep hspread hlarge
  have hT1 : 1 ≤ T := hT₀1.trans hT
  have hcard := card_raised_large_set_le_sum_block_counts hA hell a hsupp hrho S hlarge
  calc
    (S.card : ℝ) ≤ ∑ r : Fin (ell + 1),
        ((raisedDyadicBlockLargeSet S N A ell a rho r).card : ℝ) := hcard
    _ ≤ ∑ _r : Fin (ell + 1),
        T ^ (2 * (rho + kappa) - eps ^ 2 / 5) := by
      apply Finset.sum_le_sum
      intro r _hr
      have hcount := hLVT T (A ^ ell * 2 ^ (r : ℕ))
        (huxleyThresholdLossSigma (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ)) Q
        (dyadicWeightedCoeff (N ^ ell) (convPow N ell a) 1
          (A ^ ell * 2 ^ (r : ℕ)))
        (raisedDyadicBlockLargeSet S N A ell a rho r)
        hT hQ1 hQ3 (hNlo r) (hNhi r) (hsl r) (hsh r)
        (raised_dyadic_block_mass_le_of_raw_energy hA a
          (le_trans (by norm_num) hQ1) henergy r) (hthr r)
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
