import GaloisForLFunctions.RHTower.Sieve.MaynardRaisedDyadic
import GaloisForLFunctions.RHTower.Sieve.HuxleyDirichletLargeValues

/-!
# Exact block cover for the raised branch of Matomäki--Teräväinen Proposition 4.2

The short first factor is raised until its length enters the density range. Its power is not one
dyadic Dirichlet block: it has exactly `ell+1` blocks. This module proves the literal row-to-block
identity, performs the pointwise pigeonhole with its exact threshold loss, and covers an arbitrary
finite large-value set by those fixed blocks. No point-dependent block is hidden downstream.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The weighted row used by the raised decomposition is literally the Huxley block polynomial. -/
theorem inner_dyadicDirRow_dyadicWeightedCoeff_eq_blockPoly
    (M : ℕ) (b : Fin M → ℂ) (sigma t : ℝ) (D : ℕ) :
    ⟪dyadicDirRow D t, dyadicWeightedCoeff M b sigma D⟫_ℂ =
      blockPoly D (anchoredCoeff M b) sigma t := by
  rw [inner_dyadicDirRow_dyadicWeightedCoeff, blockPoly]
  rfl

/-- A large raised value forces one of its `ell+1` literal dyadic blocks to be large. -/
theorem exists_raised_dyadic_block_large
    {N A ell : ℕ} (hA : 1 ≤ A) (hell : 0 < ell)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    {sigma t V : ℝ}
    (hbig : V ≤ ‖raisedDirichletValue N ell a sigma t‖) :
    ∃ r : Fin (ell + 1),
      V / (ell + 1 : ℝ) ≤
        ‖blockPoly (A ^ ell * 2 ^ (r : ℕ))
          (anchoredCoeff (N ^ ell) (convPow N ell a)) sigma t‖ := by
  have hsum := hbig.trans
    (norm_raisedDirichletValue_le_sum_dyadic hA a hsupp sigma t)
  by_contra hcon
  push Not at hcon
  have hlt : (∑ r : Fin (ell + 1),
      ‖⟪dyadicDirRow (A ^ ell * 2 ^ (r : ℕ)) t,
        dyadicWeightedCoeff (N ^ ell) (convPow N ell a) sigma
          (A ^ ell * 2 ^ (r : ℕ))⟫_ℂ‖) < V := by
    calc
      (∑ r : Fin (ell + 1),
          ‖⟪dyadicDirRow (A ^ ell * 2 ^ (r : ℕ)) t,
            dyadicWeightedCoeff (N ^ ell) (convPow N ell a) sigma
              (A ^ ell * 2 ^ (r : ℕ))⟫_ℂ‖)
          < ∑ _r : Fin (ell + 1), V / (ell + 1 : ℝ) := by
              exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun r _ => by
                rw [inner_dyadicDirRow_dyadicWeightedCoeff_eq_blockPoly]
                exact hcon r
      _ = V := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hpos : (0 : ℝ) < ell + 1 := by positivity
        field_simp
        push_cast
        ring
  linarith

/-- Large-value set of one literal block in a raised factor. -/
noncomputable def raisedDyadicBlockLargeSet
    (S : Finset ℝ) (N A ell : ℕ) (a : Fin N → ℂ) (rho : ℝ)
    (r : Fin (ell + 1)) : Finset ℝ :=
  S.filter fun t =>
    ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ^ (-rho) / (ell + 1 : ℝ) ≤
      ‖blockPoly (A ^ ell * 2 ^ (r : ℕ))
        (anchoredCoeff (N ^ ell) (convPow N ell a)) 1 t‖

/-- A raised large-value set is covered by its fixed `ell+1` literal Huxley blocks. -/
theorem subset_biUnion_raisedDyadicBlockLargeSet
    {N A ell : ℕ} (hA : 1 ≤ A) (hell : 0 < ell)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    {rho : ℝ} (hrho : 0 ≤ rho) (S : Finset ℝ)
    (hlarge : ∀ t ∈ S,
      ((A ^ ell : ℕ) : ℝ) ^ (-rho) ≤
        ‖raisedDirichletValue N ell a 1 t‖) :
    S ⊆ (Finset.univ : Finset (Fin (ell + 1))).biUnion
      (raisedDyadicBlockLargeSet S N A ell a rho) := by
  classical
  intro t ht
  obtain ⟨r, hr⟩ := exists_raised_dyadic_block_large hA hell a hsupp
    (hbig := hlarge t ht)
  rw [Finset.mem_biUnion]
  refine ⟨r, Finset.mem_univ r, ?_⟩
  rw [raisedDyadicBlockLargeSet, Finset.mem_filter]
  refine ⟨ht, ?_⟩
  have hbase : (0 : ℝ) < ((A ^ ell : ℕ) : ℝ) := by positivity
  have hlength : ((A ^ ell : ℕ) : ℝ) ≤
      ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right (A ^ ell) (pow_pos (by omega) (r : ℕ))
  have hpow : ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ^ (-rho) ≤
      ((A ^ ell : ℕ) : ℝ) ^ (-rho) :=
    Real.rpow_le_rpow_of_nonpos hbase hlength (by linarith)
  have hden : (0 : ℝ) < (ell : ℝ) + 1 := by positivity
  exact (div_le_div_of_nonneg_right hpow hden.le).trans hr

/-- Cardinality transfer through the exact raised-block cover. -/
theorem card_raised_large_set_le_sum_block_counts
    {N A ell : ℕ} (hA : 1 ≤ A) (hell : 0 < ell)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    {rho : ℝ} (hrho : 0 ≤ rho) (S : Finset ℝ)
    (hlarge : ∀ t ∈ S,
      ((A ^ ell : ℕ) : ℝ) ^ (-rho) ≤
        ‖raisedDirichletValue N ell a 1 t‖) :
    (S.card : ℝ) ≤ ∑ r : Fin (ell + 1),
      ((raisedDyadicBlockLargeSet S N A ell a rho r).card : ℝ) := by
  classical
  have hcover := subset_biUnion_raisedDyadicBlockLargeSet hA hell a hsupp hrho S hlarge
  have hcard : S.card ≤ ∑ r : Fin (ell + 1),
      (raisedDyadicBlockLargeSet S N A ell a rho r).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  exact_mod_cast hcard

end RHTower.Sieve
