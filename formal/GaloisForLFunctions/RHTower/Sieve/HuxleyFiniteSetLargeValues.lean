import GaloisForLFunctions.RHTower.Sieve.HuxleyLargeValues

/-!
# Huxley large values on an arbitrary finite subset

Pointwise box/group selection colors a common separated ordinate set.  A color fibre is generally
not an initial segment.  The original range-indexed Huxley theorem therefore cannot be summed over
colors without an unstated reindexing argument.  This module proves the exact arbitrary-finset
form.  Harmonic separation is inherited from the ambient range, while Schur and absorption use the
actual fibre cardinality.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- Huxley Gram-row bound restricted to an arbitrary subset of an ambient separated range. -/
theorem sum_norm_inner_dyadicDirRow_le_huxley_finset
    {N K : ℕ} (hN : 1 ≤ N) {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta U T B : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T)
    (hU : 0 < U) (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hB : logDyadicSecondEnvelope N U T ≤ B) (hB1 : 1 ≤ B)
    {r : ℕ} (hr : r ∈ S) :
    ∑ s ∈ S, ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
      ≤ (N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) *
          ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) + (S.card : ℝ) * B := by
  have hrK : r < K := Finset.mem_range.mp (hS hr)
  have hoff : ∀ s ∈ S.erase r,
      ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
        ≤ 6 * Real.pi * (N : ℝ) * (1 / |lam s - lam r|) + B := by
    intro s hs
    have hsS := Finset.mem_of_mem_erase hs
    have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
    have htu : lam r ≠ lam s := by
      rcases lt_or_gt_of_ne hsr with hsr' | hrs'
      · exact ne_of_gt (lt_of_gap hdelta hgap hsr')
      · exact ne_of_lt (lt_of_gap hdelta hgap hrs')
    have hpoint := norm_inner_dyadicDirRow_le_huxley hN htu hU
      (hdiam r hr s hsS) hnear hlamT hB hB1
    convert hpoint using 1 <;> ring
  have hoffsum : ∑ s ∈ S.erase r,
        ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
      ≤ (6 * Real.pi * (N : ℝ)) *
          ∑ s ∈ S.erase r, 1 / |lam s - lam r| + ((S.erase r).card : ℝ) * B := by
    calc
      ∑ s ∈ S.erase r,
          ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
          ≤ ∑ s ∈ S.erase r,
              (6 * Real.pi * (N : ℝ) * (1 / |lam s - lam r|) + B) :=
            Finset.sum_le_sum hoff
      _ = (6 * Real.pi * (N : ℝ)) *
            ∑ s ∈ S.erase r, 1 / |lam s - lam r| + ((S.erase r).card : ℝ) * B := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have heraseSub : S.erase r ⊆ (Finset.range K).erase r := by
    intro s hs
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hs).1, hS (Finset.mem_of_mem_erase hs)⟩
  have hinvSubset : ∑ s ∈ S.erase r, 1 / |lam s - lam r| ≤
      ∑ s ∈ (Finset.range K).erase r, 1 / |lam s - lam r| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg heraseSub
    intro s _hs _hnot
    positivity
  have hinvFull := sum_inv_abs_dist_le hdelta hgap hrK
  have hinv : ∑ s ∈ S.erase r, 1 / |lam s - lam r| ≤
      (2 / delta) * ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) :=
    hinvSubset.trans hinvFull
  have hB0 : 0 ≤ B := (by linarith : 0 ≤ B)
  have hcard : (((S.erase r).card : ℕ) : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset r S)
  have hoffsum' : ∑ s ∈ S.erase r,
        ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
      ≤ (12 * Real.pi * (N : ℝ) / delta) *
          ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) + (S.card : ℝ) * B := by
    refine hoffsum.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 6 * Real.pi * (N : ℝ))
    have h2 := mul_le_mul_of_nonneg_right hcard hB0
    calc
      (6 * Real.pi * (N : ℝ)) * ∑ s ∈ S.erase r, 1 / |lam s - lam r| +
          ((S.erase r).card : ℝ) * B
        ≤ (6 * Real.pi * (N : ℝ)) *
            ((2 / delta) * ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)) +
              (S.card : ℝ) * B := add_le_add h1 h2
      _ = (12 * Real.pi * (N : ℝ) / delta) *
            ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) + (S.card : ℝ) * B := by ring
  rw [← Finset.sum_erase_add _ _ hr]
  have hdiag : ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam r)⟫_ℂ‖ = (N : ℝ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa using norm_dyadicDirRow_sq N (lam r)
  rw [hdiag]
  linarith

/-- Huxley's local large-values theorem on an arbitrary color fibre. -/
theorem huxley_local_large_values_finset
    {N K : ℕ} (hN : 1 ≤ N) (a : EuclideanSpace ℂ (Fin N))
    {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta U T B V G : ℝ}
    (hdelta : 0 < delta) (hU : 0 < U) (hV : 0 < V)
    (hmass : ‖a‖ ^ 2 ≤ G)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hB : logDyadicSecondEnvelope N U T ≤ B) (hB1 : 1 ≤ B)
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T)
    (hbig : ∀ r ∈ S, V ≤ ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖)
    (habsorb : G * B ≤ V ^ 2 / 2) :
    (S.card : ℝ) * V ^ 2 ≤
      2 * G * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) *
        ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)) := by
  let base : ℝ := (N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) *
    ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)
  let Delta : ℝ := base + (S.card : ℝ) * B
  have hDelta0 : 0 ≤ Delta := by
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by positivity
    have hB0 : 0 ≤ B := by linarith
    dsimp [Delta, base]
    positivity
  have hrow : ∀ r ∈ S,
      ∑ s ∈ S, ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖ ≤ Delta := by
    intro r hr
    simpa [Delta, base] using sum_norm_inner_dyadicDirRow_le_huxley_finset
      hN hS hdelta hgap hdiam hU hnear hlamT hB hB1 hr
  have hbessel := sum_norm_inner_sq_le_of_schur S
    (fun r => dyadicDirRow N (lam r)) hDelta0 hrow a
  have hupper : ∑ r ∈ S, ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖ ^ 2 ≤ Delta * G :=
    hbessel.trans (mul_le_mul_of_nonneg_left hmass hDelta0)
  have hlower : (S.card : ℝ) * V ^ 2 ≤
      ∑ r ∈ S, ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖ ^ 2 := by
    calc
      (S.card : ℝ) * V ^ 2 = ∑ _r ∈ S, V ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun r hr => pow_le_pow_left₀ hV.le (hbig r hr) 2
  have hmaster := hlower.trans hupper
  have habsorb' := mul_le_mul_of_nonneg_left habsorb (Nat.cast_nonneg S.card)
  dsimp [Delta, base] at hmaster ⊢
  nlinarith

/-- Multi-block Huxley theorem on an arbitrary color fibre. -/
theorem huxley_multiblock_large_values_finset
    {ι : Type*} [Fintype ι] {K : ℕ}
    (N : ι → ℕ) (hN : ∀ q, 1 ≤ N q)
    (a : ∀ q, EuclideanSpace ℂ (Fin (N q)))
    (G U B : ι → ℝ) {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hV : 0 < V)
    (hmass : ∀ q, ‖a q‖ ^ 2 ≤ G q)
    (hU : ∀ q, 0 < U q)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hnear : ∀ q, 3 * U q ≤ 4 * Real.pi * (N q : ℝ))
    (hlamT : ∀ q, logDyadicLambda (N q) T ≤ 1)
    (hB : ∀ q, logDyadicSecondEnvelope (N q) (U q) T ≤ B q)
    (hB1 : ∀ q, 1 ≤ B q)
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T)
    (hbig : ∀ r ∈ S,
      V ≤ ∑ q : ι, ‖⟪dyadicDirRow (N q) (lam r), a q⟫_ℂ‖)
    (habsorb : (Fintype.card ι : ℝ) * ∑ q : ι, G q * B q ≤ V ^ 2 / 2) :
    (S.card : ℝ) * V ^ 2 ≤
      2 * (Fintype.card ι : ℝ) * ∑ q : ι,
        G q * ((N q : ℝ) + (12 * Real.pi * (N q : ℝ) / delta) *
          ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)) := by
  let base : ι → ℝ := fun q => (N q : ℝ) + (12 * Real.pi * (N q : ℝ) / delta) *
    ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)
  let Delta : ι → ℝ := fun q => base q + (S.card : ℝ) * B q
  have hDelta0 : ∀ q, 0 ≤ Delta q := by
    intro q
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by positivity
    have hB0 : 0 ≤ B q := by linarith [hB1 q]
    dsimp [Delta, base]
    positivity
  have henergy : ∀ q, ∑ r ∈ S,
      ‖⟪dyadicDirRow (N q) (lam r), a q⟫_ℂ‖ ^ 2 ≤ Delta q * G q := by
    intro q
    have hrow : ∀ r ∈ S,
        ∑ s ∈ S, ‖⟪dyadicDirRow (N q) (lam r), dyadicDirRow (N q) (lam s)⟫_ℂ‖
          ≤ Delta q := by
      intro r hr
      simpa [Delta, base] using sum_norm_inner_dyadicDirRow_le_huxley_finset
        (hN q) hS hdelta hgap hdiam (hU q) (hnear q) (hlamT q) (hB q) (hB1 q) hr
    have hbessel := sum_norm_inner_sq_le_of_schur S
      (fun r => dyadicDirRow (N q) (lam r)) (hDelta0 q) hrow (a q)
    exact hbessel.trans (mul_le_mul_of_nonneg_left (hmass q) (hDelta0 q))
  have hpoint : ∀ r ∈ S, V ^ 2 ≤ (Fintype.card ι : ℝ) *
      ∑ q : ι, ‖⟪dyadicDirRow (N q) (lam r), a q⟫_ℂ‖ ^ 2 := by
    intro r hr
    exact (pow_le_pow_left₀ hV.le (hbig r hr) 2).trans
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
        (f := fun q => ‖⟪dyadicDirRow (N q) (lam r), a q⟫_ℂ‖))
  have htotal : (S.card : ℝ) * V ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ q : ι, Delta q * G q := by
    calc
      (S.card : ℝ) * V ^ 2 = ∑ _r ∈ S, V ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ S, (Fintype.card ι : ℝ) *
          ∑ q : ι, ‖⟪dyadicDirRow (N q) (lam r), a q⟫_ℂ‖ ^ 2 :=
        Finset.sum_le_sum hpoint
      _ = (Fintype.card ι : ℝ) * ∑ q : ι,
          ∑ r ∈ S, ‖⟪dyadicDirRow (N q) (lam r), a q⟫_ℂ‖ ^ 2 := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ (Fintype.card ι : ℝ) * ∑ q : ι, Delta q * G q :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => henergy q)
          (Nat.cast_nonneg _)
  have hsplit : ∑ q : ι, Delta q * G q =
      ∑ q : ι, G q * base q + (S.card : ℝ) * ∑ q : ι, G q * B q := by
    simp only [Delta]
    calc
      ∑ q : ι, (base q + (S.card : ℝ) * B q) * G q =
          ∑ q : ι, (G q * base q + (S.card : ℝ) * (G q * B q)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
      _ = ∑ q : ι, G q * base q +
          ∑ q : ι, (S.card : ℝ) * (G q * B q) := Finset.sum_add_distrib
      _ = ∑ q : ι, G q * base q +
          (S.card : ℝ) * ∑ q : ι, G q * B q := by rw [Finset.mul_sum]
  rw [hsplit] at htotal
  have habsorb' := mul_le_mul_of_nonneg_left habsorb (Nat.cast_nonneg S.card)
  dsimp [base] at htotal ⊢
  nlinarith

end RHTower.Sieve
