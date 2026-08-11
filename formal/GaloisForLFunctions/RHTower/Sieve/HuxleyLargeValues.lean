import GaloisForLFunctions.RHTower.Sieve.HuxleyDyadicRow
import GaloisForLFunctions.RHTower.Sieve.SeparatedRowSum

/-!
# Huxley's local large-values estimate

For one-separated frequencies in a window of diameter `T`, split every non-diagonal Gram entry at
frequency `U`.  Kuzmin--Landau contributes the summable kernel `6*pi*N/|u|`; the complementary
second-derivative range contributes the uniform endpoint envelope `B(N,U,T)`.  Thus every Gram row
is bounded by

`N + (12*pi*N/delta) H_K + K*B`,

where `K` is the number of points.  Halasz--Montgomery then absorbs the last term whenever
`G*B <= V^2/2`, leaving the characteristic Huxley count `K V^2 <= 2 G N (1+O(H_K))`.

No moment estimate or analytic hypothesis is assumed: both phase regimes are the unconditional
theorems formalised in the preceding files.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- A single off-diagonal dyadic Gram entry obeys the reciprocal kernel plus the uniform
second-derivative envelope. -/
theorem norm_inner_dyadicDirRow_le_huxley {N : ℕ} (hN : 1 ≤ N)
    {t u U T B : ℝ} (htu : t ≠ u) (hU : 0 < U)
    (hdiam : |u - t| ≤ T) (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hB : logDyadicSecondEnvelope N U T ≤ B) (hB1 : 1 ≤ B) :
    ‖⟪dyadicDirRow N t, dyadicDirRow N u⟫_ℂ‖
      ≤ 6 * Real.pi * (N : ℝ) / |u - t| + B := by
  rw [inner_dyadicDirRow]
  have hdiff : u - t ≠ 0 := sub_ne_zero.mpr htu.symm
  by_cases hsmall : |u - t| ≤ U
  · have hphase := norm_dyadicLogSum_le_kuzminLandau hN hdiff
      (le_trans (mul_le_mul_of_nonneg_left hsmall (by norm_num)) hnear)
    linarith
  · have hUdiff : U ≤ |u - t| := le_of_lt (lt_of_not_ge hsmall)
    have hphase := norm_dyadicLogSum_le_secondEnvelope hN hU hUdiff hdiam hlamT
    have hnonneg : 0 ≤ 6 * Real.pi * (N : ℝ) / |u - t| := by positivity
    exact hphase.trans (hB.trans (le_add_of_nonneg_left hnonneg))

/-- Huxley bound for one complete Gram row. -/
theorem sum_norm_inner_dyadicDirRow_le_huxley {N K : ℕ} (hN : 1 ≤ N)
    {lam : ℕ → ℝ} {delta U T B : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ Finset.range K, ∀ s ∈ Finset.range K, |lam s - lam r| ≤ T)
    (hU : 0 < U) (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hB : logDyadicSecondEnvelope N U T ≤ B) (hB1 : 1 ≤ B)
    {r : ℕ} (hr : r < K) :
    ∑ s ∈ Finset.range K,
        ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
      ≤ (N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
          * ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) + (K : ℝ) * B := by
  have hrmem : r ∈ Finset.range K := Finset.mem_range.2 hr
  have hoff : ∀ s ∈ (Finset.range K).erase r,
      ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
        ≤ 6 * Real.pi * (N : ℝ) * (1 / |lam s - lam r|) + B := by
    intro s hs
    have hsmem : s ∈ Finset.range K := Finset.mem_of_mem_erase hs
    have hsr : s ≠ r := (Finset.mem_erase.1 hs).1
    have htu : lam r ≠ lam s := by
      rcases lt_or_gt_of_ne hsr with hsr' | hrs'
      · exact ne_of_lt (lt_of_gap hdelta hgap hsr')
      · exact ne_of_gt (lt_of_gap hdelta hgap hrs')
    have hpoint := norm_inner_dyadicDirRow_le_huxley hN htu hU
      (hdiam r hrmem s hsmem) hnear hlamT hB hB1
    convert hpoint using 1 <;> ring
  have hoffsum : ∑ s ∈ (Finset.range K).erase r,
        ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
      ≤ (6 * Real.pi * (N : ℝ))
          * ∑ s ∈ (Finset.range K).erase r, 1 / |lam s - lam r|
        + ((Finset.range K).erase r).card * B := by
    calc
      ∑ s ∈ (Finset.range K).erase r,
          ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
          ≤ ∑ s ∈ (Finset.range K).erase r,
              (6 * Real.pi * (N : ℝ) * (1 / |lam s - lam r|) + B) :=
            Finset.sum_le_sum hoff
      _ = (6 * Real.pi * (N : ℝ))
            * ∑ s ∈ (Finset.range K).erase r, 1 / |lam s - lam r|
          + ((Finset.range K).erase r).card * B := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hinv := sum_inv_abs_dist_le hdelta hgap hr
  have hcoef0 : 0 ≤ 6 * Real.pi * (N : ℝ) := by positivity
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
  have hcard : (((Finset.range K).erase r).card : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.erase_subset r (Finset.range K))).trans_eq
      (Finset.card_range K)
  have hoffsum' : ∑ s ∈ (Finset.range K).erase r,
        ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖
      ≤ (12 * Real.pi * (N : ℝ) / delta)
          * ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) + (K : ℝ) * B := by
    refine hoffsum.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hinv hcoef0
    have h2 := mul_le_mul_of_nonneg_right hcard hB0
    calc
      (6 * Real.pi * (N : ℝ))
            * ∑ s ∈ (Finset.range K).erase r, 1 / |lam s - lam r|
          + (((Finset.range K).erase r).card : ℝ) * B
          ≤ (6 * Real.pi * (N : ℝ))
              * ((2 / delta) * ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))
            + (K : ℝ) * B := add_le_add h1 h2
      _ = (12 * Real.pi * (N : ℝ) / delta)
              * ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) + (K : ℝ) * B := by ring
  rw [← Finset.sum_erase_add _ _ hrmem]
  have hdiag : ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam r)⟫_ℂ‖ = (N : ℝ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa using norm_dyadicDirRow_sq N (lam r)
  rw [hdiag]
  linarith

/-- **Huxley's local large-values theorem for a dyadic Dirichlet polynomial.** -/
theorem huxley_local_large_values {N : ℕ} (hN : 1 ≤ N)
    (a : EuclideanSpace ℂ (Fin N)) {lam : ℕ → ℝ}
    {delta U T B V G : ℝ} (hdelta : 0 < delta) (hU : 0 < U) (hV : 0 < V)
    (hG : 0 ≤ G) (hmass : ‖a‖ ^ 2 ≤ G)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hB : logDyadicSecondEnvelope N U T ≤ B) (hB1 : 1 ≤ B)
    (R : ℕ)
    (hdiam : ∀ r ∈ Finset.range (R + 1), ∀ s ∈ Finset.range (R + 1),
      |lam s - lam r| ≤ T)
    (hbig : ∀ r ∈ Finset.range (R + 1),
      V ≤ ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖)
    (habsorb : G * B ≤ V ^ 2 / 2) :
    ((R : ℝ) + 1) * V ^ 2
      ≤ 2 * G * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
          * ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1)) := by
  let Delta : ℝ := (N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
      * ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1) + ((R : ℝ) + 1) * B
  have hrow : ∀ r ∈ Finset.range (R + 1),
      ∑ s ∈ Finset.range (R + 1),
          ‖⟪dyadicDirRow N (lam r), dyadicDirRow N (lam s)⟫_ℂ‖ ≤ Delta := by
    intro r hr
    have hr' : r < R + 1 := Finset.mem_range.1 hr
    simpa [Delta] using sum_norm_inner_dyadicDirRow_le_huxley hN hdelta hgap hdiam
      hU hnear hlamT hB hB1 hr'
  have hDelta0 : 0 ≤ Delta := by
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1) := by positivity
    have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
    dsimp [Delta]
    positivity
  have hbessel := sum_norm_inner_sq_le_of_schur (Finset.range (R + 1))
    (fun r => dyadicDirRow N (lam r)) hDelta0 hrow a
  have hupper : ∑ r ∈ Finset.range (R + 1),
        ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖ ^ 2 ≤ Delta * G :=
    hbessel.trans (mul_le_mul_of_nonneg_left hmass hDelta0)
  have hlower : ((R : ℝ) + 1) * V ^ 2
      ≤ ∑ r ∈ Finset.range (R + 1), ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖ ^ 2 := by
    have hterm : ∀ r ∈ Finset.range (R + 1),
        V ^ 2 ≤ ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖ ^ 2 := by
      intro r hr
      exact pow_le_pow_left₀ hV.le (hbig r hr) 2
    calc
      ((R : ℝ) + 1) * V ^ 2
          = ∑ r ∈ Finset.range (R + 1), V ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast
              ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have hmaster := hlower.trans hupper
  have habsorb' := mul_le_mul_of_nonneg_left habsorb (by positivity :
    (0 : ℝ) ≤ (R : ℝ) + 1)
  dsimp [Delta] at hmaster
  nlinarith

end RHTower.Sieve
