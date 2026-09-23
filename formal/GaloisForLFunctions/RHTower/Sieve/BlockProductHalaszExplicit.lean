import GaloisForLFunctions.RHTower.Sieve.BlockProductHalaszReady
import GaloisForLFunctions.RHTower.Sieve.HalaszMontgomeryLogPolyBlock
import GaloisForLFunctions.RHTower.Sieve.PrimeBlockLevelSetCount

/-!
# The Möbius bilinear block, bounded explicitly by Halász--Montgomery

Four reductions compose into one inequality with no existential left in the conclusion:

* the dyadic **level split** of the prime block;
* the **level-set discretisation**, which samples each level set at two one-spaced families inside
  it (`exists_spaced_families_blockProduct_gramRows`);
* the **dyadic split** of the cofactor's initial segment, each piece bounded by
  **Halász--Montgomery** (`sum_normSq_logPoly_Icc_le_halaszMontgomery`);
* a **large-values count** for the sampled families, supplied as `C j` and discharged by
  `card_le_of_mem_primeBlockLevelSet`.

Nothing here uses a lower bound on the prime block's scale, which is the whole point: the
exact-Ramaré route's `(log x)^{-1/5}` ceiling came from a sup bound on the prime block, and this
route replaces it by rarity.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The Halász--Montgomery bound for one dyadic cofactor block, as a function of the number of
sampled frequencies. -/
def halaszBlockBound (a : ℕ → ℂ) (M : ℕ) (G U : ℝ) (i : ℕ) (C : ℝ) : ℝ :=
  (((2 ^ i : ℕ) : ℝ)
      + (12 * Real.pi * ((2 ^ i : ℕ) : ℝ) / (2 * Real.pi)) * (1 + Real.log C)
      + C * (1 + 214 * Real.sqrt (4 * Real.pi * G)
          + 1536 * (((2 ^ i : ℕ) : ℝ) / Real.sqrt U)))
    * ‖blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0‖ ^ (2 : ℕ)

/-- Monotonicity of the block bound in the frequency count. -/
theorem halaszBlockBound_mono (a : ℕ → ℂ) (M : ℕ) {G U : ℝ} (hG : 0 ≤ G) (hU : 0 < U) (i : ℕ)
    {c C : ℝ} (hc : 0 ≤ c) (hC1 : 1 ≤ C) (hcC : c ≤ C) :
    halaszBlockBound a M G U i c ≤ halaszBlockBound a M G U i C := by
  have hlog : Real.log c ≤ Real.log C := by
    rcases eq_or_lt_of_le hc with h | h
    · rw [← h, Real.log_zero]
      exact Real.log_nonneg hC1
    · exact Real.log_le_log h hcC
  have hpos : (0 : ℝ) ≤ 1 + 214 * Real.sqrt (4 * Real.pi * G)
      + 1536 * (((2 ^ i : ℕ) : ℝ) / Real.sqrt U) := by positivity
  have hcoefpos : (0 : ℝ) ≤ 12 * Real.pi * ((2 ^ i : ℕ) : ℝ) / (2 * Real.pi) := by positivity
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have h1 : (12 * Real.pi * ((2 ^ i : ℕ) : ℝ) / (2 * Real.pi)) * (1 + Real.log c)
      ≤ (12 * Real.pi * ((2 ^ i : ℕ) : ℝ) / (2 * Real.pi)) * (1 + Real.log C) :=
    mul_le_mul_of_nonneg_left (by linarith) hcoefpos
  have h2 : c * (1 + 214 * Real.sqrt (4 * Real.pi * G)
        + 1536 * (((2 ^ i : ℕ) : ℝ) / Real.sqrt U))
      ≤ C * (1 + 214 * Real.sqrt (4 * Real.pi * G)
        + 1536 * (((2 ^ i : ℕ) : ℝ) / Real.sqrt U)) :=
    mul_le_mul_of_nonneg_right hcC hpos
  linarith

/-- **The bilinear Möbius block, bounded explicitly.**  Given a count `C j` valid for every
one-spaced family inside the `j`-th level set, the mean square of the bilinear block obeys an
inequality whose right side contains no existential and no sup bound on the prime block. -/
theorem integral_normSq_blockProduct_le_halaszMontgomery
    (a : ℕ → ℂ) (M : ℕ) (B : Finset ℕ) {G U V₀ : ℝ} (hG : 0 ≤ G) (hU : 0 < U) (hV₀ : 0 < V₀)
    {J : ℕ} (hJ : ((B.card : ℕ) : ℝ) ≤ 2 ^ J * V₀)
    (hnear : ∀ i : ℕ, 3 * U ≤ 4 * Real.pi * ((2 ^ i : ℕ) : ℝ))
    (hlam : ∀ i : ℕ, logDyadicLambda (2 ^ i) (4 * Real.pi * G) ≤ 1)
    (C : ℕ → ℝ) (hC1 : ∀ j, 1 ≤ C j)
    (hC : ∀ (j : ℕ) (P : Finset ℝ), (∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 : ℝ) ≤ |x - y|) →
      (∀ x ∈ P, x ∈ primeBlockLevelSet B G (2 ^ j * V₀)) → (P.card : ℝ) ≤ C j) :
    (∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w * logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
      ≤ V₀ ^ (2 : ℕ) * (∫ w in Set.Icc (-G) G, ‖logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
        + ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ (2 : ℕ) *
            (2 * (((Nat.log 2 M + 1 : ℕ) : ℝ) *
              ∑ i ∈ Finset.range (Nat.log 2 M + 1),
                halaszBlockBound a M G U i (C j))) := by
  classical
  obtain ⟨P₁, P₂, h₁mem, h₂mem, h₁sep, h₂sep, hbound⟩ :=
    exists_spaced_families_blockProduct_levelSplit a B (Finset.Icc 1 M) hG hV₀ hJ
  refine hbound.trans ?_
  have hfam : ∀ (j : ℕ) (P : Finset ℝ),
      (∀ w ∈ P, w ∈ primeBlockLevelSet B G (2 ^ j * V₀)) →
      (∀ w ∈ P, ∀ u ∈ P, w ≠ u → (1 : ℝ) ≤ |w - u|) →
      ∑ w ∈ P, ‖logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ)
        ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) *
            ∑ i ∈ Finset.range (Nat.log 2 M + 1), halaszBlockBound a M G U i (C j) := by
    intro j P hPmem hPsep
    have hspread : ∀ x ∈ P, ∀ y ∈ P, |x - y| ≤ 2 * G := by
      intro x hx y hy
      have hx' := (hPmem x hx).1
      have hy' := (hPmem y hy).1
      rw [Set.mem_Icc] at hx' hy'
      rw [abs_le]
      constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
    have hbase := sum_normSq_logPoly_Icc_le_halaszMontgomery a hG hU hPsep hspread hnear hlam
      (M := M) (P := P)
    refine hbase.trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    exact halaszBlockBound_mono a M hG hU i (Nat.cast_nonneg _) (hC1 j)
      (hC j P hPsep hPmem)
  have hstep : ∀ j : ℕ,
      (∑ w ∈ P₁ j, ‖logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
        + ∑ w ∈ P₂ j, ‖logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ)
      ≤ 2 * (((Nat.log 2 M + 1 : ℕ) : ℝ) *
          ∑ i ∈ Finset.range (Nat.log 2 M + 1), halaszBlockBound a M G U i (C j)) := by
    intro j
    have hA := hfam j (P₁ j) (h₁mem j) (h₁sep j)
    have hB := hfam j (P₂ j) (h₂mem j) (h₂sep j)
    linarith
  have hsum : ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ (2 : ℕ) *
        ((∑ w ∈ P₁ j, ‖logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
          + ∑ w ∈ P₂ j, ‖logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
      ≤ ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ (2 : ℕ) *
        (2 * (((Nat.log 2 M + 1 : ℕ) : ℝ) *
          ∑ i ∈ Finset.range (Nat.log 2 M + 1), halaszBlockBound a M G U i (C j))) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hstep j) (sq_nonneg _)
  linarith [hsum]

end

end RHTower.Sieve
