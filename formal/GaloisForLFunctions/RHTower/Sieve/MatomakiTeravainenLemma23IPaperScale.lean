import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma23I
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC1PaperScale
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC2PaperScale
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC3PaperScale

/-!
# Matomäki--Teräväinen Lemma 2.3(i) at paper scale

This file combines the three literal source errors.  It proves the weighted first moment used in
equation (2.13), then uses the unconditional pointwise ternary-divisor bound to obtain the actual
mean square asserted by Lemma 2.3(i).
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Combined weighted first moment in equation (2.13), with all three source errors literal. -/
theorem eventually_sum_ternaryWeighted_norm_mtLemma23Error_le_log_rpow
    (A : ℕ) (hA : 2 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (lower : ℕ → ℕ)
        (z₁ aLower bLower aUpper bUpper Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ z₁ → (z₁ : ℝ) ≤ X →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aLower - 1 : ℕ) : ℝ) →
      aLower ≤ bLower →
      ((bLower - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aLower - 1 : ℕ) : ℝ) →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aUpper - 1 : ℕ) : ℝ) →
      aUpper ≤ bUpper →
      ((bUpper - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aUpper - 1 : ℕ) : ℝ) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, lower q ≤ q) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → (∀ m, ‖α m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          (ternaryDivisorCount n : ℝ) *
            ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
              (primesIco aLower bLower) (primesIco aUpper bUpper)
              (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ≤
        3 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_ternaryWeighted_norm_mtC1_le_log_rpow A,
    eventually_sum_ternaryWeighted_norm_mtC2_le_log_rpow A hA,
    eventually_sum_ternaryWeighted_norm_mtC3_le_log_rpow A hA] with X hc1X hc2X hc3X
  intro α lower z₁ aLower bLower aUpper bUpper Y B hY hYX hz₁ hZ₁X
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand
    hlowerCut hlower hband hB hα
  have hc1 := hc1X α Y B hY hYX hB hα
  have hc2 := hc2X α lower aLower bLower aUpper bUpper Y B hY hYX
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand hB hα
  have hprime : ∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, q.Prime := by
    intro q hq
    exact (mem_primesIco.mp hq).2.2
  have hupper : ∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, q ≤ z₁ := by
    intro q hq
    exact (mem_primesIco.mp hq).2.1.le
  have hc3 := hc3X α (primesIco (mtLowerCutoffNat X) z₁) lower Y z₁ B
    hY hYX hz₁ hZ₁X hprime hupper hlowerCut hlower hband hB hα
  have hpoint : ∀ n ∈ Finset.Icc 1 Y,
      (ternaryDivisorCount n : ℝ) *
          ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
            (primesIco aLower bLower) (primesIco aUpper bUpper)
            (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ≤
        (ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ +
          (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) lower n‖ +
          (ternaryDivisorCount n : ℝ) *
            ‖mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖ := by
    intro n hn
    unfold mtLemma23Error
    have hnorm := (norm_add_le
      (mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n +
        mtC2Coefficient α (primesIco aLower bLower)
          (primesIco aUpper bUpper) lower n)
      (mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n)).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    calc
      (ternaryDivisorCount n : ℝ) *
          ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n +
              mtC2Coefficient α (primesIco aLower bLower)
                (primesIco aUpper bUpper) lower n +
            mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ≤
        (ternaryDivisorCount n : ℝ) *
          (‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ +
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) lower n‖ +
            ‖mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖) :=
        mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)
      _ = (ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ +
          (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) lower n‖ +
          (ternaryDivisorCount n : ℝ) *
            ‖mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖ := by ring
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) *
          ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
            (primesIco aLower bLower) (primesIco aUpper bUpper)
            (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ≤
      ∑ n ∈ Finset.Icc 1 Y,
        ((ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖ +
          (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) lower n‖ +
          (ternaryDivisorCount n : ℝ) *
            ‖mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖) :=
        Finset.sum_le_sum hpoint
    _ = (∑ n ∈ Finset.Icc 1 Y,
          (ternaryDivisorCount n : ℝ) *
            ‖mtC1Coefficient α (mtLowerCutoffNat X) (mtTruncationNat X) n‖) +
        (∑ n ∈ Finset.Icc 1 Y,
          (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) lower n‖) +
        (∑ n ∈ Finset.Icc 1 Y,
          (ternaryDivisorCount n : ℝ) *
            ‖mtC3Coefficient α (primesIco (mtLowerCutoffNat X) z₁) lower n‖) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) +
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) +
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      add_le_add (add_le_add hc1 hc2) hc3
    _ = 3 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by ring

/-- Pointwise divisor multiplicity converts the error square to its weighted first moment. -/
theorem sum_norm_sq_mtLemma23Error_le_five_mul_weighted
    (α : ℕ → ℂ) (z D : ℕ) (lowerSpill upperSpill P : Finset ℕ)
    (lower : ℕ → ℕ) (Y : ℕ) {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ∑ n ∈ Finset.Icc 1 Y,
        ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ ^ 2 ≤
      5 * B * ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) *
          ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnPos : 0 < n := by
    rw [Finset.mem_Icc] at hn
    omega
  have hpoint := norm_mtLemma23Error_le_five_mul_ternaryDivisorCount
    α z D lowerSpill upperSpill P lower hnPos hB hα
  calc
    ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ ^ 2 =
      ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ *
        ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ := by ring
    _ ≤ (5 * B * (ternaryDivisorCount n : ℝ)) *
        ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ :=
      mul_le_mul_of_nonneg_right hpoint (norm_nonneg _)
    _ = 5 * B * ((ternaryDivisorCount n : ℝ) *
        ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖) := by ring

/-- Mean-square conclusion of Matomäki--Teräväinen Lemma 2.3(i), at the literal paper scales. -/
theorem eventually_sum_norm_sq_mtLemma23Error_le_log_rpow
    (A : ℕ) (hA : 2 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (lower : ℕ → ℕ)
        (z₁ aLower bLower aUpper bUpper Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ z₁ → (z₁ : ℝ) ≤ X →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aLower - 1 : ℕ) : ℝ) →
      aLower ≤ bLower →
      ((bLower - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aLower - 1 : ℕ) : ℝ) →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aUpper - 1 : ℕ) : ℝ) →
      aUpper ≤ bUpper →
      ((bUpper - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aUpper - 1 : ℕ) : ℝ) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, lower q ≤ q) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → (∀ m, ‖α m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
            (primesIco aLower bLower) (primesIco aUpper bUpper)
            (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ^ 2 ≤
        15 * B ^ 2 * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_ternaryWeighted_norm_mtLemma23Error_le_log_rpow A hA]
    with X hweightedX
  intro α lower z₁ aLower bLower aUpper bUpper Y B hY hYX hz₁ hZ₁X
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand
    hlowerCut hlower hband hB hα
  have hweighted := hweightedX α lower z₁ aLower bLower aUpper bUpper Y B
    hY hYX hz₁ hZ₁X hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand
    hlowerCut hlower hband hB hα
  have hsq := sum_norm_sq_mtLemma23Error_le_five_mul_weighted
    α (mtLowerCutoffNat X) (mtTruncationNat X)
    (primesIco aLower bLower) (primesIco aUpper bUpper)
    (primesIco (mtLowerCutoffNat X) z₁) lower Y hB hα
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
          (primesIco aLower bLower) (primesIco aUpper bUpper)
          (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ^ 2 ≤
      5 * B * ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) *
          ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
            (primesIco aLower bLower) (primesIco aUpper bUpper)
            (primesIco (mtLowerCutoffNat X) z₁) lower n‖ := hsq
    _ ≤ 5 * B *
        (3 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hweighted (mul_nonneg (by norm_num) hB)
    _ = 15 * B ^ 2 * (Y : ℝ) *
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by ring

end

end RHTower.Sieve
