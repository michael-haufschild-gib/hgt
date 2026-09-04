import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicDyadicHeadReceiver
import GaloisForLFunctions.RHTower.Sieve.LinearMeanSquareBounded

/-!
# Reciprocal-sized dyadic head receiver for Menon's harmonic shell

The harmonic shell coefficients are bounded by `1 / (A + 1)`, not merely by one.  Retaining that
factor in the linear-to-multiplicative discretization makes its endpoint cost compatible with the
ordinary Möbius normalization after Abel transfer.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- Generic dyadic-head receiver retaining an arbitrary uniform coefficient bound. -/
theorem dyadicMeanSquare_le_dyadicHead_bound
    (f : ℕ → ℝ) {C : ℝ} (hC0 : 0 ≤ C) (hf : ∀ n, |f n| ≤ C)
    {ℓ A B M K' : ℕ} {ε W I α β : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε)
    (hW : 0 < W) (hI0 : 0 ≤ I) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hM : B + 1 + ℓ < M + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hHead : (∫ w in Set.Icc (-W) W,
      ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ I)
    (hAffine : ∀ T : ℝ, W ≤ T →
      (∫ w in Set.Icc (-T) T,
        ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ α * T + β) :
    dyadicMeanSquare f ℓ A B
      ≤ ((A : ℝ) * (1 + ε) ^ K')
          * ((K' : ℝ) * blockCostGC (ℓ : ℝ) ε C
              (2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 * I
                + (4 * α / (Real.pi ^ 2 * W)
                  + 4 * β / (3 * Real.pi ^ 2 * W ^ 2)))) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  set G : ℝ := 2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 * I
      + (4 * α / (Real.pi ^ 2 * W) + 4 * β / (3 * Real.pi ^ 2 * W ^ 2)) with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    positivity
  refine dyadicMeanSquare_le_bound f hC0 hf hℓ hA hAB hε hG0 hM hcover ?_
  intro Y' hY' E
  have hY'0 : (0 : ℝ) < Y' := lt_of_lt_of_le hA0 hY'
  have hδ0 : 0 < Real.log (1 + (ℓ : ℝ) / Y') := by
    refine Real.log_pos ?_
    have : (0 : ℝ) < (ℓ : ℝ) / Y' := by positivity
    linarith
  let a : ℕ → ℂ := fun n => ((f n : ℝ) : ℂ)
  have hwhole := gallagher_split_integral_dyadic_head a (Finset.Icc 1 M)
    hδ0 hW hHead hAffine
  have hset : (∫ u in E,
        ‖logWindowSum a (Finset.Icc 1 M) (Real.log (1 + (ℓ : ℝ) / Y')) u‖ ^ 2)
      ≤ ∫ u : ℝ,
        ‖logWindowSum a (Finset.Icc 1 M) (Real.log (1 + (ℓ : ℝ) / Y')) u‖ ^ 2 := by
    exact MeasureTheory.setIntegral_le_integral
      (integrable_normSq_logWindowSum a (Finset.Icc 1 M) _)
      (Filter.Eventually.of_forall fun _ : ℝ => by positivity)
  refine le_trans hset (le_trans hwhole ?_)
  have hmono : Real.log (1 + (ℓ : ℝ) / Y') ≤
      Real.log (1 + (ℓ : ℝ) / (A : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    have : (ℓ : ℝ) / Y' ≤ (ℓ : ℝ) / (A : ℝ) := by
      exact div_le_div_of_nonneg_left hℓ0.le hA0 hY'
    linarith
  have hsq : Real.log (1 + (ℓ : ℝ) / Y') ^ 2
      ≤ Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hδ0.le hmono 2
  rw [hGdef]
  nlinarith [hsq]

/-- Zero extension of the harmonic shell keeps the sharp reciprocal bound at its left endpoint. -/
theorem abs_localizedHarmonicMoebiusR_le_start (A n : ℕ) :
    |localizedHarmonicMoebiusR A n| ≤ 1 / ((A + 1 : ℕ) : ℝ) := by
  by_cases hn : A < n
  · rw [localizedHarmonicMoebiusR, if_pos hn]
    have hpos : 0 < n := by omega
    have hbase := abs_localizedHarmonicMoebiusR_le_inv A n hpos
    rw [localizedHarmonicMoebiusR, if_pos hn] at hbase
    have hden : ((A + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact hbase.trans (one_div_le_one_div_of_le (by positivity) hden)
  · rw [localizedHarmonicMoebiusR, if_neg hn]
    simp
    positivity

/-- Menon's harmonic shell received with its actual reciprocal coefficient size. -/
theorem dyadicMeanSquare_harmonic_le_menonFinalRange_boundedDyadicHead
    {l A B K' : ℕ} {ε W I : ℝ}
    (hl : 0 < l) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε)
    (hW : 0 < W) (hI0 : 0 ≤ I)
    (hM : B + 1 + l < menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ) + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hHead : (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell ((A + 1 : ℕ) : ℝ)) w‖ ^ 2) ≤ I) :
    dyadicMeanSquare harmonicMoebiusR l A B ≤
      ((A : ℝ) * (1 + ε) ^ K') *
        ((K' : ℝ) * blockCostGC (l : ℝ) ε (1 / ((A + 1 : ℕ) : ℝ))
          (2 * Real.log (1 + (l : ℝ) / (A : ℝ)) ^ 2 * I
            + (4 * menonHarmonicAffineRate A / (Real.pi ^ 2 * W)
              + 4 * menonHarmonicAffineConst A /
                (3 * Real.pi ^ 2 * W ^ 2)))) := by
  rw [← dyadicMeanSquare_localizedHarmonic_eq A B l hl]
  refine dyadicMeanSquare_le_dyadicHead_bound (localizedHarmonicMoebiusR A)
    (by positivity) (abs_localizedHarmonicMoebiusR_le_start A) hl hA hAB hε hW hI0
    (by dsimp [menonHarmonicAffineRate]; positivity)
    (by dsimp [menonHarmonicAffineConst]; positivity)
    hM hcover ?_ ?_
  · simpa only [logPoly_localizedHarmonic_eq_menonFinalRangeShell] using hHead
  · intro T hWT
    simpa only [logPoly_localizedHarmonic_eq_menonFinalRangeShell] using
      integral_Icc_normSq_menonFinalRangeShell_le_affine A (le_trans hW.le hWT)

end

end RHTower.Sieve
