import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRetainedBoxDecomposition

/-!
# Exact Proposition 2.2 minorant identity

This file joins source-faithful Harman rectangularization, one aggregate repaired iteration per
source, literal box expansion, and product-scale retention.  The resulting error keeps its three
distinct provenances: nonrectangular tuples, repaired-iteration errors, and box-boundary collars.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem mtRealIntervalAF_congr_on_four_mul
    (f g : ℕ → ℂ) (Y : ℕ)
    (hfg : ∀ n, 0 < n → n ≤ 4 * Y → f n = g n) :
    mtRealIntervalAF f ((Y : ℝ) / 2) (4 * (Y : ℝ)) =
      mtRealIntervalAF g ((Y : ℝ) / 2) (4 * (Y : ℝ)) := by
  ext n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [mtRealIntervalAF]
  · rw [mtRealIntervalAF_apply_of_pos _ _ _ hn,
      mtRealIntervalAF_apply_of_pos _ _ _ hn]
    by_cases hI : (Y : ℝ) / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 4 * (Y : ℝ)
    · rw [if_pos hI, if_pos hI]
      exact hfg n hn (by exact_mod_cast hI.2)
    · simp [hI]

def mtHarmanProposition22SourceAF
    (z Q D E Y : ℕ) : ArithmeticFunction ℂ :=
  mtRealIntervalAF (fun n => ((rhoMinus z Q D E n : ℤ) : ℂ))
    ((Y : ℝ) / 2) (4 * (Y : ℝ))

def mtHarmanProposition22ErrorAF {outerD recDepth : ℕ}
    (endpointD : ℕ → ℕ) (z Q D E : ℕ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (Y : ℕ)
    (boundary : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  mtRealIntervalAF
      (mtHarmanRectangularMinorantError (t := outerD) endpointD z D E)
      ((Y : ℝ) / 2) (4 * (Y : ℝ)) +
    mtRealIntervalAF
      (mtHarmanAggregateIterationErrorAF (outerDepth := outerD)
        endpointD z Q D (E : ℝ) data maxDepth j)
      ((Y : ℝ) / 2) (4 * (Y : ℝ)) + boundary

theorem mtRealIntervalAF_support_four_mul
    (f : ℕ → ℂ) {Y n : ℕ}
    (hn : mtRealIntervalAF f ((Y : ℝ) / 2) (4 * (Y : ℝ)) n ≠ 0) :
    (Y : ℝ) / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * (Y : ℝ) := by
  have hnpos : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    simp [mtRealIntervalAF] at hn
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos] at hn
  by_cases hI : (Y : ℝ) / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 4 * (Y : ℝ)
  · exact ⟨by linarith, by linarith⟩
  · simp [hI] at hn

/-- The total error inherits `(Y / 4, 8Y]` support from the product-boundary component. -/
theorem mtHarmanProposition22ErrorAF_support
    {outerD recDepth : ℕ} (endpointD : ℕ → ℕ) (z Q D E : ℕ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (Y : ℕ) (boundary : ArithmeticFunction ℂ)
    (_hY : 1 ≤ Y)
    (hboundary : ∀ {n : ℕ}, boundary n ≠ 0 →
      (Y : ℝ) / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * (Y : ℝ))
    {n : ℕ}
    (hn : mtHarmanProposition22ErrorAF (outerD := outerD)
      endpointD z Q D E data maxDepth j Y boundary n ≠ 0) :
    (Y : ℝ) / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * (Y : ℝ) := by
  by_contra hout
  have hrect : mtRealIntervalAF
      (mtHarmanRectangularMinorantError (t := outerD) endpointD z D E)
      ((Y : ℝ) / 2) (4 * (Y : ℝ)) n = 0 := by
    by_contra hne
    exact hout (mtRealIntervalAF_support_four_mul _ hne)
  have hiteration : mtRealIntervalAF
      (mtHarmanAggregateIterationErrorAF (outerDepth := outerD)
        endpointD z Q D (E : ℝ) data maxDepth j)
      ((Y : ℝ) / 2) (4 * (Y : ℝ)) n = 0 := by
    by_contra hne
    exact hout (mtRealIntervalAF_support_four_mul _ hne)
  have hboundaryZero : boundary n = 0 := by
    by_contra hne
    exact hout (hboundary hne)
  apply hn
  simp [mtHarmanProposition22ErrorAF, hrect, hiteration, hboundaryZero]

/-- Exact source interval equals retained literal boxes plus the three explicit error sources. -/
theorem mtHarmanProposition22SourceAF_eq_retained_add_error
    {outerQ outerD recDepth : ℕ}
    (endpointQ endpointD : ℕ → ℕ) (z Q D E : ℕ)
    (hendpointD : ∀ i, 1 ≤ endpointD i) (hmonoD : Monotone endpointD)
    (hmonoQ : Monotone endpointQ)
    (hsourceQ : primesIco z Q ⊆ primesIco (endpointQ 0) (endpointQ outerQ))
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) {delta : ℝ} (hdelta : 0 < delta)
    (recStart Y : ℕ) (hcutoff : data.cutoff j = z) (hz₀ : 1 < data.z₀)
    (hdepth : maxDepth =
      Nat.floor (Real.log ((4 * Y : ℕ) : ℝ) / Real.log (data.z₀ : ℝ))) :
    mtHarmanProposition22SourceAF z Q D E Y =
      mtHarmanRetainedBoxMainAF (outerQ := outerQ) (outerD := outerD)
        endpointQ endpointD z Q D (E : ℝ) data maxDepth j delta
          (4 * Y) recStart (Y : ℝ) +
      mtHarmanProposition22ErrorAF (outerD := outerD)
        endpointD z Q D E data maxDepth j Y
        (mtHarmanProductBoundaryErrorAF (outerQ := outerQ) (outerD := outerD)
          endpointQ endpointD z Q D (E : ℝ) data maxDepth j delta
            (4 * Y) recStart (Y : ℝ)) := by
  have hrect :
      mtRealIntervalAF (fun n => ((rhoMinus z Q D E n : ℤ) : ℂ))
          ((Y : ℝ) / 2) (4 * (Y : ℝ)) =
        mtRealIntervalAF (fun n =>
          mtHarmanRectangularMinorantMain (t := outerD) endpointD z Q D E n +
            mtHarmanRectangularMinorantError (t := outerD) endpointD z D E n)
          ((Y : ℝ) / 2) (4 * (Y : ℝ)) := by
    apply mtRealIntervalAF_congr_on_four_mul
    intro n hn hnY
    exact rhoMinus_eq_rectangularMinorantMain_add_error
      hendpointD hmonoD z Q D E n
  have hiteration :
      mtRealIntervalAF
          (mtHarmanRectangularMinorantMain (t := outerD) endpointD z Q D E)
          ((Y : ℝ) / 2) (4 * (Y : ℝ)) =
        mtRealIntervalAF (fun n =>
          mtHarmanAggregateIterationMainAF (outerDepth := outerD)
              endpointD z Q D (E : ℝ) data maxDepth j n +
            mtHarmanAggregateIterationErrorAF (outerDepth := outerD)
              endpointD z Q D (E : ℝ) data maxDepth j n)
          ((Y : ℝ) / 2) (4 * (Y : ℝ)) := by
    apply mtRealIntervalAF_congr_on_four_mul
    intro n hn hnY
    exact mtHarmanRectangularMinorantMain_eq_aggregateIteration
      endpointD z Q D E data maxDepth j hcutoff hn hz₀ hnY hdepth
  have hboxes :
      mtRealIntervalAF
          (mtHarmanAggregateIterationMainAF (outerDepth := outerD)
            endpointD z Q D (E : ℝ) data maxDepth j)
          ((Y : ℝ) / 2) (4 * (Y : ℝ)) =
        mtRealIntervalAF (fun n =>
          mtHarmanBaseBoxFamilyAF data maxDepth j delta (4 * Y) n -
            mtHarmanOnePrimeBoxFamilyAF (outerDepth := outerQ)
              endpointQ (primesIco z Q) data maxDepth j delta (4 * Y) n +
            mtHarmanPairBoxFamilyAF (outerDepth := outerD)
              endpointD (primesIco z D) (E : ℝ) data maxDepth j delta (4 * Y) n -
            mtHarmanTripleBoxFamilyAF (outerDepth := outerD)
              endpointD (primesIco z D) (E : ℝ) data maxDepth j delta (4 * Y) n)
          ((Y : ℝ) / 2) (4 * (Y : ℝ)) := by
    apply mtRealIntervalAF_congr_on_four_mul
    intro n hn hnY
    exact mtHarmanAggregateIterationMainAF_apply_eq_boxFamilies
      endpointQ endpointD z Q D (E : ℝ) hmonoQ hsourceQ
        data maxDepth j hdelta hn hnY
  unfold mtHarmanProposition22SourceAF
  rw [hrect, mtRealIntervalAF_add, hiteration, mtRealIntervalAF_add, hboxes,
    mtHarmanBoxFamilies_interval_eq_retained_add_boundary]
  unfold mtHarmanProposition22ErrorAF
  abel

end

end RHTower.Sieve
