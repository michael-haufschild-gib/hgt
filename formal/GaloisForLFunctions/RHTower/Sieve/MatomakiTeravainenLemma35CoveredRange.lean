import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDivisorRange

/-!
# Matomäki--Teräväinen Lemma 3.5 on the covered parameter ranges

The elementary over-height estimate covers `T ≤ N`.  The reciprocal divisor-energy estimate
covers the complementary branch once the relevant Watt or Deshouillers--Iwaniec product-length
comparison holds.  Combining them removes the artificial `N ≤ T` premise from the latter
statements: the order comparison is now performed inside the proof.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- The literal Deshouillers--Iwaniec envelope throughout the union of the over-height branch and
the reciprocal-divisor comparison range.  No comparison between `N` and `T` is retained. -/
theorem exists_integral_mtDI_lemma35_coveredRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      (T ≤ (N : ℝ) ∨
        ((A : ℝ) ≤ T ∧
          ((((2 * A) * (N' * N') : ℕ) : ℝ) ≤
            (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)))) →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
            ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ)) ≤
        C * T ^ ε *
          (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
            (1 / (A : ℝ)) *
            (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ (2 : ℕ))) := by
  obtain ⟨C, hC, hdiv⟩ :=
    exists_integral_mtDI_lemma35_divisorRange_of_le_height hε
  have hOver : 0 < mtLemma35OverHeightConst := by
    dsimp [mtLemma35OverHeightConst]
    positivity
  refine ⟨C + mtLemma35OverHeightConst, add_pos hC hOver, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hcovered
  rcases lt_or_ge (N : ℝ) T with hNT | hTN
  · rcases hcovered with hbad | ⟨hAT, hM⟩
    · exfalso
      linarith
    · have hbase := hdiv a A N N' hA hN hN' T hT hAT hNT.le hM
      calc
        _ ≤ C * T ^ ε *
            (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T +
                    (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                  ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
                (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
              (1 / (A : ℝ)) *
              (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ (2 : ℕ))) := hbase
        _ ≤ (C + mtLemma35OverHeightConst) * T ^ ε *
            (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T +
                    (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                  ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
                (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
              (1 / (A : ℝ)) *
              (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ (2 : ℕ))) := by
          gcongr
          linarith [hOver.le]
  · have hbase := integral_mtDI_lemma35_overHeight
      a hA hN hNN' hN' (one_le_two.trans hT) hTN hε
    calc
      _ ≤ mtLemma35OverHeightConst * T ^ ε *
          (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
            (1 / (A : ℝ)) *
            (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ (2 : ℕ))) := hbase
      _ ≤ (C + mtLemma35OverHeightConst) * T ^ ε *
          (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
            (1 / (A : ℝ)) *
            (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ (2 : ℕ))) := by
        gcongr
        linarith [hC.le]

/-- The literal Watt envelope throughout the union of the over-height branch and the
reciprocal-divisor comparison range.  No comparison between `N` and `T` is retained. -/
theorem exists_integral_mtWatt_lemma35_coveredRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      (T ≤ (N : ℝ) ∨
        ((A : ℝ) ≤ T ∧
          ((((2 * A) * (N' * N') : ℕ) : ℝ) ≤
            (A : ℝ) ^ (2 : ℕ) * Real.sqrt T))) →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
            ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ)) ≤
        C * T ^ ε *
          (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T) /
                ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
            (mtWattCoefficientMaxSq a A : ℝ)) := by
  obtain ⟨C, hC, hdiv⟩ :=
    exists_integral_mtWatt_lemma35_divisorRange_of_le_height hε
  have hOver : 0 < mtLemma35OverHeightConst := by
    dsimp [mtLemma35OverHeightConst]
    positivity
  refine ⟨C + mtLemma35OverHeightConst, add_pos hC hOver, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hcovered
  rcases lt_or_ge (N : ℝ) T with hNT | hTN
  · rcases hcovered with hbad | ⟨hAT, hM⟩
    · exfalso
      linarith
    · have hbase := hdiv a A N N' hA hN hN' T hT hAT hNT.le hM
      calc
        _ ≤ C * T ^ ε *
            (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T) /
                  ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
                (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
              (mtWattCoefficientMaxSq a A : ℝ)) := hbase
        _ ≤ (C + mtLemma35OverHeightConst) * T ^ ε *
            (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T) /
                  ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
                (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
              (mtWattCoefficientMaxSq a A : ℝ)) := by
          gcongr
          linarith [hOver.le]
  · have hbase := integral_mtWatt_lemma35_overHeight
      a hA hN hNN' hN' (one_le_two.trans hT) hTN hε
    calc
      _ ≤ mtLemma35OverHeightConst * T ^ ε *
          (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T) /
                ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
            (mtWattCoefficientMaxSq a A : ℝ)) := hbase
      _ ≤ (C + mtLemma35OverHeightConst) * T ^ ε *
          (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T) /
                ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
            (mtWattCoefficientMaxSq a A : ℝ)) := by
        gcongr
        linarith [hC.le]

end

end RHTower.Sieve
