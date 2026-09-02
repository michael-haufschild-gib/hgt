import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35MiddleA
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35NumeratorRange
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35ThirdDerivative

/-!
# Unified unconditional range for Matomäki--Teräväinen Lemma 3.5(ii)

The corpus has four independent unconditional constructions for the
Deshouillers--Iwaniec-shaped moment: the over-height estimate, the large-`A` estimate, the
complete middle-`A` estimate, the full-numerator convolution estimate, and a third-derivative
estimate.  This file combines them into one source-facing theorem.  No analytic estimate is
retained as a premise; the remaining disjunction consists only of explicit scale regions.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Union of every parameter range on which the corpus currently constructs the literal
Deshouillers--Iwaniec envelope.  Comparisons with the height are discharged internally.

The last disjunct is the exact scalar applicability region of the constructed third-derivative
bound.  Thus the complement of this theorem is a precise numerical description of the remaining
Type-I analytic frontier. -/
theorem exists_integral_mtDI_lemma35_constructedRange
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      (T ≤ (N : ℝ) ∨
        Real.sqrt T ≤ (A : ℝ) ∨
          (((2 * A) * (N' * N') : ℕ) : ℝ) ≤
            T + (A : ℝ) ^ 2 * Real.sqrt T +
              (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ∨
          (T ≤ (N : ℝ) ^ 3 ∧
            T ^ (5 / 6 : ℝ) ≤ (A : ℝ) ^ 2 ∧
            (N : ℝ) ^ (3 / 2 : ℝ) ≤ (A : ℝ) ^ 2 ∧
            (N : ℝ) ≤ (A : ℝ) * T ^ (1 / 6 : ℝ) ∧
            (N : ℝ) ^ (5 / 2 : ℝ) ≤ (A : ℝ) * T)) →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ epsilon *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (1 / (A : ℝ)) *
            (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2)) := by
  obtain ⟨C₀, hC₀, hover⟩ := exists_integral_mtDI_lemma35_coveredRange hepsilon
  obtain ⟨C₁, hC₁, hlarge⟩ := exists_integral_mtDI_lemma35_largeA hepsilon
  obtain ⟨C₂, hC₂, hmiddle⟩ := exists_integral_mtDI_lemma35_middleA hepsilon
  obtain ⟨C₃, hC₃, hnumerator⟩ := exists_integral_mtDI_lemma35_numeratorRange hepsilon
  obtain ⟨C₄, hC₄, hthird⟩ :=
    exists_integral_mtDI_lemma35_thirdDerivativeRange hepsilon
  let C := C₀ + C₁ + C₂ + C₃ + C₄
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hroute
  let R : ℝ :=
    T ^ epsilon *
      (((T + (A : ℝ) ^ 2 * Real.sqrt T +
              (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
            ((N : ℝ) ^ 2 * (A : ℝ)) +
          (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
        (1 / (A : ℝ)) *
        (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2))
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have henlarge₀ : C₀ * R ≤ C * R := by
    apply mul_le_mul_of_nonneg_right _ hR
    dsimp only [C]
    linarith [hC₁.le, hC₂.le, hC₃.le, hC₄.le]
  have henlarge₁ : C₁ * R ≤ C * R := by
    apply mul_le_mul_of_nonneg_right _ hR
    dsimp only [C]
    linarith [hC₀.le, hC₂.le, hC₃.le, hC₄.le]
  have henlarge₂ : C₂ * R ≤ C * R := by
    apply mul_le_mul_of_nonneg_right _ hR
    dsimp only [C]
    linarith [hC₀.le, hC₁.le, hC₃.le, hC₄.le]
  have henlarge₃ : C₃ * R ≤ C * R := by
    apply mul_le_mul_of_nonneg_right _ hR
    dsimp only [C]
    linarith [hC₀.le, hC₁.le, hC₂.le, hC₄.le]
  have henlarge₄ : C₄ * R ≤ C * R := by
    apply mul_le_mul_of_nonneg_right _ hR
    dsimp only [C]
    linarith [hC₀.le, hC₁.le, hC₂.le, hC₃.le]
  rcases hroute with hNT | hroute
  · have hbase := hover a A N N' hA hN hNN' hN' T hT (Or.inl hNT)
    exact hbase.trans (by
      simpa only [R, mul_assoc] using henlarge₀)
  · by_cases hNT : T ≤ (N : ℝ)
    · have hbase := hover a A N N' hA hN hNN' hN' T hT (Or.inl hNT)
      exact hbase.trans (by
        simpa only [R, mul_assoc] using henlarge₀)
    · have hNle : (N : ℝ) ≤ T := (not_le.mp hNT).le
      rcases hroute with hsqrt | hnumeratorRoute | hthirdRoute
      · by_cases hAT : (A : ℝ) ≤ T
        · have hbase := hmiddle a A N N' hA hN hNN' hN' T hT hsqrt hAT hNle
          exact hbase.trans (by
            simpa only [R, mul_assoc] using henlarge₂)
        · have hbase := hlarge a A N N' hA hN hNN' hN' T hT
            (not_le.mp hNT) (not_le.mp hAT).le
          exact hbase.trans (by
            simpa only [R, mul_assoc] using henlarge₁)
      · have hbase := hnumerator a A N N' hA hN hNN' hN' T hT hnumeratorRoute
        exact hbase.trans (by
          simpa only [R, mul_assoc] using henlarge₃)
      · by_cases hAT : (A : ℝ) ≤ T
        · have hbase := hthird a A N N' hA hN hNN' hN' T hT hAT hNle
            hthirdRoute.1 hthirdRoute.2.1 hthirdRoute.2.2.1 hthirdRoute.2.2.2.1
            hthirdRoute.2.2.2.2
          exact hbase.trans (by
            simpa only [R, mul_assoc] using henlarge₄)
        · have hbase := hlarge a A N N' hA hN hNN' hN' T hT
            (not_le.mp hNT) (not_le.mp hAT).le
          exact hbase.trans (by
            simpa only [R, mul_assoc] using henlarge₁)

end

end RHTower.Sieve
