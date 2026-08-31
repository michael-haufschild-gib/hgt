import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35CoveredRange
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35LargeA

/-!
# Product-range reduction for Matomäki--Teräväinen Lemma 3.5

Combining over-height, reciprocal-divisor, and constructed large-`A` branches removes the
previously exposed `A ≤ T` condition.  Only the literal Watt or Deshouillers--Iwaniec
product-length comparison remains; all height and coefficient-length routing occurs inside proofs.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

theorem exists_integral_mtDI_lemma35_productRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      ((((2 * A) * (N' * N') : ℕ) : ℝ) ≤
        (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (1 / (A : ℝ)) *
            (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2)) := by
  obtain ⟨C₀, hC₀, hcovered⟩ := exists_integral_mtDI_lemma35_coveredRange hε
  obtain ⟨C₁, hC₁, hlarge⟩ := exists_integral_mtDI_lemma35_largeA hε
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hM
  let R : ℝ :=
    (((T + (A : ℝ) ^ 2 * Real.sqrt T +
            (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
          ((N : ℝ) ^ 2 * (A : ℝ)) +
        (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
      (1 / (A : ℝ)) *
      (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2))
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hTpow0 : 0 ≤ T ^ ε := Real.rpow_nonneg (by linarith) _
  have henlarge₀ : C₀ * T ^ ε * R ≤ (C₀ + C₁) * T ^ ε * R := by
    have hfac : 0 ≤ T ^ ε * R := mul_nonneg hTpow0 hR0
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (show C₀ ≤ C₀ + C₁ by linarith [hC₁.le]) hfac
  have henlarge₁ : C₁ * T ^ ε * R ≤ (C₀ + C₁) * T ^ ε * R := by
    have hfac : 0 ≤ T ^ ε * R := mul_nonneg hTpow0 hR0
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (show C₁ ≤ C₀ + C₁ by linarith [hC₀.le]) hfac
  by_cases hNT : (N : ℝ) < T
  · by_cases hTA : T ≤ (A : ℝ)
    · have hb := hlarge a A N N' hA hN hNN' hN' T hT hNT hTA
      have hbR :
          (∫ t in (T / 2)..T,
              ‖mtWattUnitBlock N N' t‖ ^ 4 *
                ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ C₁ * T ^ ε * R := by
        simpa only [R, mul_assoc] using hb
      exact hbR.trans henlarge₁
    · have hAT : (A : ℝ) ≤ T := (not_le.mp hTA).le
      have hb := hcovered a A N N' hA hN hNN' hN' T hT
        (Or.inr ⟨hAT, hM⟩)
      have hbR :
          (∫ t in (T / 2)..T,
              ‖mtWattUnitBlock N N' t‖ ^ 4 *
                ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ C₀ * T ^ ε * R := by
        simpa only [R, mul_assoc] using hb
      exact hbR.trans henlarge₀
  · have hb := hcovered a A N N' hA hN hNN' hN' T hT
      (Or.inl (not_lt.mp hNT))
    have hbR :
        (∫ t in (T / 2)..T,
            ‖mtWattUnitBlock N N' t‖ ^ 4 *
              ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ C₀ * T ^ ε * R := by
      simpa only [R, mul_assoc] using hb
    exact hbR.trans henlarge₀

theorem exists_integral_mtWatt_lemma35_productRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      ((((2 * A) * (N' * N') : ℕ) : ℝ) ≤
        (A : ℝ) ^ 2 * Real.sqrt T) →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (mtWattCoefficientMaxSq a A : ℝ)) := by
  obtain ⟨C₀, hC₀, hcovered⟩ := exists_integral_mtWatt_lemma35_coveredRange hε
  obtain ⟨C₁, hC₁, hlarge⟩ := exists_integral_mtWatt_lemma35_largeA hε
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hM
  let R : ℝ :=
    (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
          ((N : ℝ) ^ 2 * (A : ℝ)) +
        (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
      (mtWattCoefficientMaxSq a A : ℝ))
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hTpow0 : 0 ≤ T ^ ε := Real.rpow_nonneg (by linarith) _
  have henlarge₀ : C₀ * T ^ ε * R ≤ (C₀ + C₁) * T ^ ε * R := by
    have hfac : 0 ≤ T ^ ε * R := mul_nonneg hTpow0 hR0
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (show C₀ ≤ C₀ + C₁ by linarith [hC₁.le]) hfac
  have henlarge₁ : C₁ * T ^ ε * R ≤ (C₀ + C₁) * T ^ ε * R := by
    have hfac : 0 ≤ T ^ ε * R := mul_nonneg hTpow0 hR0
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (show C₁ ≤ C₀ + C₁ by linarith [hC₀.le]) hfac
  by_cases hNT : (N : ℝ) < T
  · by_cases hTA : T ≤ (A : ℝ)
    · have hb := hlarge a A N N' hA hN hNN' hN' T hT hNT hTA
      have hbR :
          (∫ t in (T / 2)..T,
              ‖mtWattUnitBlock N N' t‖ ^ 4 *
                ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ C₁ * T ^ ε * R := by
        simpa only [R, mul_assoc] using hb
      exact hbR.trans henlarge₁
    · have hAT : (A : ℝ) ≤ T := (not_le.mp hTA).le
      have hb := hcovered a A N N' hA hN hNN' hN' T hT
        (Or.inr ⟨hAT, hM⟩)
      have hbR :
          (∫ t in (T / 2)..T,
              ‖mtWattUnitBlock N N' t‖ ^ 4 *
                ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ C₀ * T ^ ε * R := by
        simpa only [R, mul_assoc] using hb
      exact hbR.trans henlarge₀
  · have hb := hcovered a A N N' hA hN hNN' hN' T hT
      (Or.inl (not_lt.mp hNT))
    have hbR :
        (∫ t in (T / 2)..T,
            ‖mtWattUnitBlock N N' t‖ ^ 4 *
              ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ C₀ * T ^ ε * R := by
      simpa only [R, mul_assoc] using hb
    exact hbR.trans henlarge₀

end

end RHTower.Sieve

