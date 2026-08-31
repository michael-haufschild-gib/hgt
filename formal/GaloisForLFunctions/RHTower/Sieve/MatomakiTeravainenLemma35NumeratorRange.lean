import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35ProductRange
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35MiddleA

/-!
# Full-numerator elementary range of Matomäki--Teräväinen Lemma 3.5

The ordinary three-factor affine mean square is governed by the complete product length
`2 A N'²`.  Earlier comparison modules charged that length to only one term of the Watt or
Deshouillers--Iwaniec numerator.  Here it is charged to the entire literal numerator.  This closes
the strictly larger union where no individual summand dominates, with all height routing internal.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- The Deshouillers--Iwaniec envelope whenever the complete product length is at most its full
three-term numerator, under the height bounds used to absorb the fixed divisor power. -/
theorem exists_integral_mtDI_lemma35_numeratorRange_height
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (A : ℝ) ≤ T → (N : ℝ) ≤ T →
      (((2 * A) * (N' * N') : ℕ) : ℝ) ≤
        T + (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) →
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
  obtain ⟨C₀, hC₀, hbase⟩ := exists_integral_mtWatt_divisorEnergy_height hε
  refine ⟨2 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hAT hNT hM
  let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
  let D : ℝ :=
    T + (A : ℝ) ^ 2 * Real.sqrt T +
      (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)
  let Q : ℝ :=
    D / ((N : ℝ) ^ 2 * (A : ℝ)) +
      (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))
  let R : ℝ := Q * (1 / (A : ℝ)) * E
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hTD : T ≤ D := by
    dsimp only [D]
    have hrest : 0 ≤
        (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
    linarith
  have hsum : T + (((2 * A) * (N' * N') : ℕ) : ℝ) ≤ 2 * D := by
    have hMR : (((2 * A) * (N' * N') : ℕ) : ℝ) ≤ D := by simpa only [D] using hM
    linarith
  have hscalar :
      (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 ≤
        2 * (D / ((N : ℝ) ^ 2 * (A : ℝ))) * (1 / (A : ℝ)) := by
    calc
      _ = (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) /
          ((A : ℝ) ^ 2 * (N : ℝ) ^ 2) := by
        field_simp [hApos.ne', hNpos.ne']
      _ ≤ (2 * D) / ((A : ℝ) ^ 2 * (N : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hsum (by positivity)
      _ = 2 * (D / ((N : ℝ) ^ 2 * (A : ℝ))) * (1 / (A : ℝ)) := by
        field_simp [hApos.ne', hNpos.ne']
  have hres : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
  have hscalarR :
      (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 * E ≤ 2 * R := by
    have hmain :
        2 * (D / ((N : ℝ) ^ 2 * (A : ℝ))) * (1 / (A : ℝ)) ≤
          2 * Q * (1 / (A : ℝ)) := by
      have hDQ : D / ((N : ℝ) ^ 2 * (A : ℝ)) ≤ Q := by
        dsimp only [Q]
        exact le_add_of_nonneg_right hres
      gcongr
    have hs := mul_le_mul_of_nonneg_right (hscalar.trans hmain) hE0
    simpa only [R, mul_assoc] using hs
  have hraw := hbase a A N N' hA hN hN' T hT hAT hNT
  have hCT0 : 0 ≤ C₀ * T ^ ε :=
    mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith) ε)
  have hscale :
      (C₀ * T ^ ε) *
          ((T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
            (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 * E) ≤
        (C₀ * T ^ ε) * (2 * R) :=
    mul_le_mul_of_nonneg_left hscalarR hCT0
  calc
    _ ≤ C₀ * T ^ ε *
        (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
        (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 := by
      simpa only [E, mul_assoc] using hraw
    _ ≤ C₀ * T ^ ε * (2 * R) := by
      have hreorder :
          C₀ * T ^ ε *
              (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
              (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 =
            (C₀ * T ^ ε) *
              ((T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
                (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 * E) := by ac_rfl
      rw [hreorder]
      exact hscale
    _ = 2 * C₀ * T ^ ε * R := by ac_rfl
    _ = _ := by
      rfl

/-- Watt's coefficient-maximum envelope under the corresponding full two-term numerator
comparison and the height bounds used to absorb the divisor power. -/
theorem exists_integral_mtWatt_lemma35_numeratorRange_height
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (A : ℝ) ≤ T → (N : ℝ) ≤ T →
      (((2 * A) * (N' * N') : ℕ) : ℝ) ≤
        T + (A : ℝ) ^ 2 * Real.sqrt T →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (mtWattCoefficientMaxSq a A : ℝ)) := by
  obtain ⟨C₀, hC₀, hbase⟩ := exists_integral_mtWatt_divisorEnergy_height hε
  refine ⟨2 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hAT hNT hM
  let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
  let Mx : ℝ := mtWattCoefficientMaxSq a A
  let D : ℝ := T + (A : ℝ) ^ 2 * Real.sqrt T
  let Q : ℝ :=
    D / ((N : ℝ) ^ 2 * (A : ℝ)) +
      (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))
  let R : ℝ := Q * Mx
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hMx0 : 0 ≤ Mx := by dsimp only [Mx]; positivity
  have hTD : T ≤ D := by
    dsimp only [D]
    have hrest : 0 ≤ (A : ℝ) ^ 2 * Real.sqrt T := by positivity
    linarith
  have hsum : T + (((2 * A) * (N' * N') : ℕ) : ℝ) ≤ 2 * D := by
    have hMR : (((2 * A) * (N' * N') : ℕ) : ℝ) ≤ D := by simpa only [D] using hM
    linarith
  have henergy : E ≤ (A : ℝ) * Mx := by
    simpa only [E, Mx] using sum_normSq_mtWattCoefficientBlock_le_max a hA
  have hrawScalar :
      (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 * E ≤
        2 * (D / ((N : ℝ) ^ 2 * (A : ℝ))) * Mx := by
    have hfac0 : 0 ≤
        (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 := by positivity
    calc
      _ ≤ (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 * ((A : ℝ) * Mx) :=
        mul_le_mul_of_nonneg_left henergy hfac0
      _ = ((T + (((2 * A) * (N' * N') : ℕ) : ℝ)) /
          ((N : ℝ) ^ 2 * (A : ℝ))) * Mx := by
        field_simp [hApos.ne', hNpos.ne']
      _ ≤ ((2 * D) / ((N : ℝ) ^ 2 * (A : ℝ))) * Mx :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hsum (by positivity)) hMx0
      _ = 2 * (D / ((N : ℝ) ^ 2 * (A : ℝ))) * Mx := by ring
  have hres : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
  have hscalarR :
      (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 * E ≤ 2 * R := by
    have hmain :
        2 * (D / ((N : ℝ) ^ 2 * (A : ℝ))) * Mx ≤ 2 * Q * Mx := by
      have hDQ : D / ((N : ℝ) ^ 2 * (A : ℝ)) ≤ Q := by
        dsimp only [Q]
        exact le_add_of_nonneg_right hres
      gcongr
    exact hrawScalar.trans (by simpa only [R, mul_assoc] using hmain)
  have hraw := hbase a A N N' hA hN hN' T hT hAT hNT
  have hCT0 : 0 ≤ C₀ * T ^ ε :=
    mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith) ε)
  have hscale :
      (C₀ * T ^ ε) *
          ((T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
            (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 * E) ≤
        (C₀ * T ^ ε) * (2 * R) :=
    mul_le_mul_of_nonneg_left hscalarR hCT0
  calc
    _ ≤ C₀ * T ^ ε *
        (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
        (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 := by
      simpa only [E, mul_assoc] using hraw
    _ ≤ C₀ * T ^ ε * (2 * R) := by
      have hreorder :
          C₀ * T ^ ε *
              (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
              (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 =
            (C₀ * T ^ ε) *
              ((T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
                (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 * E) := by ac_rfl
      rw [hreorder]
      exact hscale
    _ = 2 * C₀ * T ^ ε * R := by ac_rfl
    _ = _ := by
      rfl

/-- Deshouillers--Iwaniec's literal Lemma 3.5 envelope on the full-numerator comparison range.
The theorem itself performs every comparison with `A`, `N`, and `T`. -/
theorem exists_integral_mtDI_lemma35_numeratorRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      (((2 * A) * (N' * N') : ℕ) : ℝ) ≤
        T + (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) →
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
  obtain ⟨C₂, hC₂, hnum⟩ := exists_integral_mtDI_lemma35_numeratorRange_height hε
  refine ⟨C₀ + C₁ + C₂, add_pos (add_pos hC₀ hC₁) hC₂, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hM
  let R : ℝ :=
    (((T + (A : ℝ) ^ 2 * Real.sqrt T +
            (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
          ((N : ℝ) ^ 2 * (A : ℝ)) +
        (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
      (1 / (A : ℝ)) *
      (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2))
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hfac0 : 0 ≤ T ^ ε * R := by positivity
  have henlarge₀ : C₀ * T ^ ε * R ≤ (C₀ + C₁ + C₂) * T ^ ε * R := by
    have : C₀ ≤ C₀ + C₁ + C₂ := by linarith [hC₁.le, hC₂.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right this hfac0
  have henlarge₁ : C₁ * T ^ ε * R ≤ (C₀ + C₁ + C₂) * T ^ ε * R := by
    have : C₁ ≤ C₀ + C₁ + C₂ := by linarith [hC₀.le, hC₂.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right this hfac0
  have henlarge₂ : C₂ * T ^ ε * R ≤ (C₀ + C₁ + C₂) * T ^ ε * R := by
    have : C₂ ≤ C₀ + C₁ + C₂ := by linarith [hC₀.le, hC₁.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right this hfac0
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
      have hb := hnum a A N N' hA hN hNN' hN' T hT hAT hNT.le hM
      have hbR :
          (∫ t in (T / 2)..T,
              ‖mtWattUnitBlock N N' t‖ ^ 4 *
                ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ C₂ * T ^ ε * R := by
        simpa only [R, mul_assoc] using hb
      exact hbR.trans henlarge₂
  · have hb := hcovered a A N N' hA hN hNN' hN' T hT
      (Or.inl (not_lt.mp hNT))
    have hbR :
        (∫ t in (T / 2)..T,
            ‖mtWattUnitBlock N N' t‖ ^ 4 *
              ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ C₀ * T ^ ε * R := by
      simpa only [R, mul_assoc] using hb
    exact hbR.trans henlarge₀

/-- Watt's literal coefficient-maximum envelope on its full-numerator comparison range, with all
height routing internal. -/
theorem exists_integral_mtWatt_lemma35_numeratorRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      (((2 * A) * (N' * N') : ℕ) : ℝ) ≤
        T + (A : ℝ) ^ 2 * Real.sqrt T →
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
  obtain ⟨C₂, hC₂, hnum⟩ := exists_integral_mtWatt_lemma35_numeratorRange_height hε
  refine ⟨C₀ + C₁ + C₂, add_pos (add_pos hC₀ hC₁) hC₂, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hM
  let R : ℝ :=
    (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
          ((N : ℝ) ^ 2 * (A : ℝ)) +
        (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
      (mtWattCoefficientMaxSq a A : ℝ))
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hfac0 : 0 ≤ T ^ ε * R := by positivity
  have henlarge₀ : C₀ * T ^ ε * R ≤ (C₀ + C₁ + C₂) * T ^ ε * R := by
    have : C₀ ≤ C₀ + C₁ + C₂ := by linarith [hC₁.le, hC₂.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right this hfac0
  have henlarge₁ : C₁ * T ^ ε * R ≤ (C₀ + C₁ + C₂) * T ^ ε * R := by
    have : C₁ ≤ C₀ + C₁ + C₂ := by linarith [hC₀.le, hC₂.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right this hfac0
  have henlarge₂ : C₂ * T ^ ε * R ≤ (C₀ + C₁ + C₂) * T ^ ε * R := by
    have : C₂ ≤ C₀ + C₁ + C₂ := by linarith [hC₀.le, hC₁.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right this hfac0
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
      have hb := hnum a A N N' hA hN hNN' hN' T hT hAT hNT.le hM
      have hbR :
          (∫ t in (T / 2)..T,
              ‖mtWattUnitBlock N N' t‖ ^ 4 *
                ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ C₂ * T ^ ε * R := by
        simpa only [R, mul_assoc] using hb
      exact hbR.trans henlarge₂
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
