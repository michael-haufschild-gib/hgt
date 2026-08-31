import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35OneUnit
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDivisorRange

/-!
# Middle coefficient-length branch of Matomäki--Teräväinen Lemma 3.5

The band `sqrt T ≤ A ≤ T` is unconditional.  If `T sqrt T ≤ A² N`, the one-unit-factor
hybrid pays the whole integral.  Otherwise `N < sqrt T`, hence `N² ≤ A sqrt T`, and the ordinary
three-factor convolution energy pays it.  This dichotomy has no supplied comparison witness.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- The three-factor divisor-energy estimate with its divisor power absorbed on `A,N ≤ T`. -/
theorem exists_integral_mtWatt_divisorEnergy_height
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (A : ℝ) ≤ T → (N : ℝ) ≤ T →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ ε *
          (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ)) ^ 2 := by
  have hδ : 0 < ε / 5 := by positivity
  obtain ⟨C, hC, hbase⟩ := exists_integral_mtWatt_divisorEnergy hδ
  refine ⟨C, hC, ?_⟩
  intro a A N N' hA hN hN' T hT hAT hNT
  have hp := mtWatt_divisorPower_le_of_two_le hε hT hAT hNT hN'
  have hp' :
      (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ ((ε / 5) / 2)) *
        (((N' * N' : ℕ) : ℝ) ^ ((ε / 5) / 2))) ≤ T ^ ε := by
    simpa only [show (ε / 5) / 2 = ε / 10 by ring] using hp
  have hraw := hbase a A N N' hA hN hN' T (one_le_two.trans hT)
  let R : ℝ :=
    (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
      (1 / (A : ℝ) ^ 2) *
      (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
      (1 / (N : ℝ)) ^ 2
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hscaled := mul_le_mul_of_nonneg_left hp' (mul_nonneg hC.le hR0)
  calc
    _ ≤ C *
        (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ ((ε / 5) / 2)) *
          (((N' * N' : ℕ) : ℝ) ^ ((ε / 5) / 2))) * R := by
      simpa only [R, hδ, mul_assoc] using hraw
    _ ≤ C * T ^ ε * R := by
      calc
        C *
            (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ ((ε / 5) / 2)) *
              (((N' * N' : ℕ) : ℝ) ^ ((ε / 5) / 2))) * R =
            (C * R) *
              (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ ((ε / 5) / 2)) *
                (((N' * N' : ℕ) : ℝ) ^ ((ε / 5) / 2))) := by ring
        _ ≤ (C * R) * T ^ ε := hscaled
        _ = C * T ^ ε * R := by ring
    _ = _ := by
      dsimp only [R]
      ring

private theorem mtLemma35_oneUnit_scalar_le
    {A N N' : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N) (hN' : N' ≤ 2 * N)
    {T : ℝ} (hT : 2 ≤ T) (hsA : Real.sqrt T ≤ (A : ℝ))
    (hNT : (N : ℝ) ≤ T)
    (hlarge : T * Real.sqrt T ≤ (A : ℝ) ^ 2 * (N : ℝ)) :
    (T + (((2 * A) * N' : ℕ) : ℝ)) *
        (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) *
        (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2 ≤
      20 * (Real.sqrt T / (N : ℝ) ^ 2) := by
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hspos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsquare : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTpos.le
  have hN'R : (N' : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN'
  have hM : (((2 * A) * N' : ℕ) : ℝ) ≤ 4 * (A : ℝ) * (N : ℝ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hN'R (Nat.cast_nonneg A)]
  have hfirstT : T / ((A : ℝ) ^ 2 * (N : ℝ)) ≤ 1 / Real.sqrt T := by
    rw [div_le_div_iff₀ (mul_pos (sq_pos_of_pos hApos) hNpos) hspos]
    simpa only [one_mul] using hlarge
  have hfirstA : 4 / (A : ℝ) ≤ 4 / Real.sqrt T := by
    exact div_le_div_of_nonneg_left (by norm_num) hspos hsA
  have hfactor :
      (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ≤
        5 / Real.sqrt T := by
    calc
      (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) =
          (T + (((2 * A) * N' : ℕ) : ℝ)) /
            ((A : ℝ) ^ 2 * (N : ℝ)) := by field_simp
      _ ≤ (T + 4 * (A : ℝ) * (N : ℝ)) /
            ((A : ℝ) ^ 2 * (N : ℝ)) :=
        div_le_div_of_nonneg_right (by simpa [add_comm] using add_le_add_left hM T)
          (mul_nonneg (sq_nonneg _) hNpos.le)
      _ = T / ((A : ℝ) ^ 2 * (N : ℝ)) + 4 / (A : ℝ) := by
        field_simp
      _ ≤ 1 / Real.sqrt T + 4 / Real.sqrt T := add_le_add hfirstT hfirstA
      _ = 5 / Real.sqrt T := by ring
  have hinv : 1 / Real.sqrt T ≤ Real.sqrt T / (N : ℝ) := by
    rw [div_le_div_iff₀ hspos hNpos]
    nlinarith [hsquare, hNT]
  have hunit :
      (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2 ≤
        4 * T / (N : ℝ) ^ 2 := by
    have hsum : Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T ≤
        2 * (Real.sqrt T / (N : ℝ)) := by linarith
    have hsum0 : 0 ≤ Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T := by positivity
    have hs := pow_le_pow_left₀ hsum0 hsum 2
    calc
      _ ≤ (2 * (Real.sqrt T / (N : ℝ))) ^ 2 := hs
      _ = 4 * Real.sqrt T ^ 2 / (N : ℝ) ^ 2 := by ring
      _ = 4 * T / (N : ℝ) ^ 2 := by rw [hsquare]
  have hmul := mul_le_mul hfactor hunit (sq_nonneg _) (by positivity : 0 ≤ 5 / Real.sqrt T)
  calc
    _ ≤ (5 / Real.sqrt T) * (4 * T / (N : ℝ) ^ 2) := by
      simpa only [mul_assoc] using hmul
    _ = 20 * (Real.sqrt T / (N : ℝ) ^ 2) := by
      field_simp
      nlinarith [hsquare]

private theorem mtLemma35_divisor_scalar_le
    {A N N' : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N) (hN' : N' ≤ 2 * N)
    {T : ℝ} (hT : 2 ≤ T)
    (hshort : (N : ℝ) ^ 2 ≤ (A : ℝ) * Real.sqrt T) :
    (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
        (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 ≤
      8 * ((T + (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
        ((N : ℝ) ^ 2 * (A : ℝ)) +
        (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
        (1 / (A : ℝ)) := by
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN'R : (N' : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN'
  have hNN' : ((N' * N' : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
    push_cast
    nlinarith [mul_self_le_mul_self (Nat.cast_nonneg N') hN'R]
  have hM : (((2 * A) * (N' * N') : ℕ) : ℝ) ≤
      8 * (A : ℝ) ^ 2 * Real.sqrt T := by
    push_cast at hNN' ⊢
    have hleft := mul_le_mul_of_nonneg_left hNN'
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hApos.le)
    have hright := mul_le_mul_of_nonneg_left hshort
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hApos.le)
    nlinarith
  have hnum : T + (((2 * A) * (N' * N') : ℕ) : ℝ) ≤
      8 * (T + (A : ℝ) ^ 2 * Real.sqrt T +
        (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
    have hrpow : 0 ≤ (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
    nlinarith
  have hfrac :
      (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) /
          ((N : ℝ) ^ 2 * (A : ℝ)) ≤
        8 * ((T + (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
            ((N : ℝ) ^ 2 * (A : ℝ))) := by
    rw [show 8 * ((T + (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
            ((N : ℝ) ^ 2 * (A : ℝ))) =
        (8 * (T + (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ))) /
            ((N : ℝ) ^ 2 * (A : ℝ)) by ring]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hres : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
  calc
    (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
        (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ^ 2 =
      ((T + (((2 * A) * (N' * N') : ℕ) : ℝ)) /
        ((N : ℝ) ^ 2 * (A : ℝ))) * (1 / (A : ℝ)) := by field_simp
    _ ≤ (8 * ((T + (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
            ((N : ℝ) ^ 2 * (A : ℝ)))) * (1 / (A : ℝ)) :=
      mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ ≤ 8 * ((T + (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
        ((N : ℝ) ^ 2 * (A : ℝ)) +
        (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
        (1 / (A : ℝ)) := by
      gcongr
      exact le_add_of_nonneg_right hres

/-- The complete DI envelope throughout `sqrt T ≤ A ≤ T`, with all routing internal. -/
theorem exists_integral_mtDI_lemma35_middleA
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → Real.sqrt T ≤ (A : ℝ) →
      (A : ℝ) ≤ T → (N : ℝ) ≤ T →
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
  obtain ⟨C₀, hC₀, hdiv⟩ := exists_integral_mtWatt_divisorEnergy_height hε
  obtain ⟨C₁, hC₁, hone⟩ :=
    exists_integral_mtWatt_oneUnit_secondDerivative_height hε
  refine ⟨8 * C₀ + 20 * C₁, add_pos (mul_pos (by norm_num) hC₀)
    (mul_pos (by norm_num) hC₁), ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hsA hAT hNT
  let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
  let Q : ℝ :=
    (T + (A : ℝ) ^ 2 * Real.sqrt T +
        (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
      ((N : ℝ) ^ 2 * (A : ℝ)) +
    (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))
  let R : ℝ := Q * (1 / (A : ℝ)) * E
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  have hR0 : 0 ≤ R := mul_nonneg (mul_nonneg hQ0 (by positivity)) hE0
  have hTpow0 : 0 ≤ T ^ ε := Real.rpow_nonneg (by positivity) _
  have hCtotal0 : 0 ≤ 8 * C₀ + 20 * C₁ := by positivity
  by_cases hlarge : T * Real.sqrt T ≤ (A : ℝ) ^ 2 * (N : ℝ)
  · have hraw := hone a A N N' hA hN hNN' hN' T hT hAT hNT
    have hscalar := mtLemma35_oneUnit_scalar_le hA hN hN' hT hsA hNT hlarge
    have hscaled := mul_le_mul_of_nonneg_left hscalar
      (mul_nonneg (mul_nonneg hC₁.le hTpow0) hE0)
    have hbranch :
        (∫ t in (T / 2)..T,
            ‖mtWattUnitBlock N N' t‖ ^ 4 *
              ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
          20 * C₁ * T ^ ε * (Real.sqrt T / (N : ℝ) ^ 2) * E := by
      calc
        _ ≤ C₁ * T ^ ε *
            (T + (((2 * A) * N' : ℕ) : ℝ)) *
            (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) *
            (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2 := by
          simpa only [E, mul_assoc] using hraw
        _ ≤ 20 * C₁ * T ^ ε * (Real.sqrt T / (N : ℝ) ^ 2) * E := by
          nlinarith [hscaled]
    have hsR : (Real.sqrt T / (N : ℝ) ^ 2) * E ≤ R := by
      have hApos : (0 : ℝ) < A := by exact_mod_cast hA
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hmain : Real.sqrt T / (N : ℝ) ^ 2 ≤ Q * (1 / (A : ℝ)) := by
        dsimp only [Q]
        have hres : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
        have hother : 0 ≤ T + (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
        calc
          Real.sqrt T / (N : ℝ) ^ 2 =
              ((A : ℝ) ^ 2 * Real.sqrt T /
                ((N : ℝ) ^ 2 * (A : ℝ))) * (1 / (A : ℝ)) := by field_simp
          _ ≤ ((T + (A : ℝ) ^ 2 * Real.sqrt T +
                (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ 2 * (A : ℝ))) * (1 / (A : ℝ)) := by
            gcongr
            nlinarith
          _ ≤ (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ 2 * (A : ℝ))) +
                (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) * (1 / (A : ℝ)) := by
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hres) (by positivity)
      exact mul_le_mul_of_nonneg_right hmain hE0
    have henlarge :
        20 * C₁ * T ^ ε * (Real.sqrt T / (N : ℝ) ^ 2) * E ≤
          (8 * C₀ + 20 * C₁) * T ^ ε * R := by
      have hcoef : 20 * C₁ ≤ 8 * C₀ + 20 * C₁ := by nlinarith [hC₀.le]
      have hfac0 : 0 ≤ T ^ ε * ((Real.sqrt T / (N : ℝ) ^ 2) * E) := by positivity
      calc
        20 * C₁ * T ^ ε * (Real.sqrt T / (N : ℝ) ^ 2) * E =
            (20 * C₁) * (T ^ ε * ((Real.sqrt T / (N : ℝ) ^ 2) * E)) := by ring
        _ ≤ (8 * C₀ + 20 * C₁) *
            (T ^ ε * ((Real.sqrt T / (N : ℝ) ^ 2) * E)) :=
          mul_le_mul_of_nonneg_right hcoef hfac0
        _ ≤ (8 * C₀ + 20 * C₁) * (T ^ ε * R) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsR hTpow0) hCtotal0
        _ = _ := by ring
    exact hbranch.trans (by simpa only [R, Q, E, mul_assoc] using henlarge)
  · have hfail : (A : ℝ) ^ 2 * (N : ℝ) < T * Real.sqrt T := lt_of_not_ge hlarge
    have hTpos : 0 < T := zero_lt_two.trans_le hT
    have hsquare : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTpos.le
    have hA2 : T ≤ (A : ℝ) ^ 2 := by
      have hs := mul_self_le_mul_self (Real.sqrt_nonneg T) hsA
      nlinarith [hsquare]
    have hNlt : (N : ℝ) < Real.sqrt T := by
      have hmul := mul_le_mul_of_nonneg_right hA2 (Nat.cast_nonneg N)
      nlinarith
    have hshort : (N : ℝ) ^ 2 ≤ (A : ℝ) * Real.sqrt T := by
      have hN2 := mul_self_le_mul_self (Nat.cast_nonneg N) hNlt.le
      have hsA' := mul_le_mul_of_nonneg_right hsA (Real.sqrt_nonneg T)
      nlinarith
    have hraw := hdiv a A N N' hA hN hN' T hT hAT hNT
    have hscalar := mtLemma35_divisor_scalar_le hA hN hN' hT hshort
    have hscaled := mul_le_mul_of_nonneg_left hscalar
      (mul_nonneg (mul_nonneg hC₀.le hTpow0) hE0)
    have hbranch :
        (∫ t in (T / 2)..T,
            ‖mtWattUnitBlock N N' t‖ ^ 4 *
              ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
          8 * C₀ * T ^ ε * R := by
      calc
        _ ≤ C₀ * T ^ ε *
            (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
            (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 := by
          simpa only [E, mul_assoc] using hraw
        _ ≤ 8 * C₀ * T ^ ε * R := by
          dsimp only [R, Q]
          nlinarith [hscaled]
    have hcoef : 8 * C₀ ≤ 8 * C₀ + 20 * C₁ := by nlinarith [hC₁.le]
    have hfac0 : 0 ≤ T ^ ε * R := mul_nonneg hTpow0 hR0
    have henlarge := mul_le_mul_of_nonneg_right hcoef hfac0
    exact hbranch.trans (by
      simpa only [R, Q, E, mul_assoc] using henlarge)

end

end RHTower.Sieve
