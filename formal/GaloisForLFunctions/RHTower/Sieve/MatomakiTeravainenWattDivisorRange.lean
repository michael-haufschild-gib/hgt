import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDivisorEnergy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35OverHeight

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

theorem exists_integral_mtDI_lemma35_divisorRange
    {δ ε : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
      ∀ T : ℝ, 1 ≤ T →
      (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ (δ / 2)) *
          (((N' * N' : ℕ) : ℝ) ^ (δ / 2)) ≤ T ^ ε) →
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
  obtain ⟨C, hC, hbase⟩ := exists_integral_mtWatt_divisorEnergy hδ
  refine ⟨C, hC, ?_⟩
  intro a A N N' hA hN hN' T hT hpow hM
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let M : ℝ := (((2 * A) * (N' * N') : ℕ) : ℝ)
  let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
  let Q : ℝ :=
    (T + (A : ℝ) ^ 2 * Real.sqrt T +
        (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
      ((N : ℝ) ^ 2 * (A : ℝ)) +
    (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hP0 : 0 ≤
      ((((M : ℝ) ^ (δ / 2)) * (((N' * N' : ℕ) : ℝ) ^ (δ / 2)))) := by
    positivity
  have hTpow0 : 0 ≤ T ^ ε := Real.rpow_nonneg hTpos.le _
  have hres0 : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
  have hnum : T + M ≤
      T + (A : ℝ) ^ 2 * Real.sqrt T +
        (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
    dsimp only [M] at hM ⊢
    nlinarith [sq_nonneg (A : ℝ), Real.sqrt_nonneg T]
  have hfrac : (T + M) / ((N : ℝ) ^ 2 * (A : ℝ)) ≤ Q := by
    dsimp only [Q]
    have hden : 0 ≤ (N : ℝ) ^ 2 * (A : ℝ) := by positivity
    exact (div_le_div_of_nonneg_right hnum hden).trans
      (le_add_of_nonneg_right hres0)
  have hshape :
      (T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 ≤
        Q * (1 / (A : ℝ)) * E := by
    have hfac0 : 0 ≤ (1 / (A : ℝ)) * E := mul_nonneg (by positivity) hE0
    have hs := mul_le_mul_of_nonneg_right hfrac hfac0
    calc
      (T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 =
          ((T + M) / ((N : ℝ) ^ 2 * (A : ℝ))) *
            ((1 / (A : ℝ)) * E) := by field_simp
      _ ≤ Q * ((1 / (A : ℝ)) * E) := hs
      _ = Q * (1 / (A : ℝ)) * E := by ring
  have hraw := hbase a A N N' hA hN hN' T hT
  have hC0 : 0 ≤ C := hC.le
  have hscaled :
      C * ((((M : ℝ) ^ (δ / 2)) * (((N' * N' : ℕ) : ℝ) ^ (δ / 2)))) *
          ((T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2) ≤
        C * T ^ ε * (Q * (1 / (A : ℝ)) * E) := by
    have hp := mul_le_mul hpow hshape (by positivity) hTpow0
    calc
      C * ((M : ℝ) ^ (δ / 2) * (((N' * N' : ℕ) : ℝ) ^ (δ / 2))) *
          ((T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2) =
          C * (((M : ℝ) ^ (δ / 2) * (((N' * N' : ℕ) : ℝ) ^ (δ / 2))) *
            ((T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2)) := by ring
      _ ≤ C * (T ^ ε * (Q * (1 / (A : ℝ)) * E)) :=
        mul_le_mul_of_nonneg_left hp hC0
      _ = C * T ^ ε * (Q * (1 / (A : ℝ)) * E) := by ring
  exact hraw.trans (by
    simpa only [M, E, Q, mul_assoc] using hscaled)

theorem exists_integral_mtWatt_lemma35_divisorRange
    {δ ε : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
      ∀ T : ℝ, 1 ≤ T →
      (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ (δ / 2)) *
          (((N' * N' : ℕ) : ℝ) ^ (δ / 2)) ≤ T ^ ε) →
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
  obtain ⟨C, hC, hbase⟩ := exists_integral_mtWatt_divisorEnergy hδ
  refine ⟨C, hC, ?_⟩
  intro a A N N' hA hN hN' T hT hpow hM
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let M : ℝ := (((2 * A) * (N' * N') : ℕ) : ℝ)
  let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
  let V : ℝ := mtWattCoefficientMaxSq a A
  let Q : ℝ :=
    (T + (A : ℝ) ^ 2 * Real.sqrt T) /
      ((N : ℝ) ^ 2 * (A : ℝ)) +
    (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hTpow0 : 0 ≤ T ^ ε := Real.rpow_nonneg hTpos.le _
  have hres0 : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
  have hnum : T + M ≤ T + (A : ℝ) ^ 2 * Real.sqrt T := by
    dsimp only [M] at hM ⊢
    linarith
  have hfrac : (T + M) / ((N : ℝ) ^ 2 * (A : ℝ)) ≤ Q := by
    dsimp only [Q]
    have hden : 0 ≤ (N : ℝ) ^ 2 * (A : ℝ) := by positivity
    exact (div_le_div_of_nonneg_right hnum hden).trans
      (le_add_of_nonneg_right hres0)
  have henergy : E ≤ (A : ℝ) * V := by
    simpa only [E, V] using sum_normSq_mtWattCoefficientBlock_le_max a hA
  have hshape :
      (T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 ≤ Q * V := by
    have hleft0 : 0 ≤ (T + M) * (1 / (A : ℝ) ^ 2) := by
      dsimp only [M]
      positivity
    have hNinv0 : 0 ≤ (1 / (N : ℝ)) ^ 2 := by positivity
    have hs₁ := mul_le_mul_of_nonneg_left henergy hleft0
    have hs₂ := mul_le_mul_of_nonneg_right hs₁ hNinv0
    calc
      (T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 ≤
          (T + M) * (1 / (A : ℝ) ^ 2) * ((A : ℝ) * V) *
            (1 / (N : ℝ)) ^ 2 := by simpa only [mul_assoc] using hs₂
      _ = ((T + M) / ((N : ℝ) ^ 2 * (A : ℝ))) * V := by field_simp
      _ ≤ Q * V := mul_le_mul_of_nonneg_right hfrac hV0
  have hraw := hbase a A N N' hA hN hN' T hT
  have hp := mul_le_mul hpow hshape (by positivity) hTpow0
  have hscaled :
      C * ((M : ℝ) ^ (δ / 2) * (((N' * N' : ℕ) : ℝ) ^ (δ / 2))) *
          ((T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2) ≤
        C * T ^ ε * (Q * V) := by
    calc
      C * ((M : ℝ) ^ (δ / 2) * (((N' * N' : ℕ) : ℝ) ^ (δ / 2))) *
          ((T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2) =
          C * (((M : ℝ) ^ (δ / 2) * (((N' * N' : ℕ) : ℝ) ^ (δ / 2))) *
            ((T + M) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2)) := by ring
      _ ≤ C * (T ^ ε * (Q * V)) := mul_le_mul_of_nonneg_left hp hC.le
      _ = C * T ^ ε * (Q * V) := by ring
  exact hraw.trans (by
    simpa only [M, E, V, Q, mul_assoc] using hscaled)

/-! ### Absorbing the divisor power from source-scale bounds -/

theorem mtWatt_divisorPower_le
    {ε : ℝ} (hε : 0 < ε) {A N N' : ℕ} {T : ℝ}
    (hT : 1 ≤ T) (hAT : (A : ℝ) ≤ T) (hNT : (N : ℝ) ≤ T)
    (hN' : N' ≤ 2 * N) :
    (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 10)) *
        (((N' * N' : ℕ) : ℝ) ^ (ε / 10))) ≤
      32 ^ (ε / 10) * T ^ (ε / 2) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hN'0 : 0 ≤ (N' : ℝ) := Nat.cast_nonneg _
  have hN'R : (N' : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN'
  have hN'T : (N' : ℝ) ≤ 2 * T := hN'R.trans (by linarith)
  have hNN : (((N' * N' : ℕ) : ℝ)) ≤ 4 * T ^ 2 := by
    push_cast
    nlinarith [mul_self_le_mul_self hN'0 hN'T]
  have hM : ((((2 * A) * (N' * N') : ℕ) : ℝ)) ≤ 8 * T ^ 3 := by
    push_cast
    have hNN' : (N' : ℝ) * (N' : ℝ) ≤ 4 * T ^ 2 := by
      simpa only [Nat.cast_mul] using hNN
    have hmul : (A : ℝ) * ((N' : ℝ) * (N' : ℝ)) ≤ T * (4 * T ^ 2) :=
      mul_le_mul hAT hNN' (mul_nonneg hN'0 hN'0) hT0
    nlinarith
  have he0 : 0 ≤ ε / 10 := by positivity
  have hMp := Real.rpow_le_rpow (Nat.cast_nonneg _) hM he0
  have hNNp := Real.rpow_le_rpow (Nat.cast_nonneg _) hNN he0
  calc
    (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 10)) *
        (((N' * N' : ℕ) : ℝ) ^ (ε / 10))) ≤
        (8 * T ^ 3) ^ (ε / 10) * (4 * T ^ 2) ^ (ε / 10) :=
      mul_le_mul hMp hNNp
        (Real.rpow_nonneg (Nat.cast_nonneg (N' * N')) _)
        (Real.rpow_nonneg (by positivity : 0 ≤ 8 * T ^ 3) _)
    _ = ((8 * T ^ 3) * (4 * T ^ 2)) ^ (ε / 10) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 8 * T ^ 3) (by positivity : 0 ≤ 4 * T ^ 2)]
    _ = (32 * T ^ 5) ^ (ε / 10) := by ring_nf
    _ = 32 ^ (ε / 10) * (T ^ 5) ^ (ε / 10) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) (by positivity : 0 ≤ T ^ 5)]
    _ = 32 ^ (ε / 10) * T ^ (ε / 2) := by
      congr 1
      have hfive : T ^ (5 : ℕ) = T ^ (5 : ℝ) :=
        (Real.rpow_natCast T 5).symm
      rw [hfive, ← Real.rpow_mul hT0]
      congr 1
      ring

theorem mtWatt_divisorPower_le_of_two_le
    {ε : ℝ} (hε : 0 < ε) {A N N' : ℕ} {T : ℝ}
    (hT : 2 ≤ T) (hAT : (A : ℝ) ≤ T) (hNT : (N : ℝ) ≤ T)
    (hN' : N' ≤ 2 * N) :
    (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 10)) *
        (((N' * N' : ℕ) : ℝ) ^ (ε / 10))) ≤ T ^ ε := by
  have hbase := mtWatt_divisorPower_le hε (one_le_two.trans hT) hAT hNT hN'
  have he0 : 0 ≤ ε / 10 := by positivity
  have h32 : (32 : ℝ) ≤ T ^ 5 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT 5
    norm_num at hpow ⊢
    exact hpow
  have h32pow : (32 : ℝ) ^ (ε / 10) ≤ (T ^ 5) ^ (ε / 10) :=
    Real.rpow_le_rpow (by norm_num) h32 he0
  have hT0 : 0 ≤ T := by positivity
  have hTpos : 0 < T := by positivity
  have hpowEq : (T ^ 5) ^ (ε / 10) = T ^ (ε / 2) := by
    have hfive : T ^ (5 : ℕ) = T ^ (5 : ℝ) :=
      (Real.rpow_natCast T 5).symm
    rw [hfive, ← Real.rpow_mul hT0]
    congr 1
    ring
  have hconst : (32 : ℝ) ^ (ε / 10) ≤ T ^ (ε / 2) := by
    rw [← hpowEq]
    exact h32pow
  calc
    _ ≤ 32 ^ (ε / 10) * T ^ (ε / 2) := hbase
    _ ≤ T ^ (ε / 2) * T ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hT0 _)
    _ = T ^ ε := by
      rw [← Real.rpow_add hTpos]
      congr 1
      ring

/-- The DI comparison with the divisor-power premise discharged from the source bounds
`A ≤ T`, `N ≤ T`, and `N' ≤ 2N`. -/
theorem exists_integral_mtDI_lemma35_divisorRange_of_le_height
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (A : ℝ) ≤ T → (N : ℝ) ≤ T →
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
  have hδ : 0 < ε / 5 := by positivity
  obtain ⟨C, hC, hbase⟩ :=
    exists_integral_mtDI_lemma35_divisorRange (δ := ε / 5) (ε := ε) hδ
  refine ⟨C, hC, ?_⟩
  intro a A N N' hA hN hN' T hT hAT hNT hM
  have hp := mtWatt_divisorPower_le_of_two_le hε hT hAT hNT hN'
  have hp' :
      (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ ((ε / 5) / 2)) *
        (((N' * N' : ℕ) : ℝ) ^ ((ε / 5) / 2))) ≤ T ^ ε := by
    simpa only [show (ε / 5) / 2 = ε / 10 by ring] using hp
  exact hbase a A N N' hA hN hN' T (one_le_two.trans hT) hp' hM

/-- The Watt comparison with the divisor-power premise discharged from the source bounds
`A ≤ T`, `N ≤ T`, and `N' ≤ 2N`. -/
theorem exists_integral_mtWatt_lemma35_divisorRange_of_le_height
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (A : ℝ) ≤ T → (N : ℝ) ≤ T →
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
  have hδ : 0 < ε / 5 := by positivity
  obtain ⟨C, hC, hbase⟩ :=
    exists_integral_mtWatt_lemma35_divisorRange (δ := ε / 5) (ε := ε) hδ
  refine ⟨C, hC, ?_⟩
  intro a A N N' hA hN hN' T hT hAT hNT hM
  have hp := mtWatt_divisorPower_le_of_two_le hε hT hAT hNT hN'
  have hp' :
      (((((2 * A) * (N' * N') : ℕ) : ℝ) ^ ((ε / 5) / 2)) *
        (((N' * N' : ℕ) : ℝ) ^ ((ε / 5) / 2))) ≤ T ^ ε := by
    simpa only [show (ε / 5) / 2 = ε / 10 by ring] using hp
  exact hbase a A N N' hA hN hN' T (one_le_two.trans hT) hp' hM

end

end RHTower.Sieve
