import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDIOverHeight

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Explicit absolute constant for the over-height branch of Lemma 3.5. -/
def mtLemma35OverHeightConst : ℝ :=
  (2 * (6 * Real.pi + 1)) ^ 4 *
    (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2)

theorem integral_mtLemma35_overHeight_le_residualEnergy
    (a : ℕ → ℂ) {A N N' : ℕ} (hA : 1 ≤ A)
    (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {T : ℝ} (hT : 1 ≤ T) (hTN : T ≤ (N : ℝ)) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      mtLemma35OverHeightConst *
        ((T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
        (1 / (A : ℝ)) *
        (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2) := by
  have hbase := integral_mtWatt_overHeight_le_energy a hA hN hNN' hN' hT hTN
  have hTR0 : (0 : ℝ) < T := zero_lt_one.trans_le hT
  have hAR0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  let B : ℝ := 2 * (6 * Real.pi + 1)
  let c₁ : ℝ := 5 * Real.pi * Real.exp 1
  let c₂ : ℝ := 5 * Real.pi / 2
  let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
  have hbase' :
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        (B / T) ^ 4 * (c₁ / (A : ℝ) + c₂ * (1 / (A : ℝ) ^ 2) * T) * E := by
    simpa only [B, c₁, c₂, E, div_eq_mul_inv, one_mul] using hbase
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hc₁0 : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hx0 : 0 ≤ 1 / (T ^ 4 * (A : ℝ)) := by positivity
  have hy0 : 0 ≤ 1 / (T ^ 3 * (A : ℝ) ^ 2) := by positivity
  have hcoeff : c₁ * (1 / (T ^ 4 * (A : ℝ))) +
        c₂ * (1 / (T ^ 3 * (A : ℝ) ^ 2)) ≤
      (c₁ + c₂) *
        (1 / (T ^ 4 * (A : ℝ)) + 1 / (T ^ 3 * (A : ℝ) ^ 2)) := by
    nlinarith
  have hexisting :
      (B / T) ^ 4 * (c₁ / (A : ℝ) + c₂ * (1 / (A : ℝ) ^ 2) * T) =
        B ^ 4 *
          (c₁ * (1 / (T ^ 4 * (A : ℝ))) +
            c₂ * (1 / (T ^ 3 * (A : ℝ) ^ 2))) := by
    field_simp
  have hresidual :
      (1 / (T ^ 4 * (A : ℝ)) + 1 / (T ^ 3 * (A : ℝ) ^ 2)) =
        (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) * (1 / (A : ℝ)) := by
    field_simp
    all_goals ring
  have hshape :
      (B / T) ^ 4 * (c₁ / (A : ℝ) + c₂ * (1 / (A : ℝ) ^ 2) * T) * E ≤
        (B ^ 4 * (c₁ + c₂)) *
          ((T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) * (1 / (A : ℝ))) * E := by
    rw [hexisting, ← hresidual]
    have hs := mul_le_mul_of_nonneg_left hcoeff (pow_nonneg hB0 4)
    have hs' :
        B ^ 4 *
            (c₁ * (1 / (T ^ 4 * (A : ℝ))) + c₂ * (1 / (T ^ 3 * (A : ℝ) ^ 2))) ≤
          (B ^ 4 * (c₁ + c₂)) *
            (1 / (T ^ 4 * (A : ℝ)) + 1 / (T ^ 3 * (A : ℝ) ^ 2)) := by
      calc
        _ ≤ B ^ 4 * ((c₁ + c₂) *
            (1 / (T ^ 4 * (A : ℝ)) + 1 / (T ^ 3 * (A : ℝ) ^ 2))) := hs
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right hs' hE0
  have hfinal := hbase'.trans hshape
  simpa only [mtLemma35OverHeightConst, B, c₁, c₂, E, mul_assoc] using hfinal

theorem integral_mtDI_lemma35_overHeight
    (a : ℕ → ℂ) {A N N' : ℕ} (hA : 1 ≤ A)
    (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {T ε : ℝ} (hT : 1 ≤ T) (hTN : T ≤ (N : ℝ)) (hε : 0 < ε) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      mtLemma35OverHeightConst * T ^ ε *
        (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
              ((N : ℝ) ^ 2 * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
          (1 / (A : ℝ)) *
          (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2)) := by
  have hbase := integral_mtLemma35_overHeight_le_residualEnergy a hA hN hNN' hN' hT hTN
  have hTR0 : (0 : ℝ) < T := zero_lt_one.trans_le hT
  have hAR0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hpow : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hmain0 : 0 ≤
      (T + (A : ℝ) ^ 2 * Real.sqrt T +
          (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
        ((N : ℝ) ^ 2 * (A : ℝ)) := by positivity
  have hres0 : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
  have hfactor0 : 0 ≤ (1 / (A : ℝ)) * E := mul_nonneg (by positivity) hE0
  have henlarge :
      mtLemma35OverHeightConst *
          ((T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) * (1 / (A : ℝ)) * E ≤
        mtLemma35OverHeightConst * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (1 / (A : ℝ)) * E) := by
    have hC0 : 0 ≤ mtLemma35OverHeightConst := by
      dsimp [mtLemma35OverHeightConst]
      positivity
    have hinside :
        (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) * ((1 / (A : ℝ)) * E) ≤
          T ^ ε *
            (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                    (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                  ((N : ℝ) ^ 2 * (A : ℝ)) +
                (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
              ((1 / (A : ℝ)) * E)) := by
      have hadd :
          (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) ≤
            (T + (A : ℝ) ^ 2 * Real.sqrt T +
                (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
              ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by linarith
      have hs := mul_le_mul_of_nonneg_right hadd hfactor0
      have hnonneg : 0 ≤
          ((T + (A : ℝ) ^ 2 * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            ((1 / (A : ℝ)) * E) :=
        mul_nonneg (add_nonneg hmain0 hres0) hfactor0
      exact hs.trans (le_mul_of_one_le_left hnonneg hpow)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinside hC0
  simpa only [E] using hbase.trans henlarge

/-- Genuine finite maximum of the squared coefficient norms on `(A,2A]`. -/
def mtWattCoefficientMaxSq (a : ℕ → ℂ) (A : ℕ) : NNReal :=
  (Finset.Ioc A (2 * A)).sup (fun m => ⟨‖a m‖ ^ 2, sq_nonneg _⟩)

theorem sum_normSq_mtWattCoefficientBlock_le_max
    (a : ℕ → ℂ) {A : ℕ} (hA : 1 ≤ A) :
    (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2) ≤
      (A : ℝ) * (mtWattCoefficientMaxSq a A : ℝ) := by
  let s := Finset.Ioc A (2 * A)
  let f : ℕ → NNReal := fun m => ⟨‖a m‖ ^ 2, sq_nonneg _⟩
  have hpoint : ∀ m ∈ s, f m ≤ s.sup f := fun m hm => Finset.le_sup hm
  have hsum := Finset.sum_le_card_nsmul s f (s.sup f) hpoint
  have hcard : s.card = A := by
    dsimp [s]
    rw [Nat.card_Ioc]
    omega
  rw [hcard, nsmul_eq_mul] at hsum
  change (∑ m ∈ s, (f m : ℝ)) ≤ (A : ℝ) * ((s.sup f : NNReal) : ℝ)
  exact_mod_cast hsum

theorem integral_mtWatt_lemma35_overHeight
    (a : ℕ → ℂ) {A N N' : ℕ} (hA : 1 ≤ A)
    (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {T ε : ℝ} (hT : 1 ≤ T) (hTN : T ≤ (N : ℝ)) (hε : 0 < ε) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      mtLemma35OverHeightConst * T ^ ε *
        (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
              ((N : ℝ) ^ 2 * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
          (mtWattCoefficientMaxSq a A : ℝ)) := by
  have hbase := integral_mtLemma35_overHeight_le_residualEnergy a hA hN hNN' hN' hT hTN
  have henergy := sum_normSq_mtWattCoefficientBlock_le_max a hA
  have hTR0 : (0 : ℝ) < T := zero_lt_one.trans_le hT
  have hAR0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
  let M : ℝ := mtWattCoefficientMaxSq a A
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have henergy' : (1 / (A : ℝ)) * E ≤ M := by
    have hscaled := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 1 / (A : ℝ))
    calc
      (1 / (A : ℝ)) * E ≤ (1 / (A : ℝ)) * ((A : ℝ) * M) := by
        simpa only [E, M] using hscaled
      _ = M := by field_simp
  have hpow : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hmain0 : 0 ≤
      (T + (A : ℝ) ^ 2 * Real.sqrt T) /
        ((N : ℝ) ^ 2 * (A : ℝ)) := by positivity
  have hres0 : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
  have hinside :
      (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) * ((1 / (A : ℝ)) * E) ≤
        T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) * M) := by
    have hresEnergy := mul_le_mul_of_nonneg_left henergy' hres0
    have hadd :
        (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) * M ≤
          ((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) * M := by
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hmain0) hM0
    have hnonneg : 0 ≤
        ((T + (A : ℝ) ^ 2 * Real.sqrt T) /
              ((N : ℝ) ^ 2 * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) * M :=
      mul_nonneg (add_nonneg hmain0 hres0) hM0
    exact (hresEnergy.trans hadd).trans (le_mul_of_one_le_left hnonneg hpow)
  have hC0 : 0 ≤ mtLemma35OverHeightConst := by
    dsimp [mtLemma35OverHeightConst]
    positivity
  have henlarge := mul_le_mul_of_nonneg_left hinside hC0
  have henlarge' :
      mtLemma35OverHeightConst *
          ((T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
          (1 / (A : ℝ)) *
          (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2) ≤
        mtLemma35OverHeightConst * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (mtWattCoefficientMaxSq a A : ℝ)) := by
    simpa only [E, M, mul_assoc] using henlarge
  exact hbase.trans henlarge'

end

end RHTower.Sieve
