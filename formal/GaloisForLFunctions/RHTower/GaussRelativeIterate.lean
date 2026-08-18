import GaloisForLFunctions.RHTower.GaussClassStep
import GaloisForLFunctions.RHTower.GaussPairingOneStep
import GaloisForLFunctions.RHTower.GaussIterate

/-!
# The relative one-step estimate along the iterates

Everything the pairing needs is now in place: the class is invariant under the principal step, the
one-step deviation is a pair of coefficientwise sums, and those sums vanish under an explicit
inequality between the spike exponents and the bulk exponents.  With the tied class the inequality
is `c_P + c_Q + 1 < θ_P + θ_Q`, and the concrete parameters `c₀ = 1/(8m)`, `ε = 1/(24m²)` satisfy
it for every `i < m`.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

theorem tendsto_zero_of_ofReal_tendsto_zero {f : ℕ → ℝ} (hf : ∀ I, 0 ≤ f I)
    (h : Tendsto (fun I => ENNReal.ofReal (f I)) atTop (nhds 0)) : Tendsto f atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ENNReal.tendsto_nhds_zero.mp h
    (ENNReal.ofReal (δ / 2)) (by simpa using half_pos hδ))
  refine ⟨N, fun n hn => ?_⟩
  have hle := (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp (hN n hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)]
  linarith

/-- Translation preserves the two-piece class. -/
theorem TwoPieceAmplitude.translate {A θ B c : ℝ} {I : ℕ}
    {u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))} (δ : AddCircle (1 : ℝ))
    (h : TwoPieceAmplitude A θ B c I (fun j => fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j)) :
    TwoPieceAmplitude A θ B c I
      (fun j => fourierCoeff ((gaussTranslationBlock δ u : AddCircle (1 : ℝ) → ℂ)) j) := by
  intro j
  have heq : ‖fourierCoeff ((gaussTranslationBlock δ u : AddCircle (1 : ℝ) → ℂ)) j‖
      = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ := by
    rw [← gaussRotationBlock_eq_translation, fourierCoeff_gaussRotationBlock, norm_mul,
      norm_fourier_eq_one, one_mul]
  rw [heq]
  exact h j

/-! ## The class of the fixed left vector -/

theorem twoPieceAmplitude_gaussPrimeScaleBlock_amplitudePow {p : ℝ} (hp : 1 < p) {c : ℝ}
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (r : ℕ) (I : ℕ) :
    TwoPieceAmplitude (4 * p ^ (r + 1)) 1 (0 / (1 + (I : ℝ)) ^ (1 : ℝ)) c I
      (fun j => fourierCoeff ((gaussPrimeScaleBlock hp
        ((gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) ^ r) (fourierLp 2 0)) :
          AddCircle (1 : ℝ) → ℂ)) j) := by
  have hzero : (0 : ℝ) / (1 + (I : ℝ)) ^ (1 : ℝ) = 0 := by simp
  rw [hzero]
  refine TwoPieceAmplitude.uniform (fun j => ?_) le_rfl
  rw [Real.rpow_one]
  exact norm_fourierCoeff_gaussPrimeScaleBlock_amplitudePow hp hs0 hs1 r j

/-! ## The relative one-step estimate -/

set_option maxHeartbeats 4000000 in
/-- **The one-step deviation, paired against a model iterate, vanishes.** -/
theorem tendsto_norm_inner_gaussPrincipalStep_sub_iterate_zero_of (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i s : ℕ) {ε c₀ : ℝ}
    (hε0 : 0 < ε) (hc₀0 : 0 < c₀)
    (hN1 : c₀ + (i : ℝ) / (m : ℝ) < 1) (hN2 : 3 * (i : ℝ) * ε < 1)
    (hN3 : ε < 1 - 3 * (i : ℝ) * ε) (hN7 : c₀ + 1 / (2 * (m : ℝ)) < 1) (hN8 : ε < 1)
    (hN9 : ε < 1 - 3 * (i : ℝ) * ε - ε)
    (hN10 : (c₀ + 1 / (2 * (m : ℝ))) + (c₀ + (i : ℝ) / (m : ℝ)) + 1
      < (1 - ε) + (1 - 3 * (i : ℝ) * ε - ε))
    (hN11 : c₀ + (c₀ + (i : ℝ) / (m : ℝ)) + 1 < 1 + (1 - 3 * (i : ℝ) * ε - ε - ε)) :
    Tendsto (fun I : ℕ => ‖(inner ℂ
        ((gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) ^ s)
          (fourierLp 2 0))
        (gaussPrincipalStepBlock (le_trans one_le_two hm2) k p hp (I : ℤ)
            ((gaussPrincipalStepBlock (le_trans one_le_two hm2) k p hp (I : ℤ) ^ i)
              (fourierLp 2 0)) -
          gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ))
            ((gaussPrincipalStepBlock (le_trans one_le_two hm2) k p hp (I : ℤ) ^ i)
              (fourierLp 2 0))) : ℂ)‖) atTop (nhds 0) := by
  have hm : 1 ≤ m := le_trans one_le_two hm2
  have hM0 : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm k p
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have h3iε0 : (0 : ℝ) ≤ 3 * (i : ℝ) * ε := by positivity
  have hcY0 : (0 : ℝ) < c₀ + (i : ℝ) / (m : ℝ) := by positivity
  have hcX0 : (0 : ℝ) < c₀ + 1 / (2 * (m : ℝ)) := by positivity
  have hA4 : (0 : ℝ) ≤ 4 * (p : ℝ) ^ (s + 1) := by positivity
  -- the class of the iterate, and of `B` applied to it
  obtain ⟨A0, B0, hA0, hB0, hcl0⟩ :=
    exists_gaussClass_principalStep_pow hm k p hp hK hKb hc₀0 hε0 i hN1 hN2
  obtain ⟨AY, BY, hAY, hBY, hYstep⟩ := exists_gaussClass_primeScale_step
    (θ := 1 - 3 * (i : ℝ) * ε) hp hcY0 hN1 (by linarith) hε0 hN3 A0 B0 hA0 hB0
  obtain ⟨AZ, BZ, hAZ, hBZ, hZstep⟩ := exists_gaussClass_primeScaleInvSq_step
    (θ := 1 - 3 * (i : ℝ) * ε - ε) hp hcY0 hN1 (by linarith) hε0 hN9 AY BY hAY hBY
  obtain ⟨AX, BX, hAX, hBX, hXstep⟩ := exists_gaussClass_primeScaleInvSq_step
    (θ := (1 : ℝ)) hp hcX0 hN7 le_rfl hε0 hN8
    (Real.sqrt (1 + 2 * K) * (4 * (p : ℝ) ^ (s + 1)))
    ((2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) * (2 * (4 * (p : ℝ) ^ (s + 1)) + 0))
    (by positivity)
    (by
      have : (0 : ℝ) ≤ (2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) := Real.rpow_nonneg (by positivity) _
      positivity)
  -- the three families
  have hBg : ∀ I : ℕ, TwoPieceAmplitude (4 * (p : ℝ) ^ (s + 1)) 1
      (0 / (1 + (I : ℝ)) ^ (1 : ℝ)) c₀ I
      (fun j => fourierCoeff ((gaussPrimeScaleBlock hp
        ((gaussMovingAmplitudeBlock hp
          ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) ^ s) (fourierLp 2 0)) :
          AddCircle (1 : ℝ) → ℂ)) j) := by
    intro I
    have hbase := twoPieceAmplitude_gaussPrimeScaleBlock_amplitudePow (c := c₀) hp
      (Int.fract_nonneg (gaussSamplePhase m p (I : ℤ)))
      (Int.fract_lt_one (gaussSamplePhase m p (I : ℤ))) s I
    rwa [coe_fract_eq] at hbase
  have hXcl : ∀ I : ℕ, 2 ≤ I → TwoPieceAmplitude AX (1 - ε) (BX / (1 + (I : ℝ)) ^ (1 - ε))
      (c₀ + 1 / (2 * (m : ℝ))) I
      (fun j => fourierCoeff ((gaussPrimeScaleInvSqBlock hp
        (gaussShiftedBlockOf hm k p (I : ℤ) (gaussPrimeScaleBlock hp
          ((gaussMovingAmplitudeBlock hp
            ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) ^ s) (fourierLp 2 0)))) :
              AddCircle (1 : ℝ) → ℂ)) j) := by
    intro I hI
    have h2 := gaussClass_shiftedBlockOf_step hm k p hK hKb hA4 le_rfl zero_le_one le_rfl hc₀0 hI
      _ (hBg I)
    exact hXstep I (by omega) _ h2
  have hYcl : ∀ I : ℕ, 2 ≤ I →
      TwoPieceAmplitude AY (1 - 3 * (i : ℝ) * ε - ε)
        (BY / (1 + (I : ℝ)) ^ (1 - 3 * (i : ℝ) * ε - ε)) (c₀ + (i : ℝ) / (m : ℝ)) I
        (fun j => fourierCoeff ((gaussPrimeScaleBlock hp
          ((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ i) (fourierLp 2 0)) :
            AddCircle (1 : ℝ) → ℂ)) j) :=
    fun I hI => hYstep I (by omega) _ (hcl0 I hI)
  have hZcl : ∀ I : ℕ, 2 ≤ I →
      TwoPieceAmplitude AZ (1 - 3 * (i : ℝ) * ε - ε - ε)
        (BZ / (1 + (I : ℝ)) ^ (1 - 3 * (i : ℝ) * ε - ε - ε)) (c₀ + (i : ℝ) / (m : ℝ)) I
        (fun j => fourierCoeff ((gaussPrimeScaleInvSqBlock hp
          (gaussTranslationBlock ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ))
            (gaussPrimeScaleBlock hp
              ((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ i) (fourierLp 2 0)))) :
                AddCircle (1 : ℝ) → ℂ)) j) :=
    fun I hI => hZstep I (by omega) _ (TwoPieceAmplitude.translate _ (hYcl I hI))
  -- the two pairing limits
  have hT1 := tendsto_tsum_twoPiece_pairing_defect_zero (k := k) (p := p) hm
    (AP := AX) (θP := 1 - ε) (BP := BX) (σP := 1 - ε) (cP := c₀ + 1 / (2 * (m : ℝ)))
    (AQ := AY) (θQ := 1 - 3 * (i : ℝ) * ε - ε) (BQ := BY) (σQ := 1 - 3 * (i : ℝ) * ε - ε)
    (cQ := c₀ + (i : ℝ) / (m : ℝ))
    hAX hBX hAY hBY hcX0.le hcY0.le (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) _ _ hXcl hYcl
  have hT2 := tendsto_tsum_twoPiece_pairing_defect_zero (k := k) (p := p) hm
    (AP := 4 * (p : ℝ) ^ (s + 1)) (θP := (1 : ℝ)) (BP := 0) (σP := (1 : ℝ)) (cP := c₀)
    (AQ := AZ) (θQ := 1 - 3 * (i : ℝ) * ε - ε - ε) (BQ := BZ)
    (σQ := 1 - 3 * (i : ℝ) * ε - ε - ε) (cQ := c₀ + (i : ℝ) / (m : ℝ))
    hA4 le_rfl hAZ hBZ hc₀0.le hcY0.le (by norm_num) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) _ _
    (fun I _ => hBg I) hZcl
  have hsum := hT1.add hT2
  rw [add_zero] at hsum
  refine tendsto_zero_of_ofReal_tendsto_zero (fun I => norm_nonneg _) ?_
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hsum η hη] with I hI
  refine le_trans ?_ hI
  exact ofReal_norm_inner_gaussPrincipalStep_sub_le hm k p hp (I : ℤ) _ _

set_option maxHeartbeats 1000000 in
/-- **The relative one-step estimate at the concrete parameters** `c₀ = 1/(8m)`, `ε = 1/(24m²)`. -/
theorem tendsto_norm_inner_gaussPrincipalStep_sub_iterate_zero (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i s : ℕ) (hi : i < m) :
    Tendsto (fun I : ℕ => ‖(inner ℂ
        ((gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) ^ s)
          (fourierLp 2 0))
        (gaussPrincipalStepBlock (le_trans one_le_two hm2) k p hp (I : ℤ)
            ((gaussPrincipalStepBlock (le_trans one_le_two hm2) k p hp (I : ℤ) ^ i)
              (fourierLp 2 0)) -
          gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ))
            ((gaussPrincipalStepBlock (le_trans one_le_two hm2) k p hp (I : ℤ) ^ i)
              (fourierLp 2 0))) : ℂ)‖) atTop (nhds 0) := by
  have hM2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hJ : (i : ℝ) ≤ (m : ℝ) - 1 := by
    have h : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hi
    linarith
  have hJ0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  refine tendsto_norm_inner_gaussPrincipalStep_sub_iterate_zero_of hm2 k p hp i s
    (ε := 1 / (24 * (m : ℝ) ^ 2)) (c₀ := 1 / (8 * (m : ℝ)))
    (by positivity) (by positivity) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · field_simp
    nlinarith [hJ, hM2, hJ0]
  · field_simp
    nlinarith [hJ, hM2, hJ0]
  · field_simp
    nlinarith [hJ, hM2, hJ0]
  · field_simp
    nlinarith [hM2]
  · field_simp
    nlinarith [hM2]
  · field_simp
    nlinarith [hJ, hM2, hJ0]
  · field_simp
    nlinarith [hJ, hM2, hJ0, mul_nonneg hJ0 hM0.le]
  · field_simp
    nlinarith [hJ, hM2, hJ0, mul_nonneg hJ0 hM0.le]

end

end RHTower
