import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorDensityPolylog
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorHorizontalBoundaryGlobal
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorCenterLogMomentExplicit

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- Weighted zeta-zero mass with one universal leading constant. All counting-line degeneration is
visible in the squared pole-recovery factor and explicit moving-right factor. -/
theorem exists_eventually_zetaZeroMass_le_uniformGabrielExplicit :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ X : ℕ in Filter.atTop,
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
        ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamUniformGabrielCenter sigma : ℂ) + (T₁ : ℂ) * I)
                  ((4 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamUniformGabrielCenter sigma)) ≤
            K * (1 +
                ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
                    (2 : ℕ) *
                  (1 + inghamMovingRightTranslatedExplicitConstant
                    ((9 / 100 : ℝ) * (1 - sigma))) *
                  (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
                  (1 + Real.log (X : ℝ)) ^
                    (2 * inghamUniformGabrielCriticalShare sigma) +
                (1 + Real.log (X : ℝ)) ^ 2) := by
  obtain ⟨Kₕ, hKₕ, hhorizontal⟩ :=
    exists_inghamClassicalHorizontalBoundary_global_polylog
  obtain ⟨C, hC, hcenter⟩ :=
    exists_intervalIntegral_log_norm_inghamClassicalDetector_uniformCenter_le_explicit
  let K : ℝ := C + Kₕ + 1 + 4 * Real.pi
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_inghamDetector_ne_zero_on_rightEdge
      (beta := 4) (by norm_num), eventually_ge_atTop (10 : ℕ)] with X hright hX
  intro sigma hsigma0 hsigma1
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hcenter699 : (699 / 1000 : ℝ) ≤ inghamUniformGabrielCenter sigma := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter0 : 0 ≤ inghamUniformGabrielCenter sigma := by
    linarith
  have hcenter4 : inghamUniformGabrielCenter sigma ≤ 4 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter4lt : inghamUniformGabrielCenter sigma < 4 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter1 : inghamUniformGabrielCenter sigma < 1 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  let P : ℝ := 4 * Real.pi * (1 - inghamUniformGabrielCenter sigma)
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hPmax : P ≤ 4 * Real.pi := by
    dsimp only [P]
    calc
      4 * Real.pi * (1 - inghamUniformGabrielCenter sigma) ≤
          4 * Real.pi * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * Real.pi := by ring
  obtain ⟨T₁, hT₁, T₂, hT₂, hzero₁, hzero₂, hhorizontalX⟩ :=
    hhorizontal hsigma0 hsigma1le hX
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hT₁neg : T₁ < 0 := by linarith [hT₁.2]
  have hT₂pos : 0 < T₂ := by linarith [hT₂.1]
  have hT : T₁ < T₂ := hT₁neg.trans hT₂pos
  have hbot : ∀ x ∈ Set.uIcc (inghamUniformGabrielCenter sigma) 4,
      inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hcenter4] at hx
    exact hzero₁ x hx
  have htop : ∀ x ∈ Set.uIcc (inghamUniformGabrielCenter sigma) 4,
      inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hcenter4] at hx
    exact hzero₂ x hx
  have hright' : ∀ t ∈ Set.uIcc T₁ T₂,
      inghamDetector X ((4 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t _
    exact hright t
  have hmass0 := two_pi_mul_zetaZeroMass_le_inghamLittlewoodBoundary X
    (c := inghamUniformGabrielCenter sigma) (d := 4) (T₁ := T₁) (T₂ := T₂)
    hcenter4lt hT hbot htop hright'
  have hgauge := inghamLittlewoodBoundary_eq_classical_add_poleCharge X
    (c := inghamUniformGabrielCenter sigma) (d := 4) (T₁ := T₁) (T₂ := T₂)
    hcenter1 (by norm_num)
    hT₁neg hT₂pos hbot htop hright'
  rw [hgauge] at hmass0
  have hboundary := inghamClassicalLittlewoodBoundary_four_le
    (show 1 ≤ X by omega) (c := inghamUniformGabrielCenter sigma) (T₁ := T₁) (T₂ := T₂)
    hcenter4 hT.le
  have hleft := hcenter hsigma0 hsigma1 (show 4 ≤ X by omega)
    (le_of_lt hT₁.1) hT.le (by linarith [hT₂.2])
  have hleft' :
      (∫ t in T₁..T₂,
        Real.log ‖inghamClassicalDetector X
          ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖) ≤
        C *
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
            (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by
    simpa only [inghamClassicalDetector] using hleft
  have hlen : T₂ - T₁ ≤ 2 * (X : ℝ) := by
    linarith [hT₁.1, hT₂.2]
  have hverticalFixed := farRightFour_verticalLoss_le_one
    (show 4 ≤ X by omega) hT.le hlen
  have hinner0 : 0 ≤ (T₂ - T₁) *
      (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)) := by
    positivity
  have hfixedle : inghamFixedGabrielSigma ≤ inghamUniformGabrielCenter sigma := by
    simpa only [inghamFixedGabrielSigma] using hcenter699
  have hvertical :
      (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
        (4 - inghamUniformGabrielCenter sigma) * ((T₂ - T₁) *
          (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) ≤ 1 := by
    calc
      _ ≤ (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
          (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
            (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_right (by linarith :
            4 - inghamUniformGabrielCenter sigma ≤ 4 - inghamFixedGabrielSigma)
            hinner0) _
      _ ≤ 1 := hverticalFixed
  have hdecomp :
      2 * Real.pi *
            (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                ((inghamUniformGabrielCenter sigma : ℂ) + (T₁ : ℂ) * I)
                ((4 : ℂ) + (T₂ : ℂ) * I),
              ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                (w.re - inghamUniformGabrielCenter sigma)) ≤
          (∫ t in T₁..T₂,
            Real.log ‖inghamClassicalDetector X
              ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖) +
          ((T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
            (4 - inghamUniformGabrielCenter sigma) * ((T₂ - T₁) *
              (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)))) +
          inghamClassicalHorizontalBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂ + P := by
    calc
      _ ≤ inghamClassicalLittlewoodBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂ +
          4 * Real.pi * (1 - inghamUniformGabrielCenter sigma) := hmass0
      _ ≤ ((∫ t in T₁..T₂,
              Real.log ‖inghamClassicalDetector X
                ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖) +
            (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
            (4 - inghamUniformGabrielCenter sigma) * ((T₂ - T₁) *
              (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) +
            inghamClassicalHorizontalBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂) +
          4 * Real.pi * (1 - inghamUniformGabrielCenter sigma) :=
        add_le_add hboundary (le_refl _)
      _ = _ := by dsimp only [P]; ring
  let Q : ℝ :=
    ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
        (2 : ℕ) *
      (1 + inghamMovingRightTranslatedExplicitConstant
        ((9 / 100 : ℝ) * (1 - sigma)))
  let A : ℝ := Q *
    (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
    (1 + Real.log (X : ℝ)) ^ (2 * inghamUniformGabrielCriticalShare sigma)
  let B : ℝ := (1 + Real.log (X : ℝ)) ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A, Q, inghamMovingRightTranslatedExplicitConstant]
    positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hCK : C ≤ K := by dsimp only [K]; linarith [Real.pi_pos]
  have hHK : Kₕ ≤ K := by dsimp only [K]; linarith [Real.pi_pos]
  have hPK : 1 + P ≤ K := by dsimp only [K]; linarith
  refine ⟨T₁, hT₁, T₂, hT₂, hdecomp.trans ?_⟩
  calc
    (∫ t in T₁..T₂,
          Real.log ‖inghamClassicalDetector X
            ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖) +
        ((T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
          (4 - inghamUniformGabrielCenter sigma) * ((T₂ - T₁) *
            (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)))) +
        inghamClassicalHorizontalBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂ + P ≤
      C * A + 1 + Kₕ * B + P := by
        dsimp only [A, Q, B]
        linarith
    _ = C * A + (1 + P) + Kₕ * B := by ring
    _ ≤ K * A + K + K * B :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCK hA) hPK)
        (mul_le_mul_of_nonneg_right hHK hB)
    _ = K * (1 + A + B) := by ring
    _ = K * (1 +
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
              (2 : ℕ) *
            (1 + inghamMovingRightTranslatedExplicitConstant
              ((9 / 100 : ℝ) * (1 - sigma))) *
            (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) +
          (1 + Real.log (X : ℝ)) ^ 2) := by rfl

end

end RHTower.Sieve
