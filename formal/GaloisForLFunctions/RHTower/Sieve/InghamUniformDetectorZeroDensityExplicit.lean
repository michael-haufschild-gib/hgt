import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorZeroDensityPolylog
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorDensityExplicit

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- Actual zeta-zero count with a universal leading constant. Division by the engineered detector
gap contributes the single displayed factor `(1 - sigma)⁻¹`. -/
theorem exists_eventually_zetaLittlewoodZeroCountAbove_le_uniformGabrielExplicit :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ X : ℕ in Filter.atTop,
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K * (1 / (1 - sigma)) *
          (1 +
            ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
                (2 : ℕ) *
              (1 + inghamMovingRightTranslatedExplicitConstant
                ((9 / 100 : ℝ) * (1 - sigma))) *
              (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
              (1 + Real.log (X : ℝ)) ^
                (2 * inghamUniformGabrielCriticalShare sigma) +
            (1 + Real.log (X : ℝ)) ^ 2) := by
  obtain ⟨K₀, hK₀, hmass⟩ :=
    exists_eventually_zetaZeroMass_le_uniformGabrielExplicit
  let K : ℝ := K₀ * 1000 / (2 * Real.pi)
  have hden : 0 < 2 * Real.pi := by positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmass, eventually_ge_atTop (10 : ℕ)] with X hselectedAll hX
  intro sigma hsigma0 hsigma1
  let q : ℝ := 2 * Real.pi * (1 - sigma) / 1000
  have hq : 0 < q := by dsimp only [q]; positivity
  have hselected := hselectedAll hsigma0 hsigma1
  obtain ⟨T₁, hT₁, T₂, hT₂, hmassX⟩ := hselected
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hTnonneg : 0 ≤ (X : ℝ) - 2 := by linarith
  have hbot : T₁ ≤ -((X : ℝ) - 2) := by linarith [hT₁.2]
  have htop : (X : ℝ) - 2 ≤ T₂ := le_of_lt hT₂.1
  have hcenter4 : inghamUniformGabrielCenter sigma ≤ 4 := by
    unfold inghamUniformGabrielCenter
    linarith
  have hcountMass :=
    zetaLittlewoodZeroCountAbove_mul_le_selectedRectangleMass
      (c := inghamUniformGabrielCenter sigma) (d := 4) (T := (X : ℝ) - 2)
      (T₁ := T₁) (T₂ := T₂) (sigma := sigma)
      hcenter4 hTnonneg hbot htop
  have hgap : sigma - inghamUniformGabrielCenter sigma = (1 - sigma) / 1000 := by
    unfold inghamUniformGabrielCenter
    ring
  rw [hgap] at hcountMass
  let R : ℝ :=
    1 +
      ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
          (2 : ℕ) *
        (1 + inghamMovingRightTranslatedExplicitConstant
          ((9 / 100 : ℝ) * (1 - sigma))) *
        (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
        (1 + Real.log (X : ℝ)) ^
          (2 * inghamUniformGabrielCriticalShare sigma) +
      (1 + Real.log (X : ℝ)) ^ 2
  have hscaled :
      q * zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤ K₀ * R := by
    calc
      _ = 2 * Real.pi * (((1 - sigma) / 1000) *
          zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
            ((X : ℝ) - 2) sigma) := by dsimp only [q]; ring
      _ ≤ 2 * Real.pi *
          (∑ w ∈ zetaResidueUnitClosedRectangleZeros
              ((inghamUniformGabrielCenter sigma : ℂ) + (T₁ : ℂ) * I)
              ((4 : ℂ) + (T₂ : ℂ) * I),
            ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
              (w.re - inghamUniformGabrielCenter sigma)) :=
        mul_le_mul_of_nonneg_left hcountMass (by positivity)
      _ ≤ K₀ * R := by simpa only [R] using hmassX
  apply le_of_mul_le_mul_left (a := q) (a0 := hq)
  calc
    q * zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤ K₀ * R := hscaled
    _ = q * (K * (1 / (1 - sigma)) * R) := by
      have hgapne : 1 - sigma ≠ 0 := by linarith
      dsimp only [q, K]
      field_simp [Real.pi_ne_zero, hgapne]
    _ = q * (K * (1 / (1 - sigma)) *
          (1 +
            ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
                (2 : ℕ) *
              (1 + inghamMovingRightTranslatedExplicitConstant
                ((9 / 100 : ℝ) * (1 - sigma))) *
              (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
              (1 + Real.log (X : ℝ)) ^
                (2 * inghamUniformGabrielCriticalShare sigma) +
            (1 + Real.log (X : ℝ)) ^ 2)) := by rfl

end

end RHTower.Sieve
