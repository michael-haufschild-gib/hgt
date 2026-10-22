import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorHorizontalBoundary

/-!
# Weighted zeta-zero mass at the uniform Gabriel center

For `7/10 ≤ σ < 1` put `c_σ = σ - (1 - σ)/1000`. This module bounds the weighted zero mass
`2π ∑ ord_w (Re w - c_σ)`, summed over the zeros `w` of `(s-1)ζ(s)` in the rectangle
`[c_σ, 4] × [T₁, T₂]` with `T₁ ≈ -X`, `T₂ ≈ X`, by
`K (1 + X^{e(σ)} (1 + log X)^{2 θ(σ)} + (1 + log X)^2)`, for all sufficiently large `X`. Here
`e(σ)` is `inghamUniformGabrielConservativeExponent` and `θ(σ)` is
`inghamUniformGabrielCriticalShare`. The proof combines the weighted Littlewood identity for
Ingham's detector, the pole-gauge identity relating it to the classical detector, the left-edge
`log |F|` moment bound at `c_σ`, the far-right edge `Re s = 4`, and the polylogarithmic horizontal
boundary.

## Main results

- `exists_eventually_zetaZeroMass_le_uniformGabrielPolylog`: for `7/10 ≤ σ < 1` there is `K ≥ 0`
  such that for all large `X` there are `T₁ ∈ (-X, -X+1)`, `T₂ ∈ (X-2, X-1)` with weighted
  zeta-zero mass in `[c_σ, 4] × [T₁, T₂]` at most
  `K (1 + X^{e(σ)} (1 + log X)^{2θ(σ)} + (1 + log X)^2)`.

## Hypotheses

The result is unconditional; it assumes only the range `7/10 ≤ σ < 1`, and the bound holds
eventually in `X`.
-/

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- For `7/10 ≤ σ < 1` there is `K ≥ 0` such that, for all large `X`, some heights
`T₁ ∈ (-X, -X+1)` and `T₂ ∈ (X-2, X-1)` give `2π ∑ ord_w (Re w - c_σ) ≤
K (1 + X^{e(σ)} (1 + log X)^{2θ(σ)} + (1 + log X)^2)` over zeta zeros in `[c_σ, 4] × [T₁, T₂]`. -/
theorem exists_eventually_zetaZeroMass_le_uniformGabrielPolylog
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in Filter.atTop,
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
        ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamUniformGabrielCenter sigma : ℂ) + (T₁ : ℂ) * I)
                  ((4 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamUniformGabrielCenter sigma)) ≤
            K * (1 +
                (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
                  (1 + Real.log (X : ℝ)) ^
                    (2 * inghamUniformGabrielCriticalShare sigma) +
                (1 + Real.log (X : ℝ)) ^ 2) := by
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hcenter699 : (699 / 1000 : ℝ) ≤ inghamUniformGabrielCenter sigma := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter4 : inghamUniformGabrielCenter sigma ≤ 4 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter4lt : inghamUniformGabrielCenter sigma < 4 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter1 : inghamUniformGabrielCenter sigma < 1 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  obtain ⟨Kₕ, hKₕ, hhorizontal⟩ :=
    exists_inghamClassicalHorizontalBoundary_uniformCenter_polylog hsigma0 hsigma1le
  obtain ⟨C, hC, hcenter⟩ :=
    exists_intervalIntegral_log_norm_inghamClassicalDetector_uniformCenter_le_polylog
      hsigma0 hsigma1
  let P : ℝ := 4 * Real.pi * (1 - inghamUniformGabrielCenter sigma)
  let K : ℝ := C + Kₕ + 1 + P
  have hP : 0 ≤ P := by
    dsimp only [P]
    have hpi := Real.pi_pos.le
    have hc : 0 ≤ 1 - inghamUniformGabrielCenter sigma := by
      linarith
    positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_inghamDetector_ne_zero_on_rightEdge
      (beta := 4) (by norm_num), eventually_ge_atTop (10 : ℕ)] with X hright hX
  obtain ⟨T₁, hT₁, T₂, hT₂, hzero₁, hzero₂, hhorizontalX⟩ :=
    hhorizontal hX
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
  have hleft := hcenter (show 4 ≤ X by omega)
    (le_of_lt hT₁.1) hT.le (by linarith [hT₂.2])
  have hleft' :
      (∫ t in T₁..T₂,
        Real.log ‖inghamClassicalDetector X
          ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖) ≤
        C * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
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
  let A : ℝ := (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
    (1 + Real.log (X : ℝ)) ^ (2 * inghamUniformGabrielCriticalShare sigma)
  let B : ℝ := (1 + Real.log (X : ℝ)) ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hCK : C ≤ K := by dsimp only [K]; linarith
  have hHK : Kₕ ≤ K := by dsimp only [K]; linarith
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
        dsimp only [A, B]
        linarith
    _ = C * A + (1 + P) + Kₕ * B := by ring
    _ ≤ K * A + K + K * B :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCK hA) hPK)
        (mul_le_mul_of_nonneg_right hHK hB)
    _ = K * (1 + A + B) := by ring
    _ = K * (1 +
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) +
          (1 + Real.log (X : ℝ)) ^ 2) := by rfl


end

end RHTower.Sieve

