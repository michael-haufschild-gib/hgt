import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaMaLocalization
import Mathlib.Tactic

/-!
# Temporal localization of the Akhmediev breather

The Akhmediev field retains its oscillating carrier and therefore need not converge as a complex
field in time.  Its squared magnitude is a plane-wave background `1/2` plus an explicit rational
correction that vanishes at both temporal infinities.  Hence its magnitude tends to `1/sqrt 2`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open Filter

theorem akhmedievNumeratorSq_sub_denominator_sq
    (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievNumeratorSq φ ξ τ - akhmedievDenominator φ ξ τ ^ (2 : ℕ) =
      4 * Real.sin (φ : ℝ) ^ (2 : ℕ) * Real.cos (φ : ℝ) *
        (Real.cosh (akhmedievOmega φ * τ) *
            Real.cos (akhmedievWaveNumber φ * ξ) - Real.cos (φ : ℝ)) := by
  rw [akhmedievNumeratorSq, akhmedievDenominator, Real.cos_two_mul,
    Real.sin_two_mul]
  rw [show (Real.sinh (akhmedievOmega φ * τ) *
      (2 * Real.sin (φ : ℝ) * Real.cos (φ : ℝ))) ^ (2 : ℕ) =
      4 * Real.sinh (akhmedievOmega φ * τ) ^ (2 : ℕ) * Real.sin (φ : ℝ) ^ (2 : ℕ) *
        Real.cos (φ : ℝ) ^ (2 : ℕ) by ring]
  have hsin : Real.sin (φ : ℝ) ^ (2 : ℕ) = 1 - Real.cos (φ : ℝ) ^ (2 : ℕ) := by
    nlinarith [Real.sin_sq_add_cos_sq (φ : ℝ)]
  rw [Real.sinh_sq, hsin]
  ring

noncomputable def akhmedievLocalizationCorrection
    (φ : BreatherAngle) (ξ τ : ℝ) : ℝ :=
  2 * Real.sin (φ : ℝ) ^ (2 : ℕ) * Real.cos (φ : ℝ) *
    (Real.cosh (akhmedievOmega φ * τ) * Real.cos (akhmedievWaveNumber φ * ξ) -
      Real.cos (φ : ℝ)) / akhmedievDenominator φ ξ τ ^ (2 : ℕ)

theorem norm_akhmedievBreather_sq_eq_background_add
    (φ : BreatherAngle) (ξ τ : ℝ) :
    ‖akhmedievBreather φ ξ τ‖ ^ (2 : ℕ) =
      1 / 2 + akhmedievLocalizationCorrection φ ξ τ := by
  rw [norm_akhmedievBreather_sq, akhmedievLocalizationCorrection]
  have hdiff := akhmedievNumeratorSq_sub_denominator_sq φ ξ τ
  have hne : akhmedievDenominator φ ξ τ ≠ 0 :=
    ne_of_gt (akhmedievDenominator_pos φ ξ τ)
  field_simp [hne]
  nlinarith

theorem akhmedievOmega_pos (φ : BreatherAngle) : 0 < akhmedievOmega φ := by
  rw [akhmedievOmega]
  exact Real.sin_pos_of_pos_of_lt_pi
    (by linarith [φ.property.1]) (by linarith [φ.property.2, Real.pi_pos])

theorem tendsto_akhmedievCosh_atTop (φ : BreatherAngle) :
    Tendsto (fun τ => Real.cosh (akhmedievOmega φ * τ)) atTop atTop := by
  let p : PositiveScale := ⟨akhmedievOmega φ, akhmedievOmega_pos φ⟩
  exact tendsto_cosh_positive_mul_atTop p

theorem tendsto_akhmedievLocalizationCorrection_atTop
    (φ : BreatherAngle) (ξ : ℝ) :
    Tendsto (akhmedievLocalizationCorrection φ ξ) atTop (nhds 0) := by
  let C : ℝ → ℝ := fun τ => Real.cosh (akhmedievOmega φ * τ)
  let c : ℝ := Real.cos (φ : ℝ)
  let y : ℝ := Real.cos (akhmedievWaveNumber φ * ξ)
  have hC : Tendsto C atTop atTop := tendsto_akhmedievCosh_atTop φ
  have hR : Tendsto (fun τ => (C τ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hC
  have hR2 : Tendsto (fun τ => (C τ)⁻¹ ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa using hR.pow 2
  have hnum : Tendsto (fun τ => y * (C τ)⁻¹ - c * (C τ)⁻¹ ^ (2 : ℕ))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hR).sub (tendsto_const_nhds.mul hR2)
  have hbase : Tendsto (fun τ => 1 - c * y * (C τ)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hR)
  have hden : Tendsto (fun τ => (1 - c * y * (C τ)⁻¹) ^ (2 : ℕ)) atTop (nhds 1) := by
    simpa using hbase.pow 2
  have hquot : Tendsto
      (fun τ => (y * (C τ)⁻¹ - c * (C τ)⁻¹ ^ (2 : ℕ)) /
        (1 - c * y * (C τ)⁻¹) ^ (2 : ℕ)) atTop (nhds 0) := by
    change Tendsto
      ((fun τ => y * (C τ)⁻¹ - c * (C τ)⁻¹ ^ (2 : ℕ)) /
        (fun τ => (1 - c * y * (C τ)⁻¹) ^ (2 : ℕ))) atTop (nhds 0)
    simpa using hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hscaled : Tendsto
      (fun τ => (2 * Real.sin (φ : ℝ) ^ (2 : ℕ) * c) *
        ((y * (C τ)⁻¹ - c * (C τ)⁻¹ ^ (2 : ℕ)) /
          (1 - c * y * (C τ)⁻¹) ^ (2 : ℕ))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hquot : Tendsto
      (fun τ => (2 * Real.sin (φ : ℝ) ^ (2 : ℕ) * c) *
        ((y * (C τ)⁻¹ - c * (C τ)⁻¹ ^ (2 : ℕ)) /
          (1 - c * y * (C τ)⁻¹) ^ (2 : ℕ))) atTop
      (nhds ((2 * Real.sin (φ : ℝ) ^ (2 : ℕ) * c) * 0)))
  apply hscaled.congr'
  filter_upwards with τ
  have hCne : C τ ≠ 0 := ne_of_gt (Real.cosh_pos _)
  change (2 * Real.sin (φ : ℝ) ^ (2 : ℕ) * c) *
      ((y * (C τ)⁻¹ - c * (C τ)⁻¹ ^ (2 : ℕ)) /
        (1 - c * y * (C τ)⁻¹) ^ (2 : ℕ)) =
    akhmedievLocalizationCorrection φ ξ τ
  rw [akhmedievLocalizationCorrection, akhmedievDenominator]
  change (2 * Real.sin (φ : ℝ) ^ (2 : ℕ) * c) *
      ((y * (C τ)⁻¹ - c * (C τ)⁻¹ ^ (2 : ℕ)) /
        (1 - c * y * (C τ)⁻¹) ^ (2 : ℕ)) =
    2 * Real.sin (φ : ℝ) ^ (2 : ℕ) * c * (C τ * y - c) / (C τ - c * y) ^ (2 : ℕ)
  field_simp [hCne]

theorem tendsto_norm_akhmedievBreather_sq_atTop
    (φ : BreatherAngle) (ξ : ℝ) :
    Tendsto (fun τ => ‖akhmedievBreather φ ξ τ‖ ^ (2 : ℕ)) atTop (nhds (1 / 2)) := by
  have h : Tendsto (fun τ => (1 / 2 : ℝ) + akhmedievLocalizationCorrection φ ξ τ)
      atTop (nhds (1 / 2)) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_akhmedievLocalizationCorrection_atTop φ ξ) :
        Tendsto (fun τ => (1 / 2 : ℝ) + akhmedievLocalizationCorrection φ ξ τ)
          atTop (nhds ((1 / 2 : ℝ) + 0)))
  apply h.congr'
  filter_upwards with τ
  rw [norm_akhmedievBreather_sq_eq_background_add]

/-- Akhmediev magnitude approaches the plane-wave background as `τ→+∞`. -/
theorem tendsto_norm_akhmedievBreather_atTop
    (φ : BreatherAngle) (ξ : ℝ) :
    Tendsto (fun τ => ‖akhmedievBreather φ ξ τ‖) atTop
      (nhds ((Real.sqrt 2)⁻¹)) := by
  have h := (tendsto_norm_akhmedievBreather_sq_atTop φ ξ).sqrt
  have htarget : Real.sqrt (1 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.sqrt_inv]
  rw [htarget] at h
  apply h.congr'
  filter_upwards with τ
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- Time-reflection symmetry gives the same background at `τ→-∞`. -/
theorem tendsto_norm_akhmedievBreather_atBot
    (φ : BreatherAngle) (ξ : ℝ) :
    Tendsto (fun τ => ‖akhmedievBreather φ ξ τ‖) atBot
      (nhds ((Real.sqrt 2)⁻¹)) := by
  have h := (tendsto_norm_akhmedievBreather_atTop φ ξ).comp tendsto_neg_atBot_atTop
  apply h.congr'
  filter_upwards with τ
  exact norm_akhmedievBreather_time_neg φ ξ τ

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
