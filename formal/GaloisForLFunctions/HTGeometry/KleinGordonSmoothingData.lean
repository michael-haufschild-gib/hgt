import GaloisForLFunctions.HTGeometry.KleinGordonSmoothingWellPosed

/-!
# The estimates in terms of the prescribed data

The energy of the constructed strong solution at time zero is an explicit expression in the Cauchy
data, so the Grönwall estimate reads as a bound by the data alone. The construction is linear in the
data, so the same bound applied to a difference is continuous dependence.

Nothing here is new analysis; it is the last step of making the card's three theorems usable, by
stating them with the data one prescribes rather than with the solution one obtains.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-! ## The initial energy -/

theorem kgStrongEnergy_kgSmoothMild_zero (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) :
    kgStrongEnergy (kgSmoothMild W₀ g₀ h₀) (kgSmoothVel W₀ g₀ h₀) 0
      = ‖kgFreqInvOp (kgFreqInvOp (E := E) h₀)‖ ^ (2 : ℕ)
        + ‖kgFreqInvOp (kgFreqInvOp (E := E) g₀)‖ ^ (2 : ℕ) := by
  rw [kgStrongEnergy, kgSmoothVel_at_zero, kgSmoothMild_at_zero hb0 hW]

/-- **The energy estimate in terms of the data.** -/
theorem kgStrongEnergy_kgSmoothMild_le_data (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgStrongEnergy (kgSmoothMild W₀ g₀ h₀) (kgSmoothVel W₀ g₀ h₀) t
      ≤ (‖kgFreqInvOp (kgFreqInvOp (E := E) h₀)‖ ^ (2 : ℕ)
          + ‖kgFreqInvOp (kgFreqInvOp (E := E) g₀)‖ ^ (2 : ℕ)) * Real.exp (b * |t|) := by
  have h := kgStrongEnergy_kgSmoothMild_le hb0 hW g₀ h₀ t
  rwa [kgStrongEnergy_kgSmoothMild_zero hb0 hW] at h

/-! ## Linearity in the data, and continuous dependence -/

/-- **The construction is linear in the Cauchy data.** -/
theorem kgSmoothMild_sub (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgSmoothMild W₀ g₁ h₁ t - kgSmoothMild W₀ g₂ h₂ t
      = kgSmoothMild W₀ (g₁ - g₂) (h₁ - h₂) t := by
  rw [kgSmoothMild, kgSmoothMild, kgSmoothMild,
    kgFieldMild_sub hb0 (norm_kgSmoothingOp_le hW)]
  simp only [← map_sub]

/-- **Continuous dependence on the Cauchy data**, for the constructed strong solution. -/
theorem norm_kgSmoothMild_sub_le (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgSmoothMild W₀ g₁ h₁ t - kgSmoothMild W₀ g₂ h₂ t‖
      ≤ (‖kgFreqInvOp (kgFreqInvOp (E := E) (g₁ - g₂))‖
          + ‖kgFreqInvOp (E := E) (h₁ - h₂)‖) * Real.exp (b * |t|) := by
  rw [kgSmoothMild_sub hb0 hW, kgSmoothMild]
  exact norm_kgFieldMild_le hb0 (norm_kgSmoothingOp_le hW) _ _ t

/-- **The solution itself is bounded by its data.** -/
theorem norm_kgSmoothMild_le (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgSmoothMild W₀ g₀ h₀ t‖
      ≤ (‖kgFreqInvOp (kgFreqInvOp (E := E) g₀)‖ + ‖kgFreqInvOp (E := E) h₀‖)
        * Real.exp (b * |t|) := by
  rw [kgSmoothMild]
  exact norm_kgFieldMild_le hb0 (norm_kgSmoothingOp_le hW) _ _ t

end GaloisForLFunctions.HTGeometry
