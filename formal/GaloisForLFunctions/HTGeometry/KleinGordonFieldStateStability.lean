import GaloisForLFunctions.HTGeometry.KleinGordonFieldVelocityBound

/-!
# Stability of the whole state

The evolution family propagates the pair `(u(t), ∂ₜu(t))`. Statement 88 makes the position depend
continuously on the data; this file does the same for the velocity, and states the two together.

The argument is that the construction is linear in the data, so the difference of two solutions is
the solution of the difference — and then the difference of the two velocities is the velocity of
that solution, by uniqueness of derivatives. The bound of statement 128 applied to it is the
stability estimate.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Stability

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The velocity is linear in the Cauchy data.** -/
theorem deriv_kgFieldMild_sub (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    deriv (kgFieldMild W (kgFreqInvOp g₁) h₁) t
        - deriv (kgFieldMild W (kgFreqInvOp g₂) h₂) t
      = deriv (kgFieldMild W (kgFreqInvOp (g₁ - g₂)) (h₁ - h₂)) t := by
  have hfun : ∀ τ : ℝ, kgFieldMild W (kgFreqInvOp (g₁ - g₂)) (h₁ - h₂) τ
      = kgFieldMild W (kgFreqInvOp g₁) h₁ τ - kgFieldMild W (kgFreqInvOp g₂) h₂ τ := by
    intro τ
    rw [kgFieldMild_sub hb0 hW, map_sub]
  have hd1 := hasDerivAt_kgFieldMild hb0 hW g₁ h₁ t
  have hd2 := hasDerivAt_kgFieldMild hb0 hW g₂ h₂ t
  have hdiff := hd1.sub hd2
  have hdd := hasDerivAt_kgFieldMild hb0 hW (g₁ - g₂) (h₁ - h₂) t
  have hdd' : HasDerivAt
      (fun τ : ℝ => kgFieldMild W (kgFreqInvOp g₁) h₁ τ
        - kgFieldMild W (kgFreqInvOp g₂) h₂ τ)
      (-(kgSinOp t (g₁ - g₂)) + kgCosOp t (h₁ - h₂)
        + ∫ s in (0 : ℝ)..t, kgCosOp (t - s)
            (W (kgFieldMild W (kgFreqInvOp (g₁ - g₂)) (h₁ - h₂) s))) t := by
    refine hdd.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun τ => (hfun τ).symm
  rw [hd1.deriv, hd2.deriv, hdd.deriv]
  exact hdiff.unique hdd'

/-- **Continuous dependence of the velocity on the Cauchy data.** -/
theorem norm_deriv_kgFieldMild_sub_le (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖deriv (kgFieldMild W (kgFreqInvOp g₁) h₁) t
        - deriv (kgFieldMild W (kgFreqInvOp g₂) h₂) t‖
      ≤ (‖g₁ - g₂‖ + ‖h₁ - h₂‖) * Real.exp (2 * (b * |t|)) := by
  rw [deriv_kgFieldMild_sub hb0 hW]
  exact norm_deriv_kgFieldMild_le hb0 hW (g₁ - g₂) (h₁ - h₂) t

/-- **Continuous dependence of the field on the Cauchy data**, in the raw data. -/
theorem norm_kgFieldMild_sub_le_data (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild W (kgFreqInvOp g₁) h₁ t - kgFieldMild W (kgFreqInvOp g₂) h₂ t‖
      ≤ (‖g₁ - g₂‖ + ‖h₁ - h₂‖) * Real.exp (b * |t|) := by
  rw [kgFieldMild_sub hb0 hW, ← map_sub]
  exact norm_kgFieldMild_le_data hb0 hW (g₁ - g₂) (h₁ - h₂) t

/-- **Stability of the whole propagated state.** Both components of `(u(t), ∂ₜu(t))` depend
continuously on the Cauchy data, exponentially in the time at a rate set by the perturbation. -/
theorem kgFieldMild_state_stability (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild W (kgFreqInvOp g₁) h₁ t - kgFieldMild W (kgFreqInvOp g₂) h₂ t‖
        ≤ (‖g₁ - g₂‖ + ‖h₁ - h₂‖) * Real.exp (2 * (b * |t|))
      ∧ ‖deriv (kgFieldMild W (kgFreqInvOp g₁) h₁) t
          - deriv (kgFieldMild W (kgFreqInvOp g₂) h₂) t‖
        ≤ (‖g₁ - g₂‖ + ‖h₁ - h₂‖) * Real.exp (2 * (b * |t|)) := by
  refine ⟨?_, norm_deriv_kgFieldMild_sub_le hb0 hW g₁ h₁ g₂ h₂ t⟩
  refine le_trans (norm_kgFieldMild_sub_le_data hb0 hW g₁ h₁ g₂ h₂ t) ?_
  have hD0 : (0 : ℝ) ≤ ‖g₁ - g₂‖ + ‖h₁ - h₂‖ := by positivity
  have hx : (0 : ℝ) ≤ b * |t| := by positivity
  have hmono : Real.exp (b * |t|) ≤ Real.exp (2 * (b * |t|)) :=
    Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_left hmono hD0

end Stability

end GaloisForLFunctions.HTGeometry
