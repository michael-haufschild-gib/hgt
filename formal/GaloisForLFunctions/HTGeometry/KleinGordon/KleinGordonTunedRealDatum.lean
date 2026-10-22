import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTunedExactNorm

/-!
# A real datum: the energy genuinely oscillates

Started from a datum with vanishing velocity the tuned clock has

`⟨D⟩u(t) = cos(ct)·⟨D⟩_R x`,   `u̇(t) = −(c sin(ct))·P_R x`,

so its energy is

`E(t) = cos²(ct)·‖⟨D⟩_R x‖² + c² sin²(ct)·‖P_R x‖²`,

an exact expression that oscillates between the two terms. The complex eigen-datum conserves the
energy exactly; a real datum does not — it exchanges energy between the gradient and the velocity, and
the size of the swing is the spread between `‖⟨D⟩_R x‖` and `c‖P_R x‖`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section RealDatum

variable {b c : ℝ}

/-- **The gradient of the tuned clock started from a real datum.** -/
theorem kgFieldGradT_kgTunedPot_real (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
          (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
        (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t
      = ((Real.cos (t * c) : ℝ) : ℂ) • kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x := by
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
      (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) r‖ ≤ b :=
    fun _ => norm_fourierMulCLM_le _ _ _
  have hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) r z := fun _ => continuous_const
  have hBandb := norm_kgBandOpT_le hb0 hWb (Real.sqrt (c ^ (2 : ℕ) - 1 + b))
  have hBands := continuous_kgBandOpT_apply hWs (Real.sqrt (c ^ (2 : ℕ) - 1 + b))
  have hzero : kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) 0 = 0 := map_zero _
  have hmild := kgFieldMildT_eq_kgShiftedField (measurable_kgTunedPot (E := E) b c) hb0 hb1
    (abs_kgTunedPot_le hb0 hc1 hcb) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x 0 t
  rw [kgShiftedField_kgTunedPot hc0 hc1, hzero, smul_zero, add_zero] at hmild
  have hgradinv := kgFreqInvOp_kgFieldGradT hb0 hBandb hBands
    (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) 0) t
  rw [hzero] at hgradinv
  refine kgFreqInvOp_injective ?_
  rw [hgradinv, hmild, map_smul, kgFreqInvOp_kgFreqLowOp]

/-- **The velocity of the tuned clock started from a real datum.** -/
theorem kgFieldVelT_kgTunedPot_real (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
          (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
        (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t
      = -(((c * Real.sin (t * c) : ℝ) : ℂ)
        • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) := by
  have hzero : kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) 0 = 0 := map_zero _
  have hvel := kgFieldVelT_eq_kgShiftedVel (measurable_kgTunedPot (E := E) b c) hb0 hb1
    (abs_kgTunedPot_le hb0 hc1 hcb) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x 0 t
  rw [kgShiftedVel_kgTunedPot hb0 hb1 hc0 hc1 hcb, hzero, smul_zero, add_zero] at hvel
  exact hvel

/-- **The exact energy of the tuned clock started from a real datum.** -/
theorem kgFieldEnergyT_kgTunedPot_real (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ)
      = Real.cos (t * c) ^ (2 : ℕ) * ‖kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
        + (c * Real.sin (t * c)) ^ (2 : ℕ) * ‖kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) := by
  rw [kgFieldGradT_kgTunedPot_real hb0 hb1 hc0 hc1 hcb x t,
    kgFieldVelT_kgTunedPot_real hb0 hb1 hc0 hc1 hcb x t, norm_neg, norm_smul, norm_smul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
    sq_abs, sq_abs]

end RealDatum

end GaloisForLFunctions.HTGeometry
