import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTunedBandData

/-!
# Switching the rate: geometric growth

On a band shared by two tuned potentials the evolution over a quarter period is, in field coordinates,

`(w, h) ↦ ((1/c)·h, −c·w)`.

Composing the quarter period of rate `c₁` with the quarter period of rate `c₂` therefore gives

`(w, h) ↦ (−(c₁/c₂)·w, −(c₂/c₁)·h)`,

so the velocity is multiplied by `c₂/c₁` on every cycle. A static real diagonal potential can never
make a clock grow — all its multipliers lie on the unit circle — but switching between two admissible
rates does, at the geometric rate `c₂/c₁`, and both rates are available for any `1 ≤ cᵢ² ≤ 1 + b`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Switched

variable {b c R : ℝ}

/-- The field of the tuned clock in field coordinates. -/
theorem kgFieldMildT_kgTunedPot_field (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (hR : R ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b))
    {w h : Lp ℂ 2 (volume : Measure E)} (hw : kgLowPassOp R w = w)
    (hh : kgLowPassOp R h = h) (t : ℝ) :
    kgFieldMildT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) R) w h t
      = ((Real.cos (t * c) : ℝ) : ℂ) • w + ((Real.sin (t * c) / c : ℝ) : ℂ) • h := by
  have hginv : kgFreqInvOp (kgFreqLowOp R w) = w := by
    rw [kgFreqInvOp_kgFreqLowOp, hw]
  have hgb : kgLowPassOp R (kgFreqLowOp R w) = kgFreqLowOp R w := kgLowPassOp_kgFreqLowOp R w
  have hmain := kgFieldMildT_kgTunedPot_band hb0 hb1 hc0 hc1 hcb hR hgb hh t
  rw [hginv] at hmain
  exact hmain

/-- The velocity of the tuned clock in field coordinates. -/
theorem kgFieldVelT_kgTunedPot_field (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (hR : R ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b))
    {w h : Lp ℂ 2 (volume : Measure E)} (hw : kgLowPassOp R w = w)
    (hh : kgLowPassOp R h = h) (t : ℝ) :
    kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) R)
        (kgFreqLowOp R w) h t
      = -(((c * Real.sin (t * c) : ℝ) : ℂ) • w) + ((Real.cos (t * c) : ℝ) : ℂ) • h := by
  have hginv : kgFreqInvOp (kgFreqLowOp R w) = w := by
    rw [kgFreqInvOp_kgFreqLowOp, hw]
  have hgb : kgLowPassOp R (kgFreqLowOp R w) = kgFreqLowOp R w := kgLowPassOp_kgFreqLowOp R w
  have hmain := kgFieldVelT_kgTunedPot_band hb0 hb1 hc0 hc1 hcb hR hgb hh t
  rw [hginv] at hmain
  exact hmain

/-- **A quarter period exchanges field and velocity**, with the rate as the exchange factor. -/
theorem kgFieldMildT_kgTunedPot_quarter (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (hR : R ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b))
    {w h : Lp ℂ 2 (volume : Measure E)} (hw : kgLowPassOp R w = w)
    (hh : kgLowPassOp R h = h) :
    kgFieldMildT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) R) w h
        (Real.pi / (2 * c))
      = (((1 / c : ℝ)) : ℂ) • h := by
  have harg : Real.pi / (2 * c) * c = Real.pi / 2 := by
    field_simp
  rw [kgFieldMildT_kgTunedPot_field hb0 hb1 hc0 hc1 hcb hR hw hh, harg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem kgFieldVelT_kgTunedPot_quarter (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (hR : R ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b))
    {w h : Lp ℂ 2 (volume : Measure E)} (hw : kgLowPassOp R w = w)
    (hh : kgLowPassOp R h = h) :
    kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) R)
        (kgFreqLowOp R w) h (Real.pi / (2 * c))
      = -(((c : ℝ) : ℂ) • w) := by
  have harg : Real.pi / (2 * c) * c = Real.pi / 2 := by
    field_simp
  rw [kgFieldVelT_kgTunedPot_field hb0 hb1 hc0 hc1 hcb hR hw hh, harg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

end Switched

section Composition

variable {b c₁ c₂ R : ℝ}

/-- **One switching cycle**: a quarter period at rate `c₁` exchanges field and velocity, and a
quarter period at rate `c₂` returns them contracted by `c₁/c₂` and dilated by `c₂/c₁`. -/
theorem kgSwitchedClock_step (hb0 : 0 ≤ b) (hb1 : b < 1) (hc10 : 0 < c₁) (hc11 : 1 ≤ c₁ ^ (2 : ℕ))
    (hc1b : c₁ ^ (2 : ℕ) ≤ 1 + b) (hR1 : R ≤ Real.sqrt (c₁ ^ (2 : ℕ) - 1 + b))
    (hc20 : 0 < c₂) (hc21 : 1 ≤ c₂ ^ (2 : ℕ)) (hc2b : c₂ ^ (2 : ℕ) ≤ 1 + b)
    (hR2 : R ≤ Real.sqrt (c₂ ^ (2 : ℕ) - 1 + b))
    {w h : Lp ℂ 2 (volume : Measure E)} (hw : kgLowPassOp R w = w)
    (hh : kgLowPassOp R h = h) :
    kgFieldMildT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c₁)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc11 hc1b))) R) w h
        (Real.pi / (2 * c₁)) = ((1 / c₁ : ℝ) : ℂ) • h
      ∧ kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c₁)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc11 hc1b))) R)
        (kgFreqLowOp R w) h (Real.pi / (2 * c₁)) = -(((c₁ : ℝ) : ℂ) • w)
      ∧ kgFieldMildT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c₂)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc21 hc2b))) R)
        (((1 / c₁ : ℝ) : ℂ) • h) (-(((c₁ : ℝ) : ℂ) • w)) (Real.pi / (2 * c₂))
        = -(((c₁ / c₂ : ℝ) : ℂ) • w)
      ∧ kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c₂)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc21 hc2b))) R)
        (kgFreqLowOp R (((1 / c₁ : ℝ) : ℂ) • h)) (-(((c₁ : ℝ) : ℂ) • w))
        (Real.pi / (2 * c₂))
        = -(((c₂ / c₁ : ℝ) : ℂ) • h) := by
  have hw1 : kgLowPassOp R (((1 / c₁ : ℝ) : ℂ) • h) = ((1 / c₁ : ℝ) : ℂ) • h := by
    rw [map_smul, hh]
  have hh1 : kgLowPassOp R (-(((c₁ : ℝ) : ℂ) • w)) = -(((c₁ : ℝ) : ℂ) • w) := by
    rw [map_neg, map_smul, hw]
  refine ⟨kgFieldMildT_kgTunedPot_quarter hb0 hb1 hc10 hc11 hc1b hR1 hw hh,
    kgFieldVelT_kgTunedPot_quarter hb0 hb1 hc10 hc11 hc1b hR1 hw hh, ?_, ?_⟩
  · rw [kgFieldMildT_kgTunedPot_quarter hb0 hb1 hc20 hc21 hc2b hR2 hw1 hh1, smul_neg,
      smul_smul, ← Complex.ofReal_mul]
    congr 2
    field_simp
  · rw [kgFieldVelT_kgTunedPot_quarter hb0 hb1 hc20 hc21 hc2b hR2 hw1 hh1, smul_smul,
      ← Complex.ofReal_mul]
    congr 2
    field_simp

/-- **The switched clock grows geometrically**: after one cycle the velocity has been multiplied by
`c₂/c₁`. -/
theorem norm_kgSwitchedClock_vel (hc10 : 0 < c₁) (hc20 : 0 < c₂)
    (h : Lp ℂ 2 (volume : Measure E)) :
    ‖-(((c₂ / c₁ : ℝ) : ℂ) • h)‖ = c₂ / c₁ * ‖h‖ := by
  rw [norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos hc20 hc10)]

end Composition

end GaloisForLFunctions.HTGeometry
