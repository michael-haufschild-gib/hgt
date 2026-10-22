import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTunedSubbandVelocity

/-!
# The tuned clock from arbitrary band-limited data

Rewriting the closed form in terms of an arbitrary band-limited pair rather than a parametrised one.
Given `P_R g = g` and `P_R h = h`, the tuned clock started from the state `(g, h)` has

`u(t) = cos(ct)·⟨D⟩⁻¹g + (sin(ct)/c)·h`,   `u̇(t) = −(c sin(ct))·⟨D⟩⁻¹g + cos(ct)·h`.

In this form the output of one evolution can be fed into the next, which is what a switch of rate
requires.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandData

variable {b c R : ℝ}

/-- **The field of the tuned clock from band-limited data.** -/
theorem kgFieldMildT_kgTunedPot_band (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (hR : R ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b))
    {g h : Lp ℂ 2 (volume : Measure E)} (hg : kgLowPassOp R g = g)
    (hh : kgLowPassOp R h = h) (t : ℝ) :
    kgFieldMildT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) R)
        (kgFreqInvOp g) h t
      = ((Real.cos (t * c) : ℝ) : ℂ) • kgFreqInvOp g
        + ((Real.sin (t * c) / c : ℝ) : ℂ) • h := by
  have hx : kgFreqLowOp R (kgFreqInvOp g) = g := by
    rw [kgFreqLowOp_kgFreqInvOp, hg]
  have hcomm : kgLowPassOp R (kgFreqInvOp g) = kgFreqInvOp (kgLowPassOp R g) :=
    fourierMulCLM_kgFreqInvOp_comm (measurable_kgLowPass (E := E) R) zero_le_one
      (norm_kgLowPass_le R) g
  have hPx : kgLowPassOp R (kgFreqInvOp g) = kgFreqInvOp g := by
    rw [hcomm, hg]
  have hmild := kgFieldMildT_eq_kgShiftedField (measurable_kgTunedPot (E := E) b c) hb0 hb1
    (abs_kgTunedPot_le hb0 hc1 hcb) R (kgFreqInvOp g) h t
  rw [hx, hh] at hmild
  rw [hmild, kgShiftedField, kgShiftedCosOp_kgTunedPot_subband hc0 hR,
    kgShiftedSinFreqOp_kgTunedPot_subband hc0 hc1 hR, hPx, hh]

/-- **The velocity of the tuned clock from band-limited data.** -/
theorem kgFieldVelT_kgTunedPot_band (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (hR : R ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b))
    {g h : Lp ℂ 2 (volume : Measure E)} (hg : kgLowPassOp R g = g)
    (hh : kgLowPassOp R h = h) (t : ℝ) :
    kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) R) g h t
      = -(((c * Real.sin (t * c) : ℝ) : ℂ) • kgFreqInvOp g)
        + ((Real.cos (t * c) : ℝ) : ℂ) • h := by
  have hx : kgFreqLowOp R (kgFreqInvOp g) = g := by
    rw [kgFreqLowOp_kgFreqInvOp, hg]
  have hcomm : kgLowPassOp R (kgFreqInvOp g) = kgFreqInvOp (kgLowPassOp R g) :=
    fourierMulCLM_kgFreqInvOp_comm (measurable_kgLowPass (E := E) R) zero_le_one
      (norm_kgLowPass_le R) g
  have hPx : kgLowPassOp R (kgFreqInvOp g) = kgFreqInvOp g := by
    rw [hcomm, hg]
  have hvel := kgFieldVelT_eq_kgShiftedVel (measurable_kgTunedPot (E := E) b c) hb0 hb1
    (abs_kgTunedPot_le hb0 hc1 hcb) R (kgFreqInvOp g) h t
  rw [hx, hh] at hvel
  rw [hvel, kgShiftedVel_kgTunedPot_subband hb0 hb1 hc0 hc1 hcb hR, hPx, hh]

end BandData

end GaloisForLFunctions.HTGeometry
