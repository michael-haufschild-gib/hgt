import GaloisForLFunctions.HTGeometry.KleinGordonTunedSubbandOps

/-!
# The tuned generator and velocity on a sub-band

The generator of a tuned potential is multiplication by `c²` on every band inside its own, so the
velocity of the tuned clock keeps its plane-rotation form there. Both rates of a switching pair are
therefore described by the same formulas on the band they share.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section SubbandVelocity

variable {b c R : ℝ}

set_option maxHeartbeats 1000000 in
/-- **On a sub-band the tuned generator is multiplication by `c²`.** -/
theorem kgShiftedFreqSqLowOp_kgTunedPot_subband (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (hR : R ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b))
    (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedFreqSqLowOp (measurable_kgTunedPot (E := E) b c).neg hb0 hb1
        (abs_neg_pot_le (abs_kgTunedPot_le hb0 hc1 hcb)) R (kgLowPassOp R x)
      = ((c ^ (2 : ℕ) : ℝ) : ℂ) • kgLowPassOp R x := by
  have hc2 : (0 : ℝ) ≤ c ^ (2 : ℕ) := sq_nonneg c
  have hprod : Measurable fun ξ : E =>
      kgShiftedFreqSqLow (fun ζ : E => -(kgTunedPot b c ζ)) R ξ * kgLowPass R ξ :=
    (measurable_kgShiftedFreqSqLow (measurable_kgTunedPot b c).neg R).mul
      (measurable_kgLowPass R)
  have hprodb : ∀ ξ : E, ‖kgShiftedFreqSqLow (fun ζ : E => -(kgTunedPot b c ζ)) R ξ
      * kgLowPass R ξ‖ ≤ c ^ (2 : ℕ) := by
    intro ξ
    rw [kgShiftedFreqSqLow_kgTunedPot_subband hc0 hR ξ, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc2]
    calc c ^ (2 : ℕ) * ‖kgLowPass R ξ‖ ≤ c ^ (2 : ℕ) * 1 :=
          mul_le_mul_of_nonneg_left (norm_kgLowPass_le R ξ) hc2
      _ = c ^ (2 : ℕ) := mul_one _
  have hconst : Measurable fun ξ : E => ((c ^ (2 : ℕ) : ℝ) : ℂ) * kgLowPass R ξ :=
    measurable_const.mul (measurable_kgLowPass R)
  have hconstb : ∀ ξ : E, ‖((c ^ (2 : ℕ) : ℝ) : ℂ) * kgLowPass R ξ‖ ≤ c ^ (2 : ℕ) := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc2]
    calc c ^ (2 : ℕ) * ‖kgLowPass R ξ‖ ≤ c ^ (2 : ℕ) * 1 :=
          mul_le_mul_of_nonneg_left (norm_kgLowPass_le R ξ) hc2
      _ = c ^ (2 : ℕ) := mul_one _
  have hcomp : (kgShiftedFreqSqLowOp (E := E) (measurable_kgTunedPot (E := E) b c).neg hb0 hb1
        (abs_neg_pot_le (abs_kgTunedPot_le hb0 hc1 hcb)) R).comp (kgLowPassOp R)
      = fourierMulCLM hprod hc2 hprodb := by
    rw [kgShiftedFreqSqLowOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ hc2 hprodb (Eventually.of_forall fun _ => rfl)
  have heq : fourierMulCLM hprod hc2 hprodb = fourierMulCLM hconst hc2 hconstb :=
    fourierMulCLM_congr _ _ _ _ _ _
      (Eventually.of_forall (kgShiftedFreqSqLow_kgTunedPot_subband (b := b) hc0 hR))
  have hsmul : fourierMulCLM hconst hc2 hconstb
      = ((c ^ (2 : ℕ) : ℝ) : ℂ) • kgLowPassOp (E := E) R := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ hconst zero_le_one (norm_kgLowPass_le R) hc2 hconstb _
      (Eventually.of_forall fun _ => rfl)
  rw [← ContinuousLinearMap.comp_apply, hcomp, heq, hsmul, smul_apply]

set_option maxHeartbeats 1000000 in
/-- **The velocity of the tuned clock on a sub-band.** -/
theorem kgShiftedVel_kgTunedPot_subband (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (hR : R ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b))
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgShiftedVel (measurable_kgTunedPot (E := E) b c) hb0 hb1
        (abs_kgTunedPot_le hb0 hc1 hcb) R x y t
      = -(((c * Real.sin (t * c) : ℝ) : ℂ) • kgLowPassOp R x)
        + ((Real.cos (t * c) : ℝ) : ℂ) • kgLowPassOp R y := by
  have hscal : ((Real.sin (t * c) / c : ℝ) : ℂ) * ((c ^ (2 : ℕ) : ℝ) : ℂ)
      = ((c * Real.sin (t * c) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [kgShiftedVel, kgShiftedSinFreqOp_kgTunedPot_subband hc0 hc1 hR,
    kgShiftedCosOp_kgTunedPot_subband hc0 hR, map_smul,
    kgShiftedFreqSqLowOp_kgTunedPot_subband hb0 hb1 hc0 hc1 hcb hR, smul_smul, hscal]

end SubbandVelocity

end GaloisForLFunctions.HTGeometry
