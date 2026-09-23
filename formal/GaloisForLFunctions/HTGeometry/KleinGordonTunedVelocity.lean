import GaloisForLFunctions.HTGeometry.KleinGordonTunedClockPeriod

/-!
# The velocity of the tuned clock

On the band of the tuned potential the generator is multiplication by `c²`, so the velocity of the
plane rotation is the expected one:

`u̇(t) = −(c sin(ct))Px + cos(ct)Py`.

Field and velocity together are the rotation of the pair `(Px, Py)` at rate `c`, with the sine entries
carrying the factors `1/c` and `c` that the second-order equation prescribes.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TunedVelocity

variable {b c : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- On the tuned band the generator symbol is `c²` times the band symbol. -/
theorem kgShiftedFreqSqLow_kgTunedPot_lowPass (hc0 : 0 < c) (ξ : E) :
    kgShiftedFreqSqLow (fun ζ : E => -(kgTunedPot b c ζ)) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ
        * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ
      = ((c ^ (2 : ℕ) : ℝ) : ℂ) * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ := by
  rw [kgShiftedFreqSqLow, kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, mul_one, mul_one, kgShiftedFreq_kgTunedPot hc0 hξ]
  · simp

set_option maxHeartbeats 1000000 in
/-- **On the tuned band the generator is multiplication by `c²`.** -/
theorem kgShiftedFreqSqLowOp_kgTunedPot (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedFreqSqLowOp (measurable_kgTunedPot (E := E) b c).neg hb0 hb1
        (abs_neg_pot_le (abs_kgTunedPot_le hb0 hc1 hcb)) (Real.sqrt (c ^ (2 : ℕ) - 1 + b))
        (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
      = ((c ^ (2 : ℕ) : ℝ) : ℂ) • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x := by
  have hband := band_bound_nonneg (b := b) hb0 (Real.sqrt (c ^ (2 : ℕ) - 1 + b))
  have hc2 : (0 : ℝ) ≤ c ^ (2 : ℕ) := sq_nonneg c
  have hprod : Measurable fun ξ : E =>
      kgShiftedFreqSqLow (fun ζ : E => -(kgTunedPot b c ζ)) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ
        * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ :=
    (measurable_kgShiftedFreqSqLow (measurable_kgTunedPot b c).neg
      (Real.sqrt (c ^ (2 : ℕ) - 1 + b))).mul (measurable_kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
  have hprodb : ∀ ξ : E, ‖kgShiftedFreqSqLow (fun ζ : E => -(kgTunedPot b c ζ))
      (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ‖ ≤ c ^ (2 : ℕ) := by
    intro ξ
    rw [kgShiftedFreqSqLow_kgTunedPot_lowPass hc0 ξ, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc2]
    calc c ^ (2 : ℕ) * ‖kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ‖
        ≤ c ^ (2 : ℕ) * 1 := mul_le_mul_of_nonneg_left
          (norm_kgLowPass_le (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ) hc2
      _ = c ^ (2 : ℕ) := mul_one _
  have hconst : Measurable fun ξ : E =>
      ((c ^ (2 : ℕ) : ℝ) : ℂ) * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ :=
    measurable_const.mul (measurable_kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
  have hconstb : ∀ ξ : E, ‖((c ^ (2 : ℕ) : ℝ) : ℂ)
      * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ‖ ≤ c ^ (2 : ℕ) := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc2]
    calc c ^ (2 : ℕ) * ‖kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ‖
        ≤ c ^ (2 : ℕ) * 1 := mul_le_mul_of_nonneg_left
          (norm_kgLowPass_le (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ) hc2
      _ = c ^ (2 : ℕ) := mul_one _
  have hcomp : (kgShiftedFreqSqLowOp (E := E) (measurable_kgTunedPot (E := E) b c).neg hb0 hb1
        (abs_neg_pot_le (abs_kgTunedPot_le hb0 hc1 hcb)) (Real.sqrt (c ^ (2 : ℕ) - 1 + b))).comp
        (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
      = fourierMulCLM hprod hc2 hprodb := by
    rw [kgShiftedFreqSqLowOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ hc2 hprodb (Eventually.of_forall fun _ => rfl)
  have heq : fourierMulCLM hprod hc2 hprodb = fourierMulCLM hconst hc2 hconstb :=
    fourierMulCLM_congr _ _ _ _ _ _
      (Eventually.of_forall (kgShiftedFreqSqLow_kgTunedPot_lowPass (b := b) hc0))
  have hsmul : fourierMulCLM hconst hc2 hconstb
      = ((c ^ (2 : ℕ) : ℝ) : ℂ) • kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ hconst zero_le_one
      (norm_kgLowPass_le (Real.sqrt (c ^ (2 : ℕ) - 1 + b))) hc2 hconstb _
      (Eventually.of_forall fun _ => rfl)
  rw [← ContinuousLinearMap.comp_apply, hcomp, heq, hsmul, smul_apply]

set_option maxHeartbeats 1000000 in
/-- **The velocity of the tuned clock.** -/
theorem kgShiftedVel_kgTunedPot (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c) (hc1 : 1 ≤ c ^ (2 : ℕ))
    (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgShiftedVel (measurable_kgTunedPot (E := E) b c) hb0 hb1
        (abs_kgTunedPot_le hb0 hc1 hcb) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x y t
      = -(((c * Real.sin (t * c) : ℝ) : ℂ) • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
        + ((Real.cos (t * c) : ℝ) : ℂ) • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) y := by
  have hscal : ((Real.sin (t * c) / c : ℝ) : ℂ) * ((c ^ (2 : ℕ) : ℝ) : ℂ)
      = ((c * Real.sin (t * c) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [kgShiftedVel, kgShiftedSinFreqOp_kgTunedPot hc0 hc1, kgShiftedCosOp_kgTunedPot hc0,
    map_smul, kgShiftedFreqSqLowOp_kgTunedPot hb0 hb1 hc0 hc1 hcb, smul_smul, hscal]

end TunedVelocity

end GaloisForLFunctions.HTGeometry
