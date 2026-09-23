import GaloisForLFunctions.HTGeometry.KleinGordonTunedClock

/-!
# The tuned clock and its period

On the band of the tuned potential the shifted propagator is multiplication by the scalars `cos(ct)`
and `sin(ct)/c`, so the clock is the plane rotation at rate `c`:

`u(t) = cos(ct)Px + (sin(ct)/c)Py`,

exactly periodic with period `2π/c`, and returning to its initial state there. As `c` ranges over
`[1, √(1+b)]` this realises every period in `[2π/√(1+b), 2π]`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TunedPeriod

variable {b c : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem one_le_of_one_le_sq (hc0 : 0 < c) (hc1 : 1 ≤ c ^ (2 : ℕ)) : (1 : ℝ) ≤ c := by
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **On the tuned band the shifted cosine propagator is the scalar `cos(ct)`.** -/
theorem kgShiftedCosOp_kgTunedPot (hc0 : 0 < c) (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedCosOp (measurable_kgTunedPot (E := E) b c).neg t
        (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
      = ((Real.cos (t * c) : ℝ) : ℂ) • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x := by
  have hprod : Measurable fun ξ : E =>
      kgShiftedCos (fun ζ : E => -(kgTunedPot b c ζ)) t ξ
        * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ :=
    (measurable_kgShiftedCos (measurable_kgTunedPot b c).neg t).mul
      (measurable_kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
  have hprodb : ∀ ξ : E, ‖kgShiftedCos (fun ζ : E => -(kgTunedPot b c ζ)) t ξ
      * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    exact mul_le_one₀ (norm_kgShiftedCos_le _ t ξ) (norm_nonneg _)
      (norm_kgLowPass_le (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ)
  have hconst : Measurable fun ξ : E =>
      ((Real.cos (t * c) : ℝ) : ℂ) * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ :=
    measurable_const.mul (measurable_kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
  have hconstb : ∀ ξ : E, ‖((Real.cos (t * c) : ℝ) : ℂ)
      * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_one₀ (Real.abs_cos_le_one _) (norm_nonneg _)
      (norm_kgLowPass_le (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ)
  have hcomp : (kgShiftedCosOp (E := E) (measurable_kgTunedPot (E := E) b c).neg t).comp
      (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b))) = fourierMulCLM hprod zero_le_one hprodb := by
    rw [kgShiftedCosOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ zero_le_one hprodb
      (Eventually.of_forall fun _ => rfl)
  have heq : fourierMulCLM hprod zero_le_one hprodb = fourierMulCLM hconst zero_le_one hconstb :=
    fourierMulCLM_congr _ _ _ _ _ _
      (Eventually.of_forall (kgShiftedCos_kgTunedPot_lowPass (b := b) hc0 t))
  have hsmul : fourierMulCLM hconst zero_le_one hconstb
      = ((Real.cos (t * c) : ℝ) : ℂ) • kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ hconst zero_le_one
      (norm_kgLowPass_le (Real.sqrt (c ^ (2 : ℕ) - 1 + b))) zero_le_one hconstb _
      (Eventually.of_forall fun _ => rfl)
  rw [← ContinuousLinearMap.comp_apply, hcomp, heq, hsmul, smul_apply]

set_option maxHeartbeats 1000000 in
/-- **On the tuned band the shifted sine propagator is the scalar `sin(ct)/c`.** -/
theorem kgShiftedSinFreqOp_kgTunedPot (hc0 : 0 < c) (hc1 : 1 ≤ c ^ (2 : ℕ)) (t : ℝ)
    (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedSinFreqOp (measurable_kgTunedPot (E := E) b c).neg t
        (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
      = ((Real.sin (t * c) / c : ℝ) : ℂ) • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x := by
  have hcge := one_le_of_one_le_sq hc0 hc1
  have hprod : Measurable fun ξ : E =>
      kgShiftedSinOverFreq (fun ζ : E => -(kgTunedPot b c ζ)) t ξ
        * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ :=
    (measurable_kgShiftedSinOverFreq (measurable_kgTunedPot b c).neg t).mul
      (measurable_kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
  have hprodb : ∀ ξ : E, ‖kgShiftedSinOverFreq (fun ζ : E => -(kgTunedPot b c ζ)) t ξ
      * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ‖ ≤ |t| := by
    intro ξ
    rw [norm_mul]
    calc ‖kgShiftedSinOverFreq (fun ζ : E => -(kgTunedPot b c ζ)) t ξ‖
          * ‖kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ‖
        ≤ |t| * 1 := mul_le_mul (norm_kgShiftedSinOverFreq_le _ t ξ)
          (norm_kgLowPass_le (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ) (norm_nonneg _) (abs_nonneg t)
      _ = |t| := mul_one _
  have hconst : Measurable fun ξ : E =>
      ((Real.sin (t * c) / c : ℝ) : ℂ) * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ :=
    measurable_const.mul (measurable_kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
  have hconstb : ∀ ξ : E, ‖((Real.sin (t * c) / c : ℝ) : ℂ)
      * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hq : |Real.sin (t * c) / c| ≤ 1 := by
      rw [abs_div, abs_of_pos hc0, div_le_one hc0]
      exact le_trans (Real.abs_sin_le_one _) hcge
    exact mul_le_one₀ hq (norm_nonneg _) (norm_kgLowPass_le (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ)
  have hcomp : (kgShiftedSinFreqOp (E := E) (measurable_kgTunedPot (E := E) b c).neg t).comp
      (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b))) = fourierMulCLM hprod (abs_nonneg t) hprodb := by
    rw [kgShiftedSinFreqOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ (abs_nonneg t) hprodb
      (Eventually.of_forall fun _ => rfl)
  have heq : fourierMulCLM hprod (abs_nonneg t) hprodb
      = fourierMulCLM hconst zero_le_one hconstb :=
    fourierMulCLM_congr _ _ _ _ _ _
      (Eventually.of_forall (kgShiftedSinOverFreq_kgTunedPot_lowPass (b := b) hc0 t))
  have hsmul : fourierMulCLM hconst zero_le_one hconstb
      = ((Real.sin (t * c) / c : ℝ) : ℂ)
        • kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ hconst zero_le_one
      (norm_kgLowPass_le (Real.sqrt (c ^ (2 : ℕ) - 1 + b))) zero_le_one hconstb _
      (Eventually.of_forall fun _ => rfl)
  rw [← ContinuousLinearMap.comp_apply, hcomp, heq, hsmul, smul_apply]

set_option maxHeartbeats 1000000 in
/-- **The tuned clock is the plane rotation at rate `c`.** -/
theorem kgShiftedField_kgTunedPot (hc0 : 0 < c) (hc1 : 1 ≤ c ^ (2 : ℕ))
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgShiftedField (measurable_kgTunedPot (E := E) b c) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x y t
      = ((Real.cos (t * c) : ℝ) : ℂ) • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x
        + ((Real.sin (t * c) / c : ℝ) : ℂ) • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) y := by
  rw [kgShiftedField, kgShiftedCosOp_kgTunedPot hc0, kgShiftedSinFreqOp_kgTunedPot hc0 hc1]

set_option maxHeartbeats 1000000 in
/-- **The tuned clock has exact period `2π/c`.** -/
theorem kgShiftedField_kgTunedPot_periodic (hc0 : 0 < c) (hc1 : 1 ≤ c ^ (2 : ℕ))
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgShiftedField (measurable_kgTunedPot (E := E) b c) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x y
        (t + 2 * Real.pi / c)
      = kgShiftedField (measurable_kgTunedPot (E := E) b c) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x y t := by
  have harg : (t + 2 * Real.pi / c) * c = t * c + 2 * Real.pi := by
    field_simp
  rw [kgShiftedField_kgTunedPot hc0 hc1, kgShiftedField_kgTunedPot hc0 hc1, harg,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

set_option maxHeartbeats 1000000 in
/-- **The tuned clock returns to its initial state after one period.** -/
theorem kgShiftedField_kgTunedPot_period (hc0 : 0 < c) (hc1 : 1 ≤ c ^ (2 : ℕ))
    (x y : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedField (measurable_kgTunedPot (E := E) b c) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x y
        (2 * Real.pi / c)
      = kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x := by
  have harg : 2 * Real.pi / c * c = 2 * Real.pi := by
    field_simp
  rw [kgShiftedField_kgTunedPot hc0 hc1, harg, Real.cos_two_pi, Real.sin_two_pi]
  simp

end TunedPeriod

end GaloisForLFunctions.HTGeometry
