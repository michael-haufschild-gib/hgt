import GaloisForLFunctions.HTGeometry.KleinGordonShiftedBandDefect

/-!
# The shifted propagator is differentiable on a band

The group law turns the increment of the shifted sine propagator into two defects,

`S(s) − S(t) − (s−t)C(t) = S(t)(C(s−t) − 1) + C(t)(S(s−t) − (s−t))`,

and below a fixed frequency both defects are quadratic in the increment. So the shifted sine
propagator has a derivative there, and that derivative is the shifted cosine propagator:

`d/dt (sin(tΩ)/Ω) = cos(tΩ)`.

This is the first of the two equations of motion of a frequency-diagonal background, and the one that
carries no unbounded factor.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section ShiftedDerivative

variable {v : E → ℝ} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The shifted sine propagator differentiates to the shifted cosine propagator**, below a fixed
frequency. -/
theorem hasDerivAt_kgShiftedSinFreqOp_lowPass (hv : Measurable v) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => kgShiftedSinFreqOp hv s (kgLowPassOp R x))
      (kgShiftedCosOp hv t (kgLowPassOp R x)) t := by
  have hband := band_bound_nonneg (b := b) hb0 R
  have hK0 : (0 : ℝ) ≤ (|t| * (1 + R ^ 2 + b) / 2 + (1 + R ^ 2 + b) / 6) * ‖x‖ := by
    have h1 : (0 : ℝ) ≤ |t| * (1 + R ^ 2 + b) / 2 :=
      div_nonneg (mul_nonneg (abs_nonneg t) hband) (by norm_num)
    have h2 : (0 : ℝ) ≤ (1 + R ^ 2 + b) / 6 := div_nonneg hband (by norm_num)
    exact mul_nonneg (by linarith) (norm_nonneg x)
  set K : ℝ := (|t| * (1 + R ^ 2 + b) / 2 + (1 + R ^ 2 + b) / 6) * ‖x‖ with hKdef
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min 1 (c / (K + 1)), lt_min zero_lt_one (div_pos hc (by linarith)), fun s hs => ?_⟩
  have hd0 : (0 : ℝ) ≤ |s - t| := abs_nonneg _
  have hdist : |s - t| < min 1 (c / (K + 1)) := by
    rwa [Real.dist_eq] at hs
  have hd1 : |s - t| ≤ 1 := le_of_lt (lt_of_lt_of_le hdist (min_le_left _ _))
  have hdc : |s - t| < c / (K + 1) := lt_of_lt_of_le hdist (min_le_right _ _)
  -- the group law turns the increment into two defects
  have hgroup := kgShiftedSinFreqOp_add hv t (s - t)
  have hst : t + (s - t) = s := by ring
  rw [hst] at hgroup
  have happ : kgShiftedSinFreqOp hv s (kgLowPassOp R x)
      = kgShiftedSinFreqOp hv t (kgShiftedCosOp hv (s - t) (kgLowPassOp R x))
        + kgShiftedCosOp hv t (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)) := by
    rw [hgroup]
    rfl
  have hkey : kgShiftedSinFreqOp hv s (kgLowPassOp R x)
        - kgShiftedSinFreqOp hv t (kgLowPassOp R x)
        - (s - t) • kgShiftedCosOp hv t (kgLowPassOp R x)
      = kgShiftedSinFreqOp hv t
          (kgShiftedCosOp hv (s - t) (kgLowPassOp R x) - kgLowPassOp R x)
        + kgShiftedCosOp hv t (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
            - ((s - t : ℝ) : ℂ) • kgLowPassOp R x) := by
    rw [happ, map_sub, map_sub, map_smul, Complex.coe_smul]
    abel
  -- the two defects are quadratic in the increment
  have hcos := norm_kgShiftedCosOp_lowPass_sub_le hv hb0 hb1 hvb (s - t) R x
  have hsin := norm_kgShiftedSinFreqOp_lowPass_sub_le hv hb0 hb1 hvb (s - t) R x
  have hA : ‖kgShiftedSinFreqOp hv t
      (kgShiftedCosOp hv (s - t) (kgLowPassOp R x) - kgLowPassOp R x)‖
      ≤ |t| * ‖kgShiftedCosOp hv (s - t) (kgLowPassOp R x) - kgLowPassOp R x‖ :=
    ContinuousLinearMap.le_of_opNorm_le _ (norm_kgShiftedSinFreqOp_le hv t) _
  have hB : ‖kgShiftedCosOp hv t (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
        - ((s - t : ℝ) : ℂ) • kgLowPassOp R x)‖
      ≤ 1 * ‖kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
          - ((s - t : ℝ) : ℂ) • kgLowPassOp R x‖ :=
    ContinuousLinearMap.le_of_opNorm_le _ (norm_kgShiftedCosOp_le hv t) _
  have hsq : (s - t) ^ 2 = |s - t| ^ 2 := (sq_abs _).symm
  have hcube : |s - t| ^ 3 ≤ |s - t| ^ 2 :=
    pow_le_pow_of_le_one hd0 hd1 (by norm_num : (2 : ℕ) ≤ 3)
  have htotal : ‖kgShiftedSinFreqOp hv s (kgLowPassOp R x)
        - kgShiftedSinFreqOp hv t (kgLowPassOp R x)
        - (s - t) • kgShiftedCosOp hv t (kgLowPassOp R x)‖
      ≤ |s - t| ^ 2 * K := by
    rw [hkey]
    refine le_trans (norm_add_le _ _) ?_
    have hAB : ‖kgShiftedSinFreqOp hv t
          (kgShiftedCosOp hv (s - t) (kgLowPassOp R x) - kgLowPassOp R x)‖
        + ‖kgShiftedCosOp hv t (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
            - ((s - t : ℝ) : ℂ) • kgLowPassOp R x)‖
        ≤ |t| * ((s - t) ^ 2 * (1 + R ^ 2 + b) / 2 * ‖x‖)
          + 1 * (|s - t| ^ 3 * (1 + R ^ 2 + b) / 6 * ‖x‖) := by
      have h1 : |t| * ‖kgShiftedCosOp hv (s - t) (kgLowPassOp R x) - kgLowPassOp R x‖
          ≤ |t| * ((s - t) ^ 2 * (1 + R ^ 2 + b) / 2 * ‖x‖) :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg t)
      have h2 : 1 * ‖kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
            - ((s - t : ℝ) : ℂ) • kgLowPassOp R x‖
          ≤ 1 * (|s - t| ^ 3 * (1 + R ^ 2 + b) / 6 * ‖x‖) :=
        mul_le_mul_of_nonneg_left hsin zero_le_one
      linarith
    refine le_trans hAB ?_
    rw [hsq, hKdef]
    have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hstep : |s - t| ^ 3 * (1 + R ^ 2 + b) / 6 * ‖x‖
        ≤ |s - t| ^ 2 * (1 + R ^ 2 + b) / 6 * ‖x‖ := by
      have hmul : |s - t| ^ 3 * (1 + R ^ 2 + b) ≤ |s - t| ^ 2 * (1 + R ^ 2 + b) :=
        mul_le_mul_of_nonneg_right hcube hband
      have hdiv : |s - t| ^ 3 * (1 + R ^ 2 + b) / 6
          ≤ |s - t| ^ 2 * (1 + R ^ 2 + b) / 6 := by linarith
      exact mul_le_mul_of_nonneg_right hdiv hx0
    nlinarith [hx0, hstep]
  refine le_trans htotal ?_
  have hnorm : ‖s - t‖ = |s - t| := Real.norm_eq_abs _
  rw [hnorm]
  have hfin : |s - t| * K < c := by
    have hKle : K ≤ K + 1 := by linarith
    have h1 : |s - t| * K ≤ |s - t| * (K + 1) := mul_le_mul_of_nonneg_left hKle hd0
    have h2 : |s - t| * (K + 1) < c := by
      have hpos : (0 : ℝ) < K + 1 := by linarith
      calc |s - t| * (K + 1) < (c / (K + 1)) * (K + 1) :=
            mul_lt_mul_of_pos_right hdc hpos
        _ = c := div_mul_cancel₀ _ hpos.ne'
    linarith
  nlinarith [hd0, hK0]

end ShiftedDerivative

end GaloisForLFunctions.HTGeometry
