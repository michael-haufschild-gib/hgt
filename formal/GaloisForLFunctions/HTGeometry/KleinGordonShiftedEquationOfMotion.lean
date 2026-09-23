import GaloisForLFunctions.HTGeometry.KleinGordonShiftedGenerator

/-!
# The second equation of motion

The cosine addition formula, read through the bounded sine symbol, becomes an operator identity on a
band:

`C(t+s)P = C(t)C(s)P − G·S(t)S(s)P`,   `G = Ω²χ_R`.

Subtracting `C(t)P` and the linear term turns the increment into the same two band defects as before,
both quadratic, so the shifted cosine propagator is differentiable below a fixed frequency and

`d/dt cos(tΩ) = −Ω²·(sin(tΩ)/Ω)`.

With statement 554 this is the full system of equations of motion of a frequency-diagonal background,
in the bounded form the mild theory uses.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section EquationOfMotion

variable {v : E → ℝ} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The group law of the shifted cosine propagator, in bounded form on a band.** -/
theorem kgShiftedCosOp_lowPass_add (hv : Measurable v) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (t s R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedCosOp hv (t + s) (kgLowPassOp R x)
      = kgShiftedCosOp hv t (kgShiftedCosOp hv s (kgLowPassOp R x))
        - kgShiftedFreqSqLowOp hv hb0 hb1 hvb R
            (kgShiftedSinFreqOp hv t (kgShiftedSinFreqOp hv s (kgLowPassOp R x))) := by
  have hband := band_bound_nonneg (b := b) hb0 R
  -- the intermediate symbols
  have hcs : Measurable fun ξ : E => kgShiftedCos v s ξ * kgLowPass R ξ :=
    (measurable_kgShiftedCos hv s).mul (measurable_kgLowPass R)
  have hcsb : ∀ ξ : E, ‖kgShiftedCos v s ξ * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    exact mul_le_one₀ (norm_kgShiftedCos_le v s ξ) (norm_nonneg _) (norm_kgLowPass_le R ξ)
  have hccs : Measurable fun ξ : E =>
      kgShiftedCos v t ξ * (kgShiftedCos v s ξ * kgLowPass R ξ) :=
    (measurable_kgShiftedCos hv t).mul hcs
  have hccsb : ∀ ξ : E,
      ‖kgShiftedCos v t ξ * (kgShiftedCos v s ξ * kgLowPass R ξ)‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    exact mul_le_one₀ (norm_kgShiftedCos_le v t ξ) (norm_nonneg _) (hcsb ξ)
  have hss : Measurable fun ξ : E => kgShiftedSinOverFreq v s ξ * kgLowPass R ξ :=
    (measurable_kgShiftedSinOverFreq hv s).mul (measurable_kgLowPass R)
  have hssb : ∀ ξ : E, ‖kgShiftedSinOverFreq v s ξ * kgLowPass R ξ‖ ≤ |s| := by
    intro ξ
    rw [norm_mul]
    calc ‖kgShiftedSinOverFreq v s ξ‖ * ‖kgLowPass R ξ‖
        ≤ |s| * 1 := mul_le_mul (norm_kgShiftedSinOverFreq_le v s ξ) (norm_kgLowPass_le R ξ)
          (norm_nonneg _) (abs_nonneg s)
      _ = |s| := mul_one _
  have htss : Measurable fun ξ : E =>
      kgShiftedSinOverFreq v t ξ * (kgShiftedSinOverFreq v s ξ * kgLowPass R ξ) :=
    (measurable_kgShiftedSinOverFreq hv t).mul hss
  have htssb : ∀ ξ : E,
      ‖kgShiftedSinOverFreq v t ξ * (kgShiftedSinOverFreq v s ξ * kgLowPass R ξ)‖
        ≤ |t| * |s| := by
    intro ξ
    rw [norm_mul]
    exact mul_le_mul (norm_kgShiftedSinOverFreq_le v t ξ) (hssb ξ) (norm_nonneg _) (abs_nonneg t)
  have hgss : Measurable fun ξ : E => kgShiftedFreqSqLow v R ξ
      * (kgShiftedSinOverFreq v t ξ * (kgShiftedSinOverFreq v s ξ * kgLowPass R ξ)) :=
    (measurable_kgShiftedFreqSqLow hv R).mul htss
  have hgssb0 : (0 : ℝ) ≤ (1 + R ^ (2 : ℕ) + b) * (|t| * |s|) :=
    mul_nonneg hband (mul_nonneg (abs_nonneg t) (abs_nonneg s))
  have hgssb : ∀ ξ : E, ‖kgShiftedFreqSqLow v R ξ
      * (kgShiftedSinOverFreq v t ξ * (kgShiftedSinOverFreq v s ξ * kgLowPass R ξ))‖
        ≤ (1 + R ^ (2 : ℕ) + b) * (|t| * |s|) := by
    intro ξ
    rw [norm_mul]
    exact mul_le_mul (norm_kgShiftedFreqSqLow_le hb0 hb1 hvb R ξ) (htssb ξ) (norm_nonneg _) hband
  have hlhs : Measurable fun ξ : E => kgShiftedCos v (t + s) ξ * kgLowPass R ξ :=
    (measurable_kgShiftedCos hv (t + s)).mul (measurable_kgLowPass R)
  have hlhsb : ∀ ξ : E, ‖kgShiftedCos v (t + s) ξ * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    exact mul_le_one₀ (norm_kgShiftedCos_le v (t + s) ξ) (norm_nonneg _) (norm_kgLowPass_le R ξ)
  -- identify the compositions
  have e0 : (kgShiftedCosOp (E := E) hv (t + s)).comp (kgLowPassOp R)
      = fourierMulCLM hlhs zero_le_one hlhsb := by
    rw [kgShiftedCosOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hlhs _ _ _ _ zero_le_one hlhsb
      (Eventually.of_forall fun _ => rfl)
  have e1 : (kgShiftedCosOp (E := E) hv s).comp (kgLowPassOp R)
      = fourierMulCLM hcs zero_le_one hcsb := by
    rw [kgShiftedCosOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hcs _ _ _ _ zero_le_one hcsb
      (Eventually.of_forall fun _ => rfl)
  have e2 : (kgShiftedCosOp (E := E) hv t).comp (fourierMulCLM hcs zero_le_one hcsb)
      = fourierMulCLM hccs zero_le_one hccsb := by
    rw [kgShiftedCosOp]
    exact fourierMulCLM_comp _ _ hccs _ _ _ _ zero_le_one hccsb
      (Eventually.of_forall fun _ => rfl)
  have e3 : (kgShiftedSinFreqOp (E := E) hv s).comp (kgLowPassOp R)
      = fourierMulCLM hss (abs_nonneg s) hssb := by
    rw [kgShiftedSinFreqOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hss _ _ _ _ (abs_nonneg s) hssb
      (Eventually.of_forall fun _ => rfl)
  have e4 : (kgShiftedSinFreqOp (E := E) hv t).comp (fourierMulCLM hss (abs_nonneg s) hssb)
      = fourierMulCLM htss (mul_nonneg (abs_nonneg t) (abs_nonneg s)) htssb := by
    rw [kgShiftedSinFreqOp]
    exact fourierMulCLM_comp _ _ htss _ _ _ _ (mul_nonneg (abs_nonneg t) (abs_nonneg s)) htssb
      (Eventually.of_forall fun _ => rfl)
  have e5 : (kgShiftedFreqSqLowOp (E := E) hv hb0 hb1 hvb R).comp
        (fourierMulCLM htss (mul_nonneg (abs_nonneg t) (abs_nonneg s)) htssb)
      = fourierMulCLM hgss hgssb0 hgssb := by
    rw [kgShiftedFreqSqLowOp]
    exact fourierMulCLM_comp _ _ hgss _ _ _ _ hgssb0 hgssb
      (Eventually.of_forall fun _ => rfl)
  have hsub : fourierMulCLM hlhs zero_le_one hlhsb
      = fourierMulCLM hccs zero_le_one hccsb - fourierMulCLM hgss hgssb0 hgssb :=
    fourierMulCLM_sub hccs hgss hlhs zero_le_one hccsb hgssb0 hgssb zero_le_one hlhsb
      (Eventually.of_forall (kgShiftedCos_add_lowPass hb1 hvb t s R))
  have hval : kgShiftedCosOp (E := E) hv (t + s) (kgLowPassOp R x)
      = fourierMulCLM hlhs zero_le_one hlhsb x := by
    rw [← ContinuousLinearMap.comp_apply, e0]
  have hinner1 : kgShiftedCosOp (E := E) hv s (kgLowPassOp R x)
      = fourierMulCLM hcs zero_le_one hcsb x := by
    rw [← ContinuousLinearMap.comp_apply, e1]
  have hval1 : kgShiftedCosOp (E := E) hv t (kgShiftedCosOp hv s (kgLowPassOp R x))
      = fourierMulCLM hccs zero_le_one hccsb x := by
    rw [hinner1, ← ContinuousLinearMap.comp_apply, e2]
  have hinner3 : kgShiftedSinFreqOp (E := E) hv s (kgLowPassOp R x)
      = fourierMulCLM hss (abs_nonneg s) hssb x := by
    rw [← ContinuousLinearMap.comp_apply, e3]
  have hinner4 : kgShiftedSinFreqOp (E := E) hv t (fourierMulCLM hss (abs_nonneg s) hssb x)
      = fourierMulCLM htss (mul_nonneg (abs_nonneg t) (abs_nonneg s)) htssb x := by
    rw [← ContinuousLinearMap.comp_apply, e4]
  have hval2 : kgShiftedFreqSqLowOp (E := E) hv hb0 hb1 hvb R
        (kgShiftedSinFreqOp hv t (kgShiftedSinFreqOp hv s (kgLowPassOp R x)))
      = fourierMulCLM hgss hgssb0 hgssb x := by
    rw [hinner3, hinner4, ← ContinuousLinearMap.comp_apply, e5]
  rw [hval, hval1, hval2, hsub, sub_apply]

set_option maxHeartbeats 1000000 in
/-- **The second equation of motion**: the shifted cosine propagator differentiates to minus the
generator applied to the shifted sine propagator, below a fixed frequency. -/
theorem hasDerivAt_kgShiftedCosOp_lowPass (hv : Measurable v) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => kgShiftedCosOp hv s (kgLowPassOp R x))
      (-(kgShiftedFreqSqLowOp hv hb0 hb1 hvb R
        (kgShiftedSinFreqOp hv t (kgLowPassOp R x)))) t := by
  have hband := band_bound_nonneg (b := b) hb0 R
  have hK0 : (0 : ℝ) ≤ ((1 + R ^ (2 : ℕ) + b) / 2
      + (1 + R ^ (2 : ℕ) + b) * |t| * (1 + R ^ (2 : ℕ) + b) / 6) * ‖x‖ := by
    have h1 : (0 : ℝ) ≤ (1 + R ^ (2 : ℕ) + b) / 2 := div_nonneg hband (by norm_num)
    have h2 : (0 : ℝ) ≤ (1 + R ^ (2 : ℕ) + b) * |t| * (1 + R ^ (2 : ℕ) + b) / 6 :=
      div_nonneg (mul_nonneg (mul_nonneg hband (abs_nonneg t)) hband) (by norm_num)
    exact mul_nonneg (by linarith) (norm_nonneg x)
  set K : ℝ := ((1 + R ^ (2 : ℕ) + b) / 2
    + (1 + R ^ (2 : ℕ) + b) * |t| * (1 + R ^ (2 : ℕ) + b) / 6) * ‖x‖ with hKdef
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min 1 (c / (K + 1)), lt_min zero_lt_one (div_pos hc (by linarith)), fun s hs => ?_⟩
  have hd0 : (0 : ℝ) ≤ |s - t| := abs_nonneg _
  have hdist : |s - t| < min 1 (c / (K + 1)) := by rwa [Real.dist_eq] at hs
  have hd1 : |s - t| ≤ 1 := le_of_lt (lt_of_lt_of_le hdist (min_le_left _ _))
  have hdc : |s - t| < c / (K + 1) := lt_of_lt_of_le hdist (min_le_right _ _)
  have hgroup := kgShiftedCosOp_lowPass_add hv hb0 hb1 hvb t (s - t) R x
  have hst : t + (s - t) = s := by ring
  rw [hst] at hgroup
  have hkey : kgShiftedCosOp hv s (kgLowPassOp R x) - kgShiftedCosOp hv t (kgLowPassOp R x)
        - (s - t) • (-(kgShiftedFreqSqLowOp hv hb0 hb1 hvb R
          (kgShiftedSinFreqOp hv t (kgLowPassOp R x))))
      = kgShiftedCosOp hv t (kgShiftedCosOp hv (s - t) (kgLowPassOp R x) - kgLowPassOp R x)
        - kgShiftedFreqSqLowOp hv hb0 hb1 hvb R (kgShiftedSinFreqOp hv t
            (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
              - ((s - t : ℝ) : ℂ) • kgLowPassOp R x)) := by
    have hcomm : kgShiftedFreqSqLowOp hv hb0 hb1 hvb R
          (kgShiftedSinFreqOp hv t (((s - t : ℝ) : ℂ) • kgLowPassOp R x))
        = ((s - t : ℝ) : ℂ) • kgShiftedFreqSqLowOp hv hb0 hb1 hvb R
            (kgShiftedSinFreqOp hv t (kgLowPassOp R x)) := by
      rw [map_smul, map_smul]
    rw [hgroup]
    simp only [map_sub]
    rw [hcomm, Complex.coe_smul, smul_neg, sub_neg_eq_add]
    abel
  have hcos := norm_kgShiftedCosOp_lowPass_sub_le hv hb0 hb1 hvb (s - t) R x
  have hsin := norm_kgShiftedSinFreqOp_lowPass_sub_le hv hb0 hb1 hvb (s - t) R x
  have hA : ‖kgShiftedCosOp hv t
      (kgShiftedCosOp hv (s - t) (kgLowPassOp R x) - kgLowPassOp R x)‖
      ≤ 1 * ‖kgShiftedCosOp hv (s - t) (kgLowPassOp R x) - kgLowPassOp R x‖ :=
    ContinuousLinearMap.le_of_opNorm_le _ (norm_kgShiftedCosOp_le hv t) _
  have hB1 : ‖kgShiftedSinFreqOp hv t (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
        - ((s - t : ℝ) : ℂ) • kgLowPassOp R x)‖
      ≤ |t| * ‖kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
          - ((s - t : ℝ) : ℂ) • kgLowPassOp R x‖ :=
    ContinuousLinearMap.le_of_opNorm_le _ (norm_kgShiftedSinFreqOp_le hv t) _
  have hB2 : ‖kgShiftedFreqSqLowOp hv hb0 hb1 hvb R (kgShiftedSinFreqOp hv t
        (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
          - ((s - t : ℝ) : ℂ) • kgLowPassOp R x))‖
      ≤ (1 + R ^ (2 : ℕ) + b) * ‖kgShiftedSinFreqOp hv t
          (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
            - ((s - t : ℝ) : ℂ) • kgLowPassOp R x)‖ :=
    ContinuousLinearMap.le_of_opNorm_le _ (norm_kgShiftedFreqSqLowOp_le hv hb0 hb1 hvb R) _
  have hsq : (s - t) ^ (2 : ℕ) = |s - t| ^ (2 : ℕ) := (sq_abs _).symm
  have hcube : |s - t| ^ (3 : ℕ) ≤ |s - t| ^ (2 : ℕ) :=
    pow_le_pow_of_le_one hd0 hd1 (by norm_num : (2 : ℕ) ≤ 3)
  have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have htotal : ‖kgShiftedCosOp hv s (kgLowPassOp R x) - kgShiftedCosOp hv t (kgLowPassOp R x)
        - (s - t) • (-(kgShiftedFreqSqLowOp hv hb0 hb1 hvb R
          (kgShiftedSinFreqOp hv t (kgLowPassOp R x))))‖
      ≤ |s - t| ^ (2 : ℕ) * K := by
    rw [hkey]
    refine le_trans (norm_sub_le _ _) ?_
    have hAle : ‖kgShiftedCosOp hv t
        (kgShiftedCosOp hv (s - t) (kgLowPassOp R x) - kgLowPassOp R x)‖
        ≤ (s - t) ^ (2 : ℕ) * (1 + R ^ (2 : ℕ) + b) / 2 * ‖x‖ := by
      have := hA
      linarith
    have hBle : ‖kgShiftedFreqSqLowOp hv hb0 hb1 hvb R (kgShiftedSinFreqOp hv t
          (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
            - ((s - t : ℝ) : ℂ) • kgLowPassOp R x))‖
        ≤ (1 + R ^ (2 : ℕ) + b) * |t| * (|s - t| ^ (3 : ℕ) * (1 + R ^ (2 : ℕ) + b) / 6 * ‖x‖) := by
      have hstep1 : |t| * ‖kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
            - ((s - t : ℝ) : ℂ) • kgLowPassOp R x‖
          ≤ |t| * (|s - t| ^ (3 : ℕ) * (1 + R ^ (2 : ℕ) + b) / 6 * ‖x‖) :=
        mul_le_mul_of_nonneg_left hsin (abs_nonneg t)
      have hstep2 := le_trans hB1 hstep1
      have hstep3 := mul_le_mul_of_nonneg_left hstep2 hband
      calc ‖kgShiftedFreqSqLowOp hv hb0 hb1 hvb R (kgShiftedSinFreqOp hv t
              (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
                - ((s - t : ℝ) : ℂ) • kgLowPassOp R x))‖
          ≤ (1 + R ^ (2 : ℕ) + b) * ‖kgShiftedSinFreqOp hv t
              (kgShiftedSinFreqOp hv (s - t) (kgLowPassOp R x)
                - ((s - t : ℝ) : ℂ) • kgLowPassOp R x)‖ := hB2
        _ ≤ (1 + R ^ (2 : ℕ) + b) * (|t| * (|s - t| ^ (3 : ℕ) * (1 + R ^ (2 : ℕ) + b) / 6 * ‖x‖)) := hstep3
        _ = (1 + R ^ (2 : ℕ) + b) * |t| * (|s - t| ^ (3 : ℕ) * (1 + R ^ (2 : ℕ) + b) / 6 * ‖x‖) := by ring
    rw [hsq] at hAle
    have hcubed : (1 + R ^ (2 : ℕ) + b) * |t| * (|s - t| ^ (3 : ℕ) * (1 + R ^ (2 : ℕ) + b) / 6 * ‖x‖)
        ≤ (1 + R ^ (2 : ℕ) + b) * |t| * (|s - t| ^ (2 : ℕ) * (1 + R ^ (2 : ℕ) + b) / 6 * ‖x‖) := by
      have hmul : |s - t| ^ (3 : ℕ) * (1 + R ^ (2 : ℕ) + b) ≤ |s - t| ^ (2 : ℕ) * (1 + R ^ (2 : ℕ) + b) :=
        mul_le_mul_of_nonneg_right hcube hband
      have hdiv : |s - t| ^ (3 : ℕ) * (1 + R ^ (2 : ℕ) + b) / 6 * ‖x‖
          ≤ |s - t| ^ (2 : ℕ) * (1 + R ^ (2 : ℕ) + b) / 6 * ‖x‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hx0
      exact mul_le_mul_of_nonneg_left hdiv
        (mul_nonneg hband (abs_nonneg t))
    rw [hKdef]
    nlinarith [hAle, hBle, hcubed]
  refine le_trans htotal ?_
  rw [Real.norm_eq_abs]
  have hfin : |s - t| * K < c := by
    have h1 : |s - t| * K ≤ |s - t| * (K + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hd0
    have hpos : (0 : ℝ) < K + 1 := by linarith
    have h2 : |s - t| * (K + 1) < c := by
      calc |s - t| * (K + 1) < (c / (K + 1)) * (K + 1) := mul_lt_mul_of_pos_right hdc hpos
        _ = c := div_mul_cancel₀ _ hpos.ne'
    linarith
  nlinarith [hd0, hK0]

end EquationOfMotion

end GaloisForLFunctions.HTGeometry
