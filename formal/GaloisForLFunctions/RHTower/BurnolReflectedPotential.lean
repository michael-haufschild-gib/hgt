import GaloisForLFunctions.RHTower.BurnolReflectedBoundary

/-!
# The reflected potential and the reflected masses

The potential `Ψ(T) = A^∨(T)/(1-ρ) - T^{1-ρ} Head^∨(T)/(1-ρ)` has right derivative `-C g_ρ` and
vanishes at the origin, so the truncated mass of the reflected divided shift is `-Ψ(T)`.  Both
pieces of `Ψ` converge: the primitive to `-1/2` and the boundary term to zero.  Hence

`∫_0^∞ C g_ρ = 1/(2(1-ρ)) = a_ρ/2`,

and subtracting the constant head on the aperture gives `B_ρ^∨ = -B_ρ`, so the reflected singular
first-wall residue is `b_ρ conj(B_ρ)`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The head moment of the reflected kernel in its right-continuous representative. -/
def burnolReflectedHeadRC (ρ : ℂ) (T : ℝ) : ℂ := ∫ y in (0 : ℝ)..T, burnolReflectedKernelRC ρ y

theorem norm_burnolReflectedKernelRC_le {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖burnolReflectedKernelRC ρ y‖ ≤ (y + 1) * y ^ (ρ.re - 1) := by
  rw [burnolReflectedKernelRC, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (ρ - 1).re = ρ.re - 1 := by rw [Complex.sub_re]; norm_num
  rw [hre]
  have hb := abs_burnolReflectedSourceRC_le hy.le
  have hp : (0 : ℝ) < y ^ (ρ.re - 1) := Real.rpow_pos_of_pos hy _
  nlinarith [hb, hp, abs_nonneg (burnolReflectedSourceRC y)]

theorem intervalIntegrable_burnolReflectedKernelRC_zero {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (burnolReflectedKernelRC ρ) volume 0 T := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hT]
  exact (integrableOn_burnolReflectedKernelRC hρ0 hρ1).mono_set (fun y hy => mem_Ioi.mpr hy.1)

theorem burnolReflectedHeadRC_eq {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {T : ℝ}
    (hT : 0 ≤ T) :
    burnolReflectedHeadRC ρ T = ∫ y in Ioc (0 : ℝ) T, burnolReflectedKernel ρ y := by
  rw [burnolReflectedHeadRC, intervalIntegral.integral_of_le hT]
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  have hmono : volume.restrict (Ioc (0 : ℝ) T) ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono (fun x hx => mem_Ioi.mpr hx.1) le_rfl
  exact (ae_restrict_iff' measurableSet_Ioc).mp
    (((burnolReflectedKernelRC_ae ρ).filter_mono (ae_mono hmono)))

theorem burnolReflectedDividedSource_eq_headRC {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT : 0 ≤ T) :
    burnolReflectedDividedSource ρ T = ((T : ℝ) : ℂ) ^ (-ρ) * burnolReflectedHeadRC ρ T := by
  rw [burnolReflectedDividedSource, burnolReflectedHeadRC_eq hρ0 hρ1 hT]

/-- A uniform head bound. -/
theorem norm_burnolReflectedHeadRC_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {T : ℝ}
    (hT : 0 ≤ T) :
    ‖burnolReflectedHeadRC ρ T‖ ≤ (T + 1) * (T ^ ρ.re / ρ.re) := by
  have hdom : IntervalIntegrable (fun y : ℝ => (T + 1) * y ^ (ρ.re - 1)) volume 0 T :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  have hnorm : ‖burnolReflectedHeadRC ρ T‖ ≤ ∫ y in (0 : ℝ)..T, (T + 1) * y ^ (ρ.re - 1) := by
    rw [burnolReflectedHeadRC]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hT) ?_
    refine intervalIntegral.integral_mono_on hT
      ((intervalIntegrable_burnolReflectedKernelRC_zero hρ0 hρ1 hT).norm) hdom ?_
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h, burnolReflectedKernelRC, Complex.ofReal_zero, Complex.zero_cpow (by
        intro hc
        have : (ρ - 1).re = 0 := by rw [hc]; simp
        rw [Complex.sub_re, Complex.one_re] at this
        linarith), mul_zero, norm_zero]
      have hz : (0 : ℝ) ^ (ρ.re - 1) = 0 := Real.zero_rpow (by linarith)
      rw [hz, mul_zero]
    · refine le_trans (norm_burnolReflectedKernelRC_le h) ?_
      have hp : (0 : ℝ) < y ^ (ρ.re - 1) := Real.rpow_pos_of_pos h _
      nlinarith [hy.2, hp]
  refine le_trans hnorm (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  rw [show ρ.re - 1 + 1 = ρ.re by ring, Real.zero_rpow (by linarith : ρ.re ≠ 0), sub_zero]


/-! ## The potential -/

/-- The reflected potential. -/
def burnolReflectedPotential (ρ : ℂ) (T : ℝ) : ℂ :=
  ((burnolReflectedTruncMass T : ℝ) : ℂ) / (1 - ρ) -
    ((T : ℝ) : ℂ) ^ (1 - ρ) * burnolReflectedHeadRC ρ T / (1 - ρ)

theorem burnolReflectedPotential_zero (ρ : ℂ) : burnolReflectedPotential ρ 0 = 0 := by
  rw [burnolReflectedPotential, burnolReflectedHeadRC, intervalIntegral.integral_same,
    burnolReflectedTruncMass]
  norm_num

theorem continuousWithinAt_burnolReflectedKernelRC {ρ : ℂ} {a : ℝ} (ha : 0 < a) :
    ContinuousWithinAt (burnolReflectedKernelRC ρ) (Ici a) a := by
  refine ContinuousWithinAt.mul ?_ ?_
  · exact Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_burnolReflectedSourceRC ha.le)
  · exact ((hasDerivAt_burnolRealCpow ha (ρ - 1)).continuousAt).continuousWithinAt

theorem hasDerivWithinAt_burnolReflectedHeadRC {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {a : ℝ} (ha : 0 < a) :
    HasDerivWithinAt (burnolReflectedHeadRC ρ) (burnolReflectedKernelRC ρ a) (Ici a) a :=
  intervalIntegral.integral_hasDerivWithinAt_right (s := Ici a) (t := Ioi a)
    (intervalIntegrable_burnolReflectedKernelRC_zero hρ0 hρ1 ha.le)
    ⟨Ioi a, self_mem_nhdsWithin,
      ((integrableOn_burnolReflectedKernelRC hρ0 hρ1).mono_set
        (fun y hy => mem_Ioi.mpr (lt_trans ha hy))).aestronglyMeasurable⟩
    ((continuousWithinAt_burnolReflectedKernelRC ha).mono Ioi_subset_Ici_self)

theorem hasDerivWithinAt_burnolReflectedPotential {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT : 0 < T) :
    HasDerivWithinAt (burnolReflectedPotential ρ)
      (-(burnolReflectedDividedSource ρ T)) (Ici T) T := by
  have hρne : (1 : ℂ) - ρ ≠ 0 := by
    intro hc
    have : (1 - ρ).re = 0 := by rw [hc]; simp
    rw [Complex.sub_re, Complex.one_re] at this
    linarith
  have hTne : ((T : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hA : HasDerivWithinAt (fun x : ℝ => ((burnolReflectedTruncMass x : ℝ) : ℂ) / (1 - ρ))
      (((burnolReflectedSourceRC T : ℝ) : ℂ) / (1 - ρ)) (Ici T) T :=
    ((hasDerivWithinAt_burnolReflectedTruncMass hT.le).ofReal_comp).div_const _
  have hcpow : HasDerivWithinAt (fun x : ℝ => (x : ℂ) ^ (1 - ρ))
      ((1 - ρ) * ((T : ℝ) : ℂ) ^ (1 - ρ - 1)) (Ici T) T :=
    (hasDerivAt_burnolRealCpow hT (1 - ρ)).hasDerivWithinAt
  have hprod := (hcpow.mul (hasDerivWithinAt_burnolReflectedHeadRC hρ0 hρ1 hT)).div_const (1 - ρ)
  have hsub := hA.sub hprod
  refine hsub.congr_deriv ?_
  have hker : ((T : ℝ) : ℂ) ^ (1 - ρ) * burnolReflectedKernelRC ρ T =
      ((burnolReflectedSourceRC T : ℝ) : ℂ) := by
    rw [burnolReflectedKernelRC, ← mul_assoc, mul_comm (((T : ℝ) : ℂ) ^ (1 - ρ)), mul_assoc,
      ← Complex.cpow_add _ _ hTne, show (1 - ρ) + (ρ - 1) = (0 : ℂ) by ring, Complex.cpow_zero,
      mul_one]
  have hexp : ((T : ℝ) : ℂ) ^ (1 - ρ - 1) = ((T : ℝ) : ℂ) ^ (-ρ) := by
    congr 1
    ring
  rw [burnolReflectedDividedSource_eq_headRC hρ0 hρ1 hT.le, hexp, hker]
  field_simp
  ring

theorem continuousOn_burnolReflectedHeadRC {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {T : ℝ}
    (hT : 0 ≤ T) : ContinuousOn (burnolReflectedHeadRC ρ) (Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_burnolReflectedKernelRC_zero hρ0 hρ1 hT)
    (by rw [Set.uIcc_of_le hT]; exact ⟨le_rfl, hT⟩)
  rwa [Set.uIcc_of_le hT] at h

theorem continuousWithinAt_burnolReflectedCpowHead_zero {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (T : ℝ) :
    ContinuousWithinAt (fun y : ℝ => (y : ℂ) ^ (1 - ρ) * burnolReflectedHeadRC ρ y)
      (Icc 0 T) 0 := by
  have hval : (((0 : ℝ) : ℂ)) ^ (1 - ρ) * burnolReflectedHeadRC ρ 0 = 0 := by
    rw [burnolReflectedHeadRC, intervalIntegral.integral_same, mul_zero]
  have hlim : Tendsto (fun y : ℝ => (y : ℂ) ^ (1 - ρ) * burnolReflectedHeadRC ρ y)
      (𝓝[Icc (0 : ℝ) T] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun y : ℝ => (y + 1) * y / ρ.re)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rcases eq_or_lt_of_le hy.1 with h | h
      · rw [← h, burnolReflectedHeadRC, intervalIntegral.integral_same, mul_zero, norm_zero]
        positivity
      · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h]
        have hre : (1 - ρ).re = 1 - ρ.re := by rw [Complex.sub_re, Complex.one_re]
        rw [hre]
        have hhead := norm_burnolReflectedHeadRC_le hρ0 hρ1 hy.1
        have hpos : (0 : ℝ) < y ^ (1 - ρ.re) := Real.rpow_pos_of_pos h _
        have hstep := mul_le_mul_of_nonneg_left hhead hpos.le
        refine le_trans hstep (le_of_eq ?_)
        rw [show y ^ (1 - ρ.re) * ((y + 1) * (y ^ ρ.re / ρ.re)) =
            (y + 1) * (y ^ (1 - ρ.re) * y ^ ρ.re) / ρ.re by ring, ← Real.rpow_add h,
          show 1 - ρ.re + ρ.re = 1 by ring, Real.rpow_one]
    · have hc : Tendsto (fun y : ℝ => (y + 1) * y / ρ.re) (𝓝[Icc 0 T] (0 : ℝ))
          (𝓝 ((0 + 1) * 0 / ρ.re)) :=
        ((((continuous_id.add continuous_const).mul continuous_id).div_const ρ.re).tendsto
          0).mono_left nhdsWithin_le_nhds
      simpa using hc
  show Tendsto (fun y : ℝ => (y : ℂ) ^ (1 - ρ) * burnolReflectedHeadRC ρ y)
    (𝓝[Icc (0 : ℝ) T] 0) (𝓝 ((((0 : ℝ) : ℂ)) ^ (1 - ρ) * burnolReflectedHeadRC ρ 0))
  rw [hval]
  exact hlim

theorem continuousOn_burnolReflectedPotential {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT : 0 ≤ T) : ContinuousOn (burnolReflectedPotential ρ) (Icc 0 T) := by
  refine ContinuousOn.sub ?_ ?_
  · refine ContinuousOn.div_const ?_ _
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.congr
      (f := fun x : ℝ => burnolReflectedShiftedMass x - 1 / 2) ?_ (fun x _ => by
        simp only [burnolReflectedShiftedMass]
        ring)
    exact (continuousOn_burnolReflectedShiftedMass le_rfl hT).sub continuousOn_const
  · refine ContinuousOn.div_const ?_ _
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      exact continuousWithinAt_burnolReflectedCpowHead_zero hρ0 hρ1 T
    · refine ContinuousWithinAt.mul ?_ ?_
      · exact ((hasDerivAt_burnolRealCpow h (1 - ρ)).continuousAt).continuousWithinAt
      · exact continuousOn_burnolReflectedHeadRC hρ0 hρ1 hT x hx


/-! ## The reflected masses -/

theorem xiDivisor_burnolReflectedHeadRC_eq_neg_tail {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {t : ℝ} (ht : 0 < t) :
    burnolReflectedHeadRC ρ t = -∫ y in Ioi t, burnolReflectedKernelRC ρ y := by
  have hRC : (∫ y in Ioi t, burnolReflectedKernel ρ y) =
      ∫ y in Ioi t, burnolReflectedKernelRC ρ y := by
    refine (setIntegral_congr_ae measurableSet_Ioi ?_).symm
    have hmono : volume.restrict (Ioi t) ≤ volume.restrict (Ioi (0 : ℝ)) :=
      Measure.restrict_mono (fun x hx => mem_Ioi.mpr (lt_trans ht hx)) le_rfl
    exact (ae_restrict_iff' measurableSet_Ioi).mp
      (((burnolReflectedKernelRC_ae ρ).filter_mono (ae_mono hmono)))
  rw [burnolReflectedHeadRC_eq hρ0 hρ1 ht.le,
    xiDivisor_integral_burnolReflectedKernel_Ioc hρ0 hρ1 hxi ht, hRC]

theorem norm_burnolReflectedDividedSource_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {t : ℝ}
    (ht : 0 < t) : ‖burnolReflectedDividedSource ρ t‖ ≤ (t + 1) / ρ.re := by
  rw [burnolReflectedDividedSource_eq_headRC hρ0 hρ1 ht.le, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re]
  have hhead := norm_burnolReflectedHeadRC_le hρ0 hρ1 ht.le
  have hpos : (0 : ℝ) < t ^ (-ρ.re) := Real.rpow_pos_of_pos ht _
  have hstep := mul_le_mul_of_nonneg_left hhead hpos.le
  refine le_trans hstep (le_of_eq ?_)
  rw [show t ^ (-ρ.re) * ((t + 1) * (t ^ ρ.re / ρ.re)) =
      (t + 1) * (t ^ (-ρ.re) * t ^ ρ.re) / ρ.re by ring, ← Real.rpow_add ht,
    show -ρ.re + ρ.re = 0 by ring, Real.rpow_zero]
  ring

theorem xiDivisor_norm_burnolReflectedDividedSource_le_sq {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) {t : ℝ} (ht : 2 ≤ t) :
    ‖burnolReflectedDividedSource ρ t‖ ≤
      2 * (1 + ‖ρ - 1‖ / (1 - ρ.re)) * t ^ (-2 : ℝ) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  rw [burnolReflectedDividedSource_eq_headRC hρ0 hρ1 ht0.le,
    xiDivisor_burnolReflectedHeadRC_eq_neg_tail hρ0 hρ1 hxi ht0, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.neg_re]
  have htail := norm_integral_burnolReflectedKernelRC_Ioi_le hρ0 hρ1 ht
  have hpos : (0 : ℝ) < t ^ (-ρ.re) := Real.rpow_pos_of_pos ht0 _
  have hstep := mul_le_mul_of_nonneg_left htail hpos.le
  refine le_trans hstep ?_
  have hprod : t ^ (-ρ.re) * ((1 + ‖ρ - 1‖ / (1 - ρ.re)) * (t ^ (ρ.re - 1) / (t - 1))) =
      (1 + ‖ρ - 1‖ / (1 - ρ.re)) * (t ^ (-(1 : ℝ)) / (t - 1)) := by
    rw [show t ^ (-ρ.re) * ((1 + ‖ρ - 1‖ / (1 - ρ.re)) * (t ^ (ρ.re - 1) / (t - 1))) =
        (1 + ‖ρ - 1‖ / (1 - ρ.re)) * (t ^ (-ρ.re) * t ^ (ρ.re - 1)) / (t - 1) by ring,
      ← Real.rpow_add ht0, show -ρ.re + (ρ.re - 1) = -(1 : ℝ) by ring]
    ring
  rw [hprod]
  have hC : (0 : ℝ) ≤ 1 + ‖ρ - 1‖ / (1 - ρ.re) := by
    have : (0 : ℝ) ≤ ‖ρ - 1‖ / (1 - ρ.re) := by
      apply div_nonneg (norm_nonneg _) (by linarith)
    linarith
  have hkey : t ^ (-(1 : ℝ)) / (t - 1) ≤ 2 * t ^ (-2 : ℝ) := by
    have h1 : t ^ (-(1 : ℝ)) = 1 / t := by
      rw [Real.rpow_neg_one]
      exact (one_div t).symm
    have h2 : t ^ (-2 : ℝ) = 1 / t ^ (2 : ℕ) := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg ht0.le,
        Real.rpow_natCast]
      exact (one_div _).symm
    rw [h1, h2, div_div]
    have hsq : (0 : ℝ) < t ^ (2 : ℕ) := by positivity
    have hden : (0 : ℝ) < t * (t - 1) := by positivity
    rw [div_le_iff₀ hden]
    rw [mul_comm (2 : ℝ), mul_assoc, one_div, inv_mul_eq_div, le_div_iff₀ hsq]
    nlinarith [ht, ht1, hsq, hden]
  nlinarith [hkey, hC, Real.rpow_pos_of_pos ht0 (-2 : ℝ)]

theorem continuousOn_burnolReflectedDividedSource {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT : 0 ≤ T) : ContinuousOn (burnolReflectedDividedSource ρ) (Ioc (0 : ℝ) T) := by
  refine ContinuousOn.congr (f := fun t : ℝ => (t : ℂ) ^ (-ρ) * burnolReflectedHeadRC ρ t) ?_
    (fun t ht => burnolReflectedDividedSource_eq_headRC hρ0 hρ1 ht.1.le)
  refine ContinuousOn.mul ?_ ?_
  · intro t ht
    exact ((hasDerivAt_burnolRealCpow ht.1 (-ρ)).continuousAt).continuousWithinAt
  · exact (continuousOn_burnolReflectedHeadRC hρ0 hρ1 hT).mono
      (fun t ht => ⟨ht.1.le, ht.2⟩)

theorem intervalIntegrable_burnolReflectedDividedSource {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (burnolReflectedDividedSource ρ) volume 0 T := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hT]
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (T + 1) / ρ.re)
    (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) T) measure_Ioc_lt_top.ne)
    ((continuousOn_burnolReflectedDividedSource hρ0 hρ1 hT).aestronglyMeasurable
      measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  refine le_trans (norm_burnolReflectedDividedSource_le hρ0 hρ1 ht.1) ?_
  rw [div_le_div_iff₀ hρ0 hρ0]
  nlinarith [ht.2, hρ0]

/-- **The truncated reflected mass is the potential.** -/
theorem xiDivisor_integral_burnolReflectedDividedSource {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, burnolReflectedDividedSource ρ t) = -burnolReflectedPotential ρ T := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) T, HasDerivWithinAt (burnolReflectedPotential ρ)
      (-(burnolReflectedDividedSource ρ x)) (Ioi x) x := fun x hx =>
    (hasDerivWithinAt_burnolReflectedPotential hρ0 hρ1 hx.1).mono Ioi_subset_Ici_self
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
    (continuousOn_burnolReflectedPotential hρ0 hρ1 hT) hderiv
    ((intervalIntegrable_burnolReflectedDividedSource hρ0 hρ1 hT).neg)
  rw [intervalIntegral.integral_neg, burnolReflectedPotential_zero, sub_zero] at hftc
  linear_combination -hftc


theorem integrableOn_burnolReflectedDividedSource {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) : IntegrableOn (burnolReflectedDividedSource ρ) (Ioi (0 : ℝ)) := by
  have hnear : IntegrableOn (burnolReflectedDividedSource ρ) (Ioc (0 : ℝ) 2) := by
    have h := intervalIntegrable_burnolReflectedDividedSource hρ0 hρ1 (T := (2 : ℝ)) (by norm_num)
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 2)] at h
    exact h
  have hmeasFar : AEStronglyMeasurable (burnolReflectedDividedSource ρ)
      (volume.restrict (Ioi (2 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.congr (f := fun t : ℝ => (t : ℂ) ^ (-ρ) * burnolReflectedHeadRC ρ t) ?_
      (fun t ht => burnolReflectedDividedSource_eq_headRC hρ0 hρ1
        (le_of_lt (lt_trans (by norm_num) ht)))
    refine ContinuousOn.mul ?_ ?_
    · intro t ht
      have hc := (hasDerivAt_burnolRealCpow (lt_trans (by norm_num) ht) (-ρ)).continuousAt
      exact hc.continuousWithinAt
    · intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans (by norm_num) ht
      have hmem : Icc (0 : ℝ) (t + 1) ∈ 𝓝 t := Icc_mem_nhds ht0 (by linarith)
      exact (((continuousOn_burnolReflectedHeadRC hρ0 hρ1
        (by linarith : (0:ℝ) ≤ t + 1)).continuousAt hmem)).continuousWithinAt
  have hfar : IntegrableOn (burnolReflectedDividedSource ρ) (Ioi (2 : ℝ)) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => 2 * (1 + ‖ρ - 1‖ / (1 - ρ.re)) * t ^ (-2 : ℝ))
      (((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num)
        (by norm_num : (0:ℝ) < 2)).const_mul _)) hmeasFar ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact xiDivisor_norm_burnolReflectedDividedSource_le_sq hρ0 hρ1 hxi (le_of_lt ht)
  have hunion : Ioc (0 : ℝ) 2 ∪ Ioi 2 = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hunion]
  exact hnear.union hfar

/-- **The total reflected mass.** -/
theorem xiDivisor_integral_burnolReflectedDividedSource_Ioi {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    (∫ t in Ioi (0 : ℝ), burnolReflectedDividedSource ρ t) = burnolFirstWallHead ρ / 2 := by
  have hρne : (1 : ℂ) - ρ ≠ 0 := by
    intro hc
    have : (1 - ρ).re = 0 := by rw [hc]; simp
    rw [Complex.sub_re, Complex.one_re] at this
    linarith
  have hlim : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, burnolReflectedDividedSource ρ t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), burnolReflectedDividedSource ρ t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_burnolReflectedDividedSource hρ0 hρ1 hxi) tendsto_id
  have hA : Tendsto (fun T : ℝ => ((burnolReflectedTruncMass T : ℝ) : ℂ) / (1 - ρ)) atTop
      (𝓝 (((-(1 : ℝ) / 2 : ℝ) : ℂ) / (1 - ρ))) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp tendsto_burnolReflectedTruncMass
    exact (h.div_const (1 - ρ)).congr fun T => rfl
  have hB : Tendsto
      (fun T : ℝ => ((T : ℝ) : ℂ) ^ (1 - ρ) * burnolReflectedHeadRC ρ T / (1 - ρ)) atTop
      (𝓝 0) := by
    have hb := (tendsto_burnolReflectedBoundary hρ0 hρ1 hxi).div_const (1 - ρ)
    rw [zero_div] at hb
    refine hb.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [burnolReflectedHeadRC_eq hρ0 hρ1 hT.le]
  have hpot := hA.sub hB
  rw [sub_zero] at hpot
  have hneg : Tendsto (fun T : ℝ => -burnolReflectedPotential ρ T) atTop
      (𝓝 (-(((-(1 : ℝ) / 2 : ℝ) : ℂ) / (1 - ρ)))) := by
    refine (hpot.neg).congr fun T => ?_
    rw [burnolReflectedPotential]
  have heq := tendsto_nhds_unique (hlim.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact xiDivisor_integral_burnolReflectedDividedSource hρ0 hρ1 hT)) hneg
  rw [heq, burnolFirstWallHead]
  push_cast
  field_simp

/-- The reflected aperture mass is half the reflected head. -/
theorem xiDivisor_integral_burnolReflectedDividedSource_aperture {ρ : ℂ} (hρ0 : 0 < ρ.re) :
    (∫ t in Ioc (0 : ℝ) (1 / 2), burnolReflectedDividedSource ρ t) =
      burnolFirstWallCosineHead ρ / 2 := by
  have hcongr : (∫ t in Ioc (0 : ℝ) (1 / 2), burnolReflectedDividedSource ρ t) =
      ∫ _t in Ioc (0 : ℝ) (1 / 2), burnolFirstWallCosineHead ρ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    exact burnolReflectedDividedSource_head hρ0 ht.1 ht.2
  rw [hcongr, setIntegral_const]
  have hvol : (volume.real (Ioc (0 : ℝ) (1 / 2))) = 1 / 2 := by
    simp [MeasureTheory.measureReal_def, Real.volume_Ioc]
  rw [hvol, Complex.real_smul]
  push_cast
  ring

/-- **The reflected exterior mass is the negative of the forward one.** -/
theorem xiDivisor_integral_burnolReflectedDividedSource_exterior {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    (∫ t in Ioi (1 / 2 : ℝ), burnolReflectedDividedSource ρ t) =
      -burnolFirstWallExteriorMass ρ := by
  have hdisj : Disjoint (Ioc (0 : ℝ) (1 / 2)) (Ioi (1 / 2 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc (0 : ℝ) (1 / 2) ∪ Ioi (1 / 2 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hint := integrableOn_burnolReflectedDividedSource hρ0 hρ1 hxi
  have hsplit := setIntegral_union hdisj measurableSet_Ioi
    (hint.mono_set (fun x hx => mem_Ioi.mpr hx.1))
    (hint.mono_set (fun x hx => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hx))))
  rw [hunion, xiDivisor_integral_burnolReflectedDividedSource_Ioi hρ0 hρ1 hxi,
    xiDivisor_integral_burnolReflectedDividedSource_aperture hρ0] at hsplit
  rw [burnolFirstWallExteriorMass]
  linear_combination -hsplit

/-- **The reflected singular first-wall Cartier residue.** -/
theorem xiDivisor_tendsto_burnolFirstWallCosineResidue {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    Tendsto (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW (burnolReflectedDividedSource ρ) s) atTop
      (𝓝 (burnolFirstWallCosineResidue ρ)) := by
  have hIoi : IntegrableOn (burnolReflectedDividedSource ρ) (Ioi (1 / 2 : ℝ)) :=
    (integrableOn_burnolReflectedDividedSource hρ0 hρ1 hxi).mono_set
      (fun x hx => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hx)))
  have h := tendsto_burnolCrossingResidue
    (burnolReflectedDividedSource_apertureHead hρ0) hIoi
  rw [xiDivisor_integral_burnolReflectedDividedSource_exterior hρ0 hρ1 hxi] at h
  have hval : -(burnolFirstWallCosineHead ρ) *
      (starRingEnd ℂ) (-burnolFirstWallExteriorMass ρ) = burnolFirstWallCosineResidue ρ := by
    rw [burnolFirstWallCosineResidue, map_neg]
    ring
  rwa [hval] at h

end RHTower
