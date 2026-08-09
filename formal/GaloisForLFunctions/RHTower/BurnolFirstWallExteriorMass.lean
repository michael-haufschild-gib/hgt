import GaloisForLFunctions.RHTower.BurnolFirstWallSourceMass

/-!
# The exterior mass of the zero-divided source

At a zero of `ξ` the forward divided shift has an explicit potential,

`Φ_ρ(T) = (1/ρ) ∫_0^T f₀ - (T^ρ/ρ) ∫_0^T p(y) y^{-ρ-1} dy`,

whose right derivative is `g_ρ` and whose value at the origin is zero.  Hence the truncated mass of
`g_ρ` is `Φ_ρ(T)`; the second term is `O(T)` at the origin and `O(1/T)` at infinity, so the total
mass is `1/ρ` times the improper mass of the raw source:

`∫_0^∞ g_ρ = -(log 2)/(2ρ) = b_ρ/2`.

Subtracting the constant head on the aperture `(0,1/2]` gives the exterior mass
`B_ρ = (b_ρ - a_ρ)/2`, which is exactly the abstract first-wall exterior mass.
-/

open Complex Real MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-! ## Elementary bounds on the coboundary kernel -/

theorem abs_burnolFractPair_le_self {y : ℝ} (hy : 0 ≤ y) : |burnolFractPair y| ≤ y := by
  rcases lt_or_ge y 1 with h | h
  · exact abs_burnolFractPair_le_of_lt_one hy h
  · exact le_trans (abs_burnolFractPair_le_one y) h

theorem norm_burnolFractPairKernel_le {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖burnolFractPairKernel ρ y‖ ≤ y ^ (-ρ.re) := by
  rw [burnolFractPairKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (-(ρ + 1)).re = -(ρ.re + 1) := by
    rw [Complex.neg_re, Complex.add_re]; norm_num
  rw [hre]
  have hsplit : y ^ (-(ρ.re + 1)) * y = y ^ (-ρ.re) := by
    nth_rewrite 2 [show y = y ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hy]
    congr 1
    ring
  have hbound := abs_burnolFractPair_le_self hy.le
  have hpos : (0 : ℝ) < y ^ (-(ρ.re + 1)) := Real.rpow_pos_of_pos hy _
  nlinarith [hbound, hpos, hsplit]

theorem burnolFractPairKernel_zero (ρ : ℂ) : burnolFractPairKernel ρ 0 = 0 := by
  rw [burnolFractPairKernel, burnolFractPair]
  norm_num

/-- The head moment of the coboundary kernel. -/
def burnolFractPairHead (ρ : ℂ) (T : ℝ) : ℂ := ∫ y in (0 : ℝ)..T, burnolFractPairKernel ρ y

theorem intervalIntegrable_burnolFractPairKernel_zero {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT : 0 ≤ T) : IntervalIntegrable (burnolFractPairKernel ρ) volume 0 T := by
  rw [intervalIntegrable_iff]
  refine (integrableOn_burnolFractPairKernel hρ0 hρ1).mono_set ?_
  rw [Set.uIoc_of_le hT]
  exact fun y hy => mem_Ioi.mpr hy.1

theorem norm_burnolFractPairHead_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {T : ℝ}
    (hT : 0 ≤ T) : ‖burnolFractPairHead ρ T‖ ≤ T ^ (1 - ρ.re) / (1 - ρ.re) := by
  have hrpow : IntervalIntegrable (fun y : ℝ => y ^ (-ρ.re)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hnorm : ‖burnolFractPairHead ρ T‖ ≤ ∫ y in (0 : ℝ)..T, y ^ (-ρ.re) := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hT) ?_
    refine intervalIntegral.integral_mono_on hT
      ((intervalIntegrable_burnolFractPairKernel_zero hρ0 hρ1 hT).norm) hrpow ?_
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h, burnolFractPairKernel_zero, norm_zero]
      exact Real.rpow_nonneg le_rfl _
    · exact norm_burnolFractPairKernel_le h
  refine le_trans hnorm (le_of_eq ?_)
  rw [integral_rpow (Or.inl (by linarith))]
  have h1 : -ρ.re + 1 = 1 - ρ.re := by ring
  rw [h1, Real.zero_rpow (by linarith : (1 : ℝ) - ρ.re ≠ 0), sub_zero]

theorem continuousWithinAt_burnolFractPairKernel_Ici {ρ : ℂ} {a : ℝ} (ha : 0 < a) :
    ContinuousWithinAt (burnolFractPairKernel ρ) (Ici a) a := by
  refine ContinuousWithinAt.mul ?_ ?_
  · exact Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_burnolFractPair_Ici a)
  · exact ((hasDerivAt_burnolRealCpow ha (-(ρ + 1))).continuousAt).continuousWithinAt

theorem hasDerivWithinAt_burnolFractPairHead {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {a : ℝ}
    (ha : 0 < a) :
    HasDerivWithinAt (burnolFractPairHead ρ) (burnolFractPairKernel ρ a) (Ici a) a :=
  intervalIntegral.integral_hasDerivWithinAt_right (s := Ici a) (t := Ioi a)
    (intervalIntegrable_burnolFractPairKernel_zero hρ0 hρ1 ha.le)
    ⟨Ioi a, self_mem_nhdsWithin,
      ((integrableOn_burnolFractPairKernel hρ0 hρ1).mono_set
        (fun _ hy => mem_Ioi.mpr (lt_trans ha hy))).aestronglyMeasurable⟩
    ((continuousWithinAt_burnolFractPairKernel_Ici ha).mono Ioi_subset_Ici_self)

theorem continuousOn_burnolFractPairHead {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {T : ℝ}
    (hT : 0 ≤ T) : ContinuousOn (burnolFractPairHead ρ) (Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_burnolFractPairKernel_zero hρ0 hρ1 hT)
    (by rw [Set.uIcc_of_le hT]; exact ⟨le_rfl, hT⟩)
  rwa [Set.uIcc_of_le hT] at h

/-! ## The raw-source head -/

/-- The truncated mass of the raw source, complexified. -/
def burnolRawSourceHead (T : ℝ) : ℂ := ∫ y in (0 : ℝ)..T, ((burnolRawSource y : ℝ) : ℂ)

theorem intervalIntegrable_burnolRawSourceC {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun y : ℝ => ((burnolRawSource y : ℝ) : ℂ)) volume a b :=
  ⟨(intervalIntegrable_burnolRawSource ha hb).1.ofReal,
    (intervalIntegrable_burnolRawSource ha hb).2.ofReal⟩

theorem continuousWithinAt_burnolRawSource_Ici {a : ℝ} (ha : 0 < a) :
    ContinuousWithinAt burnolRawSource (Ici a) a := by
  refine ContinuousWithinAt.div (continuousWithinAt_burnolFractPair_Ici a)
    continuousWithinAt_id (ne_of_gt ha)

theorem hasDerivWithinAt_burnolRawSourceHead {a : ℝ} (ha : 0 < a) :
    HasDerivWithinAt burnolRawSourceHead ((burnolRawSource a : ℝ) : ℂ) (Ici a) a :=
  intervalIntegral.integral_hasDerivWithinAt_right (s := Ici a) (t := Ioi a)
    (intervalIntegrable_burnolRawSourceC le_rfl ha.le)
    ⟨Ioi a, self_mem_nhdsWithin,
      (Complex.measurable_ofReal.comp measurable_burnolRawSource).aestronglyMeasurable.restrict⟩
    (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_burnolRawSource_Ici ha).mono Ioi_subset_Ici_self))

theorem continuousOn_burnolRawSourceHead {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn burnolRawSourceHead (Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_burnolRawSourceC le_rfl hT)
    (by rw [Set.uIcc_of_le hT]; exact ⟨le_rfl, hT⟩)
  rwa [Set.uIcc_of_le hT] at h

theorem continuousWithinAt_burnolCpowHead_zero {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (T : ℝ) :
    ContinuousWithinAt (fun y : ℝ => (y : ℂ) ^ ρ * burnolFractPairHead ρ y) (Icc 0 T) 0 := by
  have hval : (((0 : ℝ) : ℂ)) ^ ρ * burnolFractPairHead ρ 0 = 0 := by
    rw [burnolFractPairHead, intervalIntegral.integral_same, mul_zero]
  have hlim : Tendsto (fun y : ℝ => (y : ℂ) ^ ρ * burnolFractPairHead ρ y)
      (𝓝[Icc (0 : ℝ) T] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun y : ℝ => y / (1 - ρ.re))
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hy0 : 0 ≤ y := hy.1
      rcases eq_or_lt_of_le hy0 with hy1 | hy1
      · rw [← hy1, burnolFractPairHead, intervalIntegral.integral_same, mul_zero, norm_zero]
        positivity
      · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy1]
        have hhead := norm_burnolFractPairHead_le hρ0 hρ1 hy0
        have hpos : (0 : ℝ) < y ^ ρ.re := Real.rpow_pos_of_pos hy1 _
        have hstep := mul_le_mul_of_nonneg_left hhead hpos.le
        refine le_trans hstep (le_of_eq ?_)
        rw [show y ^ ρ.re * (y ^ (1 - ρ.re) / (1 - ρ.re)) =
            (y ^ ρ.re * y ^ (1 - ρ.re)) / (1 - ρ.re) by ring, ← Real.rpow_add hy1,
          show ρ.re + (1 - ρ.re) = 1 by ring, Real.rpow_one]
    · have hc : Tendsto (fun y : ℝ => y / (1 - ρ.re)) (𝓝[Icc 0 T] (0 : ℝ))
          (𝓝 (0 / (1 - ρ.re))) :=
        ((continuous_id.div_const (1 - ρ.re)).tendsto 0).mono_left nhdsWithin_le_nhds
      rwa [zero_div] at hc
  show Tendsto (fun y : ℝ => (y : ℂ) ^ ρ * burnolFractPairHead ρ y) (𝓝[Icc (0 : ℝ) T] 0)
    (𝓝 ((((0 : ℝ) : ℂ)) ^ ρ * burnolFractPairHead ρ 0))
  rw [hval]
  exact hlim

/-! ## The potential of the divided shift -/

/-- The exact potential of the forward divided shift. -/
def burnolZeroDividedPotential (ρ : ℂ) (T : ℝ) : ℂ :=
  burnolRawSourceHead T / ρ - (T : ℂ) ^ ρ * burnolFractPairHead ρ T / ρ

theorem burnolZeroDividedPotential_zero (ρ : ℂ) : burnolZeroDividedPotential ρ 0 = 0 := by
  rw [burnolZeroDividedPotential, burnolRawSourceHead, burnolFractPairHead,
    intervalIntegral.integral_same, intervalIntegral.integral_same]
  simp

theorem burnolFractPairHead_eq_neg_tail {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {T : ℝ} (hT : 0 < T) :
    burnolFractPairHead ρ T = -∫ y in Ioi T, burnolFractPairKernel ρ y := by
  rw [xiDivisor_integral_burnolFractPairKernel_Ioi hρ0 hρ1 hxi hT, neg_neg,
    burnolFractPairHead, intervalIntegral.integral_of_le hT.le]

theorem xiDivisor_burnolZeroDividedSource_eq_head {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {T : ℝ} (hT : 0 < T) :
    burnolZeroDividedSource ρ T = -((T : ℂ) ^ (ρ - 1) * burnolFractPairHead ρ T) := by
  rw [burnolZeroDividedSource_eq_tail hT, burnolFractPairHead_eq_neg_tail hρ0 hρ1 hxi hT]
  ring

theorem hasDerivWithinAt_burnolZeroDividedPotential {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {T : ℝ} (hT : 0 < T) :
    HasDerivWithinAt (burnolZeroDividedPotential ρ) (burnolZeroDividedSource ρ T) (Ici T) T := by
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ0
    exact lt_irrefl 0 hρ0
  have hTne : ((T : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hA : HasDerivWithinAt (fun x : ℝ => burnolRawSourceHead x / ρ)
      (((burnolRawSource T : ℝ) : ℂ) / ρ) (Ici T) T :=
    (hasDerivWithinAt_burnolRawSourceHead hT).div_const ρ
  have hcpow : HasDerivWithinAt (fun x : ℝ => (x : ℂ) ^ ρ) (ρ * (T : ℂ) ^ (ρ - 1)) (Ici T) T :=
    (hasDerivAt_burnolRealCpow hT ρ).hasDerivWithinAt
  have hprod := (hcpow.mul (hasDerivWithinAt_burnolFractPairHead hρ0 hρ1 hT)).div_const ρ
  have hsub := hA.sub hprod
  refine hsub.congr_deriv ?_
  have hraw : ((burnolRawSource T : ℝ) : ℂ) =
      ((burnolFractPair T : ℝ) : ℂ) / ((T : ℝ) : ℂ) := by
    rw [burnolRawSource, Complex.ofReal_div]
  have hker : (T : ℂ) ^ ρ * burnolFractPairKernel ρ T =
      ((burnolFractPair T : ℝ) : ℂ) / ((T : ℝ) : ℂ) := by
    rw [burnolFractPairKernel, ← mul_assoc, mul_comm ((T : ℂ) ^ ρ), mul_assoc,
      ← Complex.cpow_add _ _ hTne, show ρ + -(ρ + 1) = (-1 : ℂ) by ring, Complex.cpow_neg_one,
      div_eq_mul_inv]
  rw [xiDivisor_burnolZeroDividedSource_eq_head hρ0 hρ1 hxi hT, hraw, hker]
  field_simp
  ring

/-! ## The truncated mass -/

theorem continuousOn_burnolZeroDividedSource {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (burnolZeroDividedSource ρ) (Ioc 0 T) := by
  refine ContinuousOn.congr (f := fun x : ℝ => -((x : ℂ) ^ (ρ - 1) * burnolFractPairHead ρ x)) ?_
    (fun x hx => (xiDivisor_burnolZeroDividedSource_eq_head hρ0 hρ1 hxi hx.1))
  refine ContinuousOn.neg (ContinuousOn.mul ?_ ?_)
  · intro x hx
    exact ((hasDerivAt_burnolRealCpow hx.1 (ρ - 1)).continuousAt).continuousWithinAt
  · exact (continuousOn_burnolFractPairHead hρ0 hρ1 hT).mono
      (fun x hx => ⟨hx.1.le, hx.2⟩)

theorem norm_burnolZeroDividedSource_le_const {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {t : ℝ} (ht : 0 < t) :
    ‖burnolZeroDividedSource ρ t‖ ≤ 1 / (1 - ρ.re) := by
  rw [xiDivisor_burnolZeroDividedSource_eq_head hρ0 hρ1 hxi ht, norm_neg, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hre : (ρ - 1).re = ρ.re - 1 := by rw [Complex.sub_re, Complex.one_re]
  rw [hre]
  have hpos : (0 : ℝ) < t ^ (ρ.re - 1) := Real.rpow_pos_of_pos ht _
  have hhead := norm_burnolFractPairHead_le hρ0 hρ1 ht.le
  have hstep := mul_le_mul_of_nonneg_left hhead hpos.le
  refine le_trans hstep (le_of_eq ?_)
  rw [show t ^ (ρ.re - 1) * (t ^ (1 - ρ.re) / (1 - ρ.re)) =
      (t ^ (ρ.re - 1) * t ^ (1 - ρ.re)) / (1 - ρ.re) by ring, ← Real.rpow_add ht,
    show ρ.re - 1 + (1 - ρ.re) = 0 by ring, Real.rpow_zero]

theorem intervalIntegrable_burnolZeroDividedSource {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (burnolZeroDividedSource ρ) volume 0 T := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hT]
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => 1 / (1 - ρ.re))
    (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) T) measure_Ioc_lt_top.ne)
    ((continuousOn_burnolZeroDividedSource hρ0 hρ1 hxi hT).aestronglyMeasurable
      measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact norm_burnolZeroDividedSource_le_const hρ0 hρ1 hxi hx.1

theorem continuousOn_burnolZeroDividedPotential {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (burnolZeroDividedPotential ρ) (Icc 0 T) := by
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ0
    exact lt_irrefl 0 hρ0
  refine ContinuousOn.sub ((continuousOn_burnolRawSourceHead hT).div_const ρ) ?_
  refine ContinuousOn.div_const ?_ ρ
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h
    exact continuousWithinAt_burnolCpowHead_zero hρ0 hρ1 T
  · refine ContinuousWithinAt.mul ?_ ?_
    · exact ((hasDerivAt_burnolRealCpow h ρ).continuousAt).continuousWithinAt
    · exact continuousOn_burnolFractPairHead hρ0 hρ1 hT x hx

/-- **The truncated mass of the divided shift is its potential.** -/
theorem xiDivisor_integral_burnolZeroDividedSource {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, burnolZeroDividedSource ρ t) = burnolZeroDividedPotential ρ T := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) T, HasDerivWithinAt (burnolZeroDividedPotential ρ)
      (burnolZeroDividedSource ρ x) (Ioi x) x := fun x hx =>
    (hasDerivWithinAt_burnolZeroDividedPotential hρ0 hρ1 hxi hx.1).mono Ioi_subset_Ici_self
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
    (continuousOn_burnolZeroDividedPotential hρ0 hρ1 hT) hderiv
    (intervalIntegrable_burnolZeroDividedSource hρ0 hρ1 hxi hT)
  rw [hftc, burnolZeroDividedPotential_zero, sub_zero]

/-! ## The total and exterior masses -/

theorem burnolRawSourceHead_eq_ofReal {T : ℝ} (hT : 0 ≤ T) :
    burnolRawSourceHead T = (((∫ y in (0 : ℝ)..T, burnolRawSource y : ℝ)) : ℂ) := by
  rw [burnolRawSourceHead, intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_of_le hT, integral_complex_ofReal]

theorem norm_burnolFractPairHead_le_tail {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {T : ℝ} (hT : 0 < T) :
    ‖burnolFractPairHead ρ T‖ ≤ (1 + ‖ρ + 1‖ / (ρ.re + 1)) * T ^ (-(ρ.re + 1)) := by
  rw [burnolFractPairHead_eq_neg_tail hρ0 hρ1 hxi hT, norm_neg]
  exact norm_integral_burnolFractPairKernel_Ioi_le hρ0 hρ1 hT

theorem tendsto_burnolZeroDividedPotential {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) :
    Tendsto (burnolZeroDividedPotential ρ) atTop (𝓝 (((-(Real.log 2) / 2 : ℝ) : ℂ) / ρ)) := by
  have hraw : Tendsto (fun T : ℝ => burnolRawSourceHead T / ρ) atTop
      (𝓝 (((-(Real.log 2) / 2 : ℝ) : ℂ) / ρ)) := by
    have hR := (Complex.continuous_ofReal.tendsto _).comp tendsto_integral_burnolRawSource
    refine (hR.div_const ρ).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [Function.comp_apply, ← burnolRawSourceHead_eq_ofReal hT]
  have hbdry : Tendsto
      (fun T : ℝ => (T : ℂ) ^ ρ * burnolFractPairHead ρ T / ρ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdom : Tendsto
        (fun T : ℝ => (1 + ‖ρ + 1‖ / (ρ.re + 1)) / ‖ρ‖ * T ^ (-(1 : ℝ))) atTop (𝓝 0) := by
      have h := (_root_.tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1)).const_mul
        ((1 + ‖ρ + 1‖ / (ρ.re + 1)) / ‖ρ‖)
      simpa using h
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hdom
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hT]
    have hhead := norm_burnolFractPairHead_le_tail hρ0 hρ1 hxi hT
    have hpos : (0 : ℝ) < T ^ ρ.re := Real.rpow_pos_of_pos hT _
    have hρnorm : (0 : ℝ) < ‖ρ‖ := by
      refine norm_pos_iff.mpr ?_
      intro h
      rw [h, Complex.zero_re] at hρ0
      exact lt_irrefl 0 hρ0
    have hstep := mul_le_mul_of_nonneg_left hhead hpos.le
    have hcomb : T ^ ρ.re * ((1 + ‖ρ + 1‖ / (ρ.re + 1)) * T ^ (-(ρ.re + 1))) =
        (1 + ‖ρ + 1‖ / (ρ.re + 1)) * T ^ (-(1 : ℝ)) := by
      rw [show T ^ ρ.re * ((1 + ‖ρ + 1‖ / (ρ.re + 1)) * T ^ (-(ρ.re + 1))) =
          (1 + ‖ρ + 1‖ / (ρ.re + 1)) * (T ^ ρ.re * T ^ (-(ρ.re + 1))) by ring,
        ← Real.rpow_add hT]
      congr 2
      ring
    rw [div_le_iff₀ hρnorm]
    have hrhs : (1 + ‖ρ + 1‖ / (ρ.re + 1)) / ‖ρ‖ * T ^ (-(1 : ℝ)) * ‖ρ‖ =
        (1 + ‖ρ + 1‖ / (ρ.re + 1)) * T ^ (-(1 : ℝ)) := by
      field_simp
    rw [hrhs]
    linarith [hstep, hcomb.le, hcomb.ge]
  have hsum := hraw.sub hbdry
  rw [sub_zero] at hsum
  exact hsum.congr fun T => rfl

theorem continuousOn_burnolFractPairHead_Ioi {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ContinuousOn (burnolFractPairHead ρ) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hmem : Icc (0 : ℝ) (x + 1) ∈ 𝓝 x :=
    Icc_mem_nhds hx0 (by linarith)
  exact ((continuousOn_burnolFractPairHead hρ0 hρ1 (by linarith : (0:ℝ) ≤ x + 1)).continuousAt
    hmem).continuousWithinAt

theorem continuousOn_burnolZeroDividedSource_Ioi {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) : ContinuousOn (burnolZeroDividedSource ρ) (Ioi 0) := by
  refine ContinuousOn.congr (f := fun x : ℝ => -((x : ℂ) ^ (ρ - 1) * burnolFractPairHead ρ x)) ?_
    (fun x hx => (xiDivisor_burnolZeroDividedSource_eq_head hρ0 hρ1 hxi hx))
  refine ContinuousOn.neg (ContinuousOn.mul ?_ (continuousOn_burnolFractPairHead_Ioi hρ0 hρ1))
  intro x hx
  exact ((hasDerivAt_burnolRealCpow hx (ρ - 1)).continuousAt).continuousWithinAt

theorem integrableOn_burnolZeroDividedSource {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) : IntegrableOn (burnolZeroDividedSource ρ) (Ioi 0) := by
  have hmeasIoc : AEStronglyMeasurable (burnolZeroDividedSource ρ)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuousOn_burnolZeroDividedSource_Ioi hρ0 hρ1 hxi).mono
      (fun x hx => mem_Ioi.mpr hx.1)).aestronglyMeasurable measurableSet_Ioc
  have hmeasIoi : AEStronglyMeasurable (burnolZeroDividedSource ρ)
      (volume.restrict (Ioi (1 : ℝ))) :=
    ((continuousOn_burnolZeroDividedSource_Ioi hρ0 hρ1 hxi).mono
      (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one hx))).aestronglyMeasurable measurableSet_Ioi
  have hnear : IntegrableOn (burnolZeroDividedSource ρ) (Ioc (0 : ℝ) 1) := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => 1 / (1 - ρ.re))
      (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) 1) measure_Ioc_lt_top.ne)
      hmeasIoc ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact norm_burnolZeroDividedSource_le_const hρ0 hρ1 hxi hx.1
  have hfar : IntegrableOn (burnolZeroDividedSource ρ) (Ioi (1 : ℝ)) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => (1 + ‖ρ + 1‖ / (ρ.re + 1)) * t ^ (-2 : ℝ))
      (((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) one_pos)).const_mul _)
      hmeasIoi ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_burnolZeroDividedSource_le hρ0 hρ1 (lt_trans zero_lt_one ht)
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hunion]
  exact hnear.union hfar

/-- **The total mass of the zero-divided source.** -/
theorem xiDivisor_integral_burnolZeroDividedSource_Ioi {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) :
    (∫ t in Ioi (0 : ℝ), burnolZeroDividedSource ρ t) = burnolFirstWallCosineHead ρ / 2 := by
  have hlim : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, burnolZeroDividedSource ρ t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), burnolZeroDividedSource ρ t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_burnolZeroDividedSource hρ0 hρ1 hxi) tendsto_id
  have hpot := tendsto_burnolZeroDividedPotential hρ0 hρ1 hxi
  have heq := tendsto_nhds_unique (hlim.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact xiDivisor_integral_burnolZeroDividedSource hρ0 hρ1 hxi hT)) hpot
  rw [heq, burnolFirstWallCosineHead]
  push_cast
  ring

/-- The aperture mass is half the forward head. -/
theorem xiDivisor_integral_burnolZeroDividedSource_aperture {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    (∫ t in Ioc (0 : ℝ) (1 / 2), burnolZeroDividedSource ρ t) = burnolFirstWallHead ρ / 2 := by
  have hcongr : (∫ t in Ioc (0 : ℝ) (1 / 2), burnolZeroDividedSource ρ t) =
      ∫ _t in Ioc (0 : ℝ) (1 / 2), burnolFirstWallHead ρ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    exact xiDivisor_burnolZeroDividedSource_head_eq hρ0 hρ1 hxi ht.1 ht.2
  rw [hcongr, setIntegral_const]
  have hvol : (volume.real (Ioc (0 : ℝ) (1 / 2))) = 1 / 2 := by
    simp [MeasureTheory.measureReal_def, Real.volume_Ioc]
  rw [hvol, Complex.real_smul]
  push_cast
  ring

/-- **The exterior mass of the zero-divided source is the abstract first-wall exterior mass.** -/
theorem xiDivisor_integral_burnolZeroDividedSource_exterior {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    (∫ t in Ioi (1 / 2 : ℝ), burnolZeroDividedSource ρ t) = burnolFirstWallExteriorMass ρ := by
  have hdisj : Disjoint (Ioc (0 : ℝ) (1 / 2)) (Ioi (1 / 2 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc (0 : ℝ) (1 / 2) ∪ Ioi (1 / 2 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hint := integrableOn_burnolZeroDividedSource hρ0 hρ1 hxi
  have hsplit := setIntegral_union hdisj measurableSet_Ioi
    (hint.mono_set (fun x hx => mem_Ioi.mpr hx.1))
    (hint.mono_set (fun x hx => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hx))))
  rw [hunion, xiDivisor_integral_burnolZeroDividedSource_Ioi hρ0 hρ1 hxi,
    xiDivisor_integral_burnolZeroDividedSource_aperture hρ0 hρ1 hxi] at hsplit
  rw [burnolFirstWallExteriorMass]
  linear_combination -hsplit

end RHTower
