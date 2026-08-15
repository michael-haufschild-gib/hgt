import GaloisForLFunctions.RHTower.BurnolFirstWallCenteredPrimitive
import GaloisForLFunctions.RHTower.BurnolFirstWallExteriorMass

/-!
# The exterior mass of the forward divided shift decays quadratically

The pointwise estimate `g_ρ(t) = O(t^{-2})` only gives `∫_T^∞ g_ρ = O(T^{-1})`.  The extra power
comes from a cancellation inside the integral, which the centred primitive exposes:

`g_ρ(t) = -P₀(t) t^{-2} + (ρ+1) t^{ρ-1} ∫_t^∞ P₀(y) y^{-ρ-2} dy`.

The cell mean of `P` is what makes the boundary term of the first integration by parts cancel
against the mean part of its tail moment, and once it is removed the first summand is a moment of a
**mean-zero periodic** function, whose own primitive is bounded; the second summand is already
`O(t^{-3})` because the tail moment of `P₀` gains one power from that same bounded second
primitive.  Both pieces therefore contribute `O(T^{-2})` to the exterior mass.

Along the way the divided shift is identified with a continuous function of the cut,
`g_ρ(T) = T^{ρ-1} (M_ρ − Head_ρ(T))`, which gives its integrability beyond any positive cut without
reference to the divisor of `ξ`.
-/

open Complex Real MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-! ## The divided shift as a continuous function of the cut -/

/-- The tail moment is the total moment minus the head, for every positive cut. -/
theorem integral_burnolFractPairKernel_Ioi_eq_sub {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {t : ℝ} (ht : 0 < t) :
    (∫ y in Ioi t, burnolFractPairKernel ρ y) =
      burnolFixedAtomRawMellin ρ - burnolFractPairHead ρ t := by
  have hdisj : Disjoint (Ioc (0 : ℝ) t) (Ioi t) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc (0 : ℝ) t ∪ Ioi t = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi ht.le
  have h := setIntegral_union hdisj measurableSet_Ioi
    (integrableOn_burnolFractPairKernel_Ioc hρ0 hρ1 t)
    (integrableOn_burnolFractPairKernel_Ioi hρ0 hρ1 ht)
  rw [hunion, integral_burnolFractPairKernel hρ0 hρ1] at h
  rw [burnolFractPairHead, intervalIntegral.integral_of_le ht.le]
  linear_combination -h

theorem burnolZeroDividedSource_eq_head_sub {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {t : ℝ}
    (ht : 0 < t) :
    burnolZeroDividedSource ρ t =
      (t : ℂ) ^ (ρ - 1) * (burnolFixedAtomRawMellin ρ - burnolFractPairHead ρ t) := by
  rw [burnolZeroDividedSource_eq_tail ht, integral_burnolFractPairKernel_Ioi_eq_sub hρ0 hρ1 ht]

theorem continuousOn_burnolZeroDividedSource_pos {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ContinuousOn (burnolZeroDividedSource ρ) (Ioi 0) := by
  refine ContinuousOn.congr
    (f := fun x : ℝ => (x : ℂ) ^ (ρ - 1) * (burnolFixedAtomRawMellin ρ - burnolFractPairHead ρ x))
    ?_ fun x hx => burnolZeroDividedSource_eq_head_sub hρ0 hρ1 hx
  refine ContinuousOn.mul ?_
    (continuousOn_const.sub (continuousOn_burnolFractPairHead_Ioi hρ0 hρ1))
  intro x hx
  exact ((hasDerivAt_burnolRealCpow hx (ρ - 1)).continuousAt).continuousWithinAt

theorem integrableOn_burnolZeroDividedSource_Ioi {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT : 0 < T) : IntegrableOn (burnolZeroDividedSource ρ) (Ioi T) := by
  refine MeasureTheory.Integrable.mono'
    (g := fun t : ℝ => (1 + ‖ρ + 1‖ / (ρ.re + 1)) * t ^ (-2 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hT).const_mul _)
    (((continuousOn_burnolZeroDividedSource_pos hρ0 hρ1).mono
      fun x hx => mem_Ioi.mpr (lt_trans hT hx)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_burnolZeroDividedSource_le hρ0 hρ1 (lt_trans hT ht)

/-! ## The divided shift on the centred primitive -/

/-- **The divided shift, written on the centred primitive.**  The cell mean of `P` cancels between
the boundary term of the integration by parts and the mean part of the tail moment; what is left is
a boundary term with a mean-zero periodic factor. -/
theorem burnolZeroDividedSource_eq_centered {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {t : ℝ}
    (ht : 0 < t) :
    burnolZeroDividedSource ρ t =
      -burnolCenteredPrimitiveKernel 0 t
        + (ρ + 1) * ((t : ℂ) ^ (ρ - 1) * ∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y) := by
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpow : (t : ℂ) ^ (ρ - 1) * (t : ℂ) ^ (-(ρ + 1)) = (t : ℂ) ^ (-((0 : ℂ) + 2)) := by
    rw [← Complex.cpow_add _ _ htne]
    congr 1
    ring
  have hk0 : burnolCenteredPrimitiveKernel 0 t =
      ((burnolCenteredPrimitive t : ℝ) : ℂ) * ((t : ℂ) ^ (ρ - 1) * (t : ℂ) ^ (-(ρ + 1))) := by
    rw [burnolCenteredPrimitiveKernel, hpow]
  rw [burnolZeroDividedSource_eq_tail ht,
    integral_burnolFractPairKernel_Ioi_centered hρ0 hρ1 ht, hk0]
  ring

/-! ## The quadratic exterior mass -/

/-- The constant in the quadratic exterior-mass bound. -/
def burnolTailMassConstant (ρ : ℂ) : ℝ := ‖ρ + 1‖ * (1 + ‖ρ + 2‖ / (ρ.re + 2)) + 4

theorem burnolTailMassConstant_nonneg {ρ : ℂ} (hρ : -2 < ρ.re) : 0 ≤ burnolTailMassConstant ρ := by
  have hquot : (0 : ℝ) ≤ ‖ρ + 2‖ / (ρ.re + 2) := div_nonneg (norm_nonneg _) (by linarith)
  have hprod : (0 : ℝ) ≤ ‖ρ + 1‖ * (1 + ‖ρ + 2‖ / (ρ.re + 2)) :=
    mul_nonneg (norm_nonneg _) (by linarith)
  rw [burnolTailMassConstant]
  linarith

/-- **The exterior mass of the forward divided shift is `O(T^{-2})`.** -/
theorem norm_integral_burnolZeroDividedSource_Ioi_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT : 0 < T) :
    ‖∫ t in Ioi T, burnolZeroDividedSource ρ t‖ ≤ burnolTailMassConstant ρ * T ^ (-2 : ℝ) := by
  have hgint : IntegrableOn (burnolZeroDividedSource ρ) (Ioi T) :=
    integrableOn_burnolZeroDividedSource_Ioi hρ0 hρ1 hT
  have hk0int : IntegrableOn (burnolCenteredPrimitiveKernel 0) (Ioi T) :=
    integrableOn_burnolCenteredPrimitiveKernel (by rw [Complex.zero_re]; norm_num) hT
  have hsum : (∫ t in Ioi T, burnolZeroDividedSource ρ t) =
      (∫ t in Ioi T, (burnolZeroDividedSource ρ t + burnolCenteredPrimitiveKernel 0 t))
        - ∫ t in Ioi T, burnolCenteredPrimitiveKernel 0 t := by
    rw [MeasureTheory.integral_add hgint hk0int]
    ring
  -- the mean-zero boundary term
  have hA : ‖∫ t in Ioi T, burnolCenteredPrimitiveKernel 0 t‖ ≤ 4 * T ^ (-2 : ℝ) := by
    have h := norm_integral_burnolCenteredPrimitiveKernel_Ioi_le (ρ := (0 : ℂ))
      (by rw [Complex.zero_re]; norm_num) hT
    rw [Complex.zero_re, show ((0 : ℂ) + 2) = 2 by ring,
      show ‖(2 : ℂ)‖ = 2 by norm_num, show (0 : ℝ) + 2 = 2 by norm_num] at h
    calc ‖∫ t in Ioi T, burnolCenteredPrimitiveKernel 0 t‖
        ≤ 2 * (1 + 2 / 2) * T ^ (-2 : ℝ) := h
      _ = 4 * T ^ (-2 : ℝ) := by rw [show (2 : ℝ) * (1 + 2 / 2) = 4 by norm_num]
  -- the tail term, already one power better
  have hB : ‖∫ t in Ioi T, (burnolZeroDividedSource ρ t + burnolCenteredPrimitiveKernel 0 t)‖
      ≤ ‖ρ + 1‖ * (1 + ‖ρ + 2‖ / (ρ.re + 2)) * T ^ (-2 : ℝ) := by
    have hpt : ∀ᵐ t ∂(volume.restrict (Ioi T)),
        ‖burnolZeroDividedSource ρ t + burnolCenteredPrimitiveKernel 0 t‖ ≤
          2 * ‖ρ + 1‖ * (1 + ‖ρ + 2‖ / (ρ.re + 2)) * t ^ (-3 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t htm
      have ht0 : 0 < t := lt_trans hT htm
      have hcancel : -burnolCenteredPrimitiveKernel 0 t
          + (ρ + 1) * ((t : ℂ) ^ (ρ - 1) * ∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y)
          + burnolCenteredPrimitiveKernel 0 t
          = (ρ + 1) * ((t : ℂ) ^ (ρ - 1) * ∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y) := by
        ring
      rw [burnolZeroDividedSource_eq_centered hρ0 hρ1 ht0, hcancel, norm_mul, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0,
        show (ρ - 1).re = ρ.re - 1 by rw [Complex.sub_re, Complex.one_re]]
      have hprep : (0 : ℝ) < t ^ (ρ.re - 1) := Real.rpow_pos_of_pos ht0 _
      have hstep : t ^ (ρ.re - 1) * ‖∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y‖ ≤
          t ^ (ρ.re - 1) * (2 * (1 + ‖ρ + 2‖ / (ρ.re + 2)) * t ^ (-(ρ.re + 2))) :=
        mul_le_mul_of_nonneg_left
          (norm_integral_burnolCenteredPrimitiveKernel_Ioi_le (by linarith) ht0) hprep.le
      have hcomb : t ^ (ρ.re - 1) * t ^ (-(ρ.re + 2)) = t ^ (-3 : ℝ) := by
        rw [← Real.rpow_add ht0]
        congr 1
        ring
      calc ‖ρ + 1‖ * (t ^ (ρ.re - 1) * ‖∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y‖)
          ≤ ‖ρ + 1‖ * (t ^ (ρ.re - 1) * (2 * (1 + ‖ρ + 2‖ / (ρ.re + 2)) * t ^ (-(ρ.re + 2)))) :=
            mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
        _ = 2 * ‖ρ + 1‖ * (1 + ‖ρ + 2‖ / (ρ.re + 2)) * t ^ (-3 : ℝ) := by
            rw [← hcomb]; ring
    have hdom : IntegrableOn
        (fun t : ℝ => 2 * ‖ρ + 1‖ * (1 + ‖ρ + 2‖ / (ρ.re + 2)) * t ^ (-3 : ℝ)) (Ioi T) :=
      ((integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hT).congr_fun
        (fun _ _ => rfl) measurableSet_Ioi).const_mul _
    have hcmp := MeasureTheory.norm_integral_le_of_norm_le hdom hpt
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hT] at hcmp
    have hval : -T ^ ((-3 : ℝ) + 1) / ((-3 : ℝ) + 1) = T ^ (-2 : ℝ) / 2 := by
      rw [show (-3 : ℝ) + 1 = -2 by norm_num]
      ring
    rw [hval] at hcmp
    refine le_trans hcmp (le_of_eq ?_)
    ring
  have hexpand : burnolTailMassConstant ρ * T ^ (-2 : ℝ)
      = ‖ρ + 1‖ * (1 + ‖ρ + 2‖ / (ρ.re + 2)) * T ^ (-2 : ℝ) + 4 * T ^ (-2 : ℝ) := by
    rw [burnolTailMassConstant]; ring
  rw [hsum, hexpand]
  exact le_trans (norm_sub_le _ _) (by linarith [hA, hB])

end RHTower
