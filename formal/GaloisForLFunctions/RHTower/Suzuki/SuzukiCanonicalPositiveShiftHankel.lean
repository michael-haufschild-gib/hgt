import GaloisForLFunctions.HTGeometry.IntegrableMultiplicativeHankel
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalCompressedHankelOperator

/-! The literal arithmetic Hankel operator is compact and self-adjoint for every positive
shift. Integrable cusp mass replaces the square-integrable-row requirement. -/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.SuzukiPositiveShiftHankel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Measure.Subtype.measureSpace

/-- Absolute Mellin admission gives local integrability of the complete arithmetic source,
including every cusp, for every strictly positive shift. -/
theorem integrableOn_source (omega b : ℝ) (homega : 0 < omega) :
    IntegrableOn (suzukiSourceHFinite omega) (Icc 1 b) := by
  let s : ℂ := ((omega+2:ℝ):ℂ)
  have hs : 1+omega < s.re := by simp only [s,Complex.ofReal_re]; linarith
  have hi := (hasMellin_suzukiSourceH_eq_xiRatio (s := s) homega hs).1
  change IntegrableOn (fun u : ℝ => (u:ℂ)^((1-s)-1) • suzukiSourceH omega u) (Ioi 0) at hi
  simp only [show (1-s)-1 = -s by ring,smul_eq_mul] at hi
  have hc : ContinuousOn (fun u : ℝ => (u:ℂ)^s) (Icc 1 b) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun _ hu => Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le zero_lt_one hu.1))
  have hlocal := (hi.mono_set (fun _ hu => lt_of_lt_of_le zero_lt_one hu.1)).mul_continuousOn
    hc isCompact_Icc
  apply hlocal.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hu0 : (u:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1))
  calc
    ((u:ℂ)^(-s)*suzukiSourceH omega u)*(u:ℂ)^s =
        ((u:ℂ)^(-s)*(u:ℂ)^s)*suzukiSourceH omega u := by ring
    _ = suzukiSourceHFinite omega u := by
      rw [← Complex.cpow_add (-s) s hu0,neg_add_cancel,Complex.cpow_zero,one_mul,
        suzukiSourceH_eq_finite]

private theorem source_measurable (omega : ℝ) : Measurable (suzukiSourceHFinite omega) := by
  have he : suzukiSourceHFinite omega=suzukiSourceH omega :=
    funext (fun u => (suzukiSourceH_eq_finite omega u).symm)
  rw [he]
  exact measurable_suzukiSourceH omega

private def profile (omega a : ℝ) (homega : 0 < omega) : MultiplicativeHankel.Profile where
  toFun := (Ioc 1 (a^2)).indicator (suzukiSourceHFinite omega)
  measurable := (source_measurable omega).indicator measurableSet_Ioc
  integrable := ((integrableOn_source omega (a^2) homega).mono_set
    (fun _ hu => ⟨hu.1.le,hu.2⟩)).integrable_indicator measurableSet_Ioc
  zero_below u hu := by
    apply Set.indicator_of_notMem
    intro h
    exact not_lt_of_ge hu h.1

private theorem profile_eq_source {omega a : ℝ} (homega : 0 < omega) (ha : 1 < a)
    (x y : ClosedInterval 0 a) :
    (profile omega a homega).toFun ((x:ℝ)*(y:ℝ)) =
      suzukiSourceHFinite omega ((x:ℝ)*(y:ℝ)) := by
  change (Ioc 1 (a^2)).indicator (suzukiSourceHFinite omega) ((x:ℝ)*(y:ℝ)) = _
  by_cases hxy : 1 < (x:ℝ)*(y:ℝ)
  · apply Set.indicator_of_mem
    refine ⟨hxy,?_⟩
    have h := mul_le_mul x.property.2 y.property.2 y.property.1 (by linarith : 0 ≤ a)
    nlinarith
  · rw [Set.indicator_of_notMem (by exact fun h => hxy h.1)]
    simp only [suzukiSourceHFinite,if_neg hxy]

private theorem profile_conj (omega a : ℝ) (homega : 0 < omega) (u : ℝ) :
    (starRingEnd ℂ) ((profile omega a homega).toFun u) = (profile omega a homega).toFun u := by
  change (starRingEnd ℂ) ((Ioc 1 (a^2)).indicator (suzukiSourceHFinite omega) u) =
    (Ioc 1 (a^2)).indicator (suzukiSourceHFinite omega) u
  by_cases hu : u ∈ Ioc 1 (a^2)
  · simp only [Set.indicator_of_mem hu,conj_suzukiSourceHFinite]
  · simp only [Set.indicator_of_notMem hu,map_zero]

/-- The exact source integral on the original interval space, including the critical
shift range where square-integrable kernel rows are unavailable. -/
def operator (omega a : ℝ) (homega : 0 < omega) : IntervalL2 0 a →L[ℂ] IntervalL2 0 a :=
  if ha : 1 < a then MultiplicativeHankel.operator ha (profile omega a homega) else 0

private theorem source_zero_below_aperture {omega a : ℝ} (ha : a ≤ 1)
    (x y : ClosedInterval 0 a) : suzukiSourceHFinite omega ((x:ℝ)*(y:ℝ))=0 := by
  have ha0 : 0 ≤ a := x.property.1.trans x.property.2
  have h := mul_le_mul x.property.2 y.property.2 y.property.1 ha0
  have hxy : (x:ℝ)*(y:ℝ) ≤ 1 := by nlinarith
  simp only [suzukiSourceHFinite,if_neg (not_lt_of_ge hxy)]

/-- The unsmoothed arithmetic integral exists almost everywhere for every `L2` input. -/
theorem ae_integrable (omega a : ℝ) (homega : 0 < omega) (f : IntervalL2 0 a) :
    ∀ᵐ x : ClosedInterval 0 a ∂volume,
      Integrable (fun y : ClosedInterval 0 a =>
        suzukiSourceHFinite omega ((x:ℝ)*(y:ℝ))*f y) := by
  by_cases ha : 1 < a
  · simpa only [profile_eq_source homega ha] using
      MultiplicativeHankel.operator_ae_integrable ha (profile omega a homega) f
  · apply Eventually.of_forall
    intro x
    simp only [source_zero_below_aperture (le_of_not_gt ha) x,zero_mul]
    exact integrable_zero _ ℂ volume

/-- The positive-shift operator is represented by the literal original kernel. -/
theorem operator_coeFn (omega a : ℝ) (homega : 0 < omega) (f : IntervalL2 0 a) :
    (operator omega a homega f : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      fun x => ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x:ℝ)*(y:ℝ))*f y := by
  by_cases ha : 1 < a
  · rw [operator,dif_pos ha]
    simpa only [profile_eq_source homega ha] using
      MultiplicativeHankel.operator_coeFn ha (profile omega a homega) f
  · rw [operator,dif_neg ha]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (ClosedInterval 0 a))] with x hx
    simp only [_root_.zero_apply,hx,source_zero_below_aperture (le_of_not_gt ha) x,
      zero_mul,integral_zero]
    rfl

/-- Unconditional compact admission of the complete arithmetic Hankel source at every
positive shift and every aperture. No meromorphic-inner or positivity premise is used. -/
theorem operator_isCompact (omega a : ℝ) (homega : 0 < omega) :
    IsCompactOperator (operator omega a homega) := by
  by_cases ha : 1 < a
  · rw [operator,dif_pos ha]
    exact MultiplicativeHankel.operator_isCompact ha (profile omega a homega)
  · rw [operator,dif_neg ha]
    exact isCompactOperator_zero

/-- The complete arithmetic source yields a self-adjoint operator throughout the
positive-shift domain, including all weak arithmetic cusps. -/
theorem operator_isSelfAdjoint (omega a : ℝ) (homega : 0 < omega) :
    IsSelfAdjoint (operator omega a homega) := by
  by_cases ha : 1 < a
  · rw [operator,dif_pos ha]
    exact MultiplicativeHankel.operator_isSelfAdjoint ha (profile omega a homega)
      (profile_conj omega a homega)
  · rw [operator,dif_neg ha]
    exact IsSelfAdjoint.zero _

/-- On the old admission domain, this is exactly the existing compressed Hankel operator. -/
theorem operator_eq_existing {omega a : ℝ} (homega : 1/2 < omega) (ha : 0 < a) :
    operator omega a (by linarith) = suzukiCompressedHankelOperator omega a homega := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (operator_coeFn omega a (by linarith) f).trans
    (suzukiCompressedHankelOperator_coeFn omega a homega ha f).symm

/-- The literal integral identifies the operator uniquely; the extended admission does
not introduce an independent choice of source or response. -/
theorem operator_unique (omega a : ℝ) (homega : 0 < omega)
    (T : IntervalL2 0 a →L[ℂ] IntervalL2 0 a)
    (hT : ∀ f : IntervalL2 0 a,
      (T f : ClosedInterval 0 a → ℂ) =ᵐ[volume]
        fun x => ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega ((x:ℝ)*(y:ℝ))*f y) :
    T=operator omega a homega := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hT f).trans (operator_coeFn omega a homega f).symm)

end
end RHTower.SuzukiPositiveShiftHankel
