import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemmaAd2Continuity

/-!
# The Suzuki Hankel kernel as an `L¹ → L²` smoothing operator

For `omega > 1`, Suzuki's literal arithmetic kernel is continuous on every compact physical
square, including the zero-product seam where it vanishes locally.  Currying the compact-square
kernel into `L∞` rows and applying Hölder gives the exact bounded map `L¹(0,B) → L²(0,B)` needed
to propagate aperture derivatives through the signed resolvent.  This avoids the false claim that
the moving sharp cutoff is differentiable as an `L²`-valued family.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

abbrev IntervalL1 (a b : ℝ) :=
  Lp ℂ 1 (volume : Measure (ClosedInterval a b))

/-- Suzuki's literal kernel, continuously realized on a compact physical square. -/
def suzukiHankelKernelContinuous
    (omega B : ℝ) (homega : 1 < omega) :
    C(ClosedInterval 0 B × ClosedInterval 0 B, ℂ) where
  toFun p := suzukiSourceHFinite omega ((p.1 : ℝ) * (p.2 : ℝ))
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro p
    let m : ClosedInterval 0 B × ClosedInterval 0 B → ℝ :=
      fun q => (q.1 : ℝ) * (q.2 : ℝ)
    have hm : Continuous m := by
      dsimp only [m]
      fun_prop
    have hmp0 : 0 ≤ m p := mul_nonneg p.1.property.1 p.2.property.1
    rcases hmp0.eq_or_lt with hmpZero | hmpPos
    · have hev : (fun q => suzukiSourceHFinite omega (m q)) =ᶠ[𝓝 p]
          fun _ => 0 := by
        have hsmall : ∀ᶠ q in 𝓝 p, m q < 1 :=
          hm.continuousAt (Iio_mem_nhds (by rw [← hmpZero]; norm_num))
        filter_upwards [hsmall] with q hq
        rw [suzukiSourceHFinite, if_neg (not_lt_of_ge hq.le)]
      exact continuousAt_const.congr_of_eventuallyEq (by simpa only [m] using hev)
    · exact (continuousAt_suzukiSourceHFinite homega hmpPos).comp
        hm.continuousAt

@[simp] theorem suzukiHankelKernelContinuous_apply
    (omega B : ℝ) (homega : 1 < omega)
    (p : ClosedInterval 0 B × ClosedInterval 0 B) :
    suzukiHankelKernelContinuous omega B homega p =
      suzukiSourceHFinite omega ((p.1 : ℝ) * (p.2 : ℝ)) := rfl

/-- Continuous family of `L∞` rows of Suzuki's compact-square kernel. -/
def suzukiHankelKernelRowsLInf
    (omega B : ℝ) (homega : 1 < omega) :
    C(ClosedInterval 0 B,
      Lp ℂ ∞ (volume : Measure (ClosedInterval 0 B))) where
  toFun x := ContinuousMap.toLp ∞ volume ℂ
    ((suzukiHankelKernelContinuous omega B homega).curry x)
  continuous_toFun :=
    (ContinuousMap.toLp ∞ volume ℂ).continuous.comp
      (suzukiHankelKernelContinuous omega B homega).curry.continuous

theorem suzukiHankelKernelRowsLInf_ae
    (omega B : ℝ) (homega : 1 < omega)
    (x : ClosedInterval 0 B) :
    (suzukiHankelKernelRowsLInf omega B homega x :
        ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun y => suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) := by
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (∞ : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 B)))
    ((suzukiHankelKernelContinuous omega B homega).curry x)] with y hy
  exact hy

/-- Point evaluation after applying Suzuki's kernel to an `L¹` input. -/
def suzukiHankelL1FunctionalContinuous
    (omega B : ℝ) (homega : 1 < omega) :
    C(ClosedInterval 0 B, IntervalL1 0 B →L[ℂ] ℂ) where
  toFun x := (complexMulBilinear.lpPairing volume ∞ 1)
    (suzukiHankelKernelRowsLInf omega B homega x)
  continuous_toFun :=
    (complexMulBilinear.lpPairing volume ∞ 1).continuous.comp
      (suzukiHankelKernelRowsLInf omega B homega).continuous

def suzukiHankelL1FunctionalField
    (omega B : ℝ) (homega : 1 < omega) :
    Lp (IntervalL1 0 B →L[ℂ] ℂ) 2
      (volume : Measure (ClosedInterval 0 B)) :=
  ContinuousMap.toLp 2 volume ℂ
    (suzukiHankelL1FunctionalContinuous omega B homega)

/-- The literal compact Suzuki Hankel kernel as a bounded smoothing map `L¹(0,B) → L²(0,B)`. -/
def suzukiCompressedHankelL1ToL2
    (omega B : ℝ) (homega : 1 < omega) :
    IntervalL1 0 B →L[ℂ] IntervalL2 0 B :=
  kernelOperator (volume : Measure (ClosedInterval 0 B))
    (suzukiHankelL1FunctionalField omega B homega)

/-- The smoothing map is exactly integration against Suzuki's literal kernel. -/
theorem suzukiCompressedHankelL1ToL2_coeFn
    (omega B : ℝ) (homega : 1 < omega)
    (f : IntervalL1 0 B) :
    (suzukiCompressedHankelL1ToL2 omega B homega f :
        ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun x => ∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume := by
  filter_upwards [
    (evalBilinear (𝕜 := ℂ) (E := IntervalL1 0 B)).coeFn_holder
      (r := (2 : ENNReal))
      (suzukiHankelL1FunctionalField omega B homega)
      (Lp.const ∞ (volume : Measure (ClosedInterval 0 B)) f),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval 0 B)))
      (suzukiHankelL1FunctionalContinuous omega B homega),
    Lp.coeFn_const (p := ∞) (volume : Measure (ClosedInterval 0 B)) f
  ] with x hholder hfield hconst
  rw [suzukiCompressedHankelL1ToL2, kernelOperator, kernelOperatorMap_apply,
    hholder, suzukiHankelL1FunctionalField, hfield, hconst]
  change (complexMulBilinear.lpPairing volume ∞ 1
    (suzukiHankelKernelRowsLInf omega B homega x)) f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [suzukiHankelKernelRowsLInf_ae omega B homega x] with y hy
  rw [hy]
  simp [complexMulBilinear]

/-- Canonical finite-measure inclusion of an interval `L²` class into interval `L¹`. -/
def suzukiIntervalL2AsL1 (B : ℝ) (f : IntervalL2 0 B) : IntervalL1 0 B :=
  ((Lp.memLp f).mono_exponent (by norm_num)).toLp f

theorem suzukiIntervalL2AsL1_ae (B : ℝ) (f : IntervalL2 0 B) :
    (suzukiIntervalL2AsL1 B f : ClosedInterval 0 B → ℂ) =ᵐ[volume] f :=
  ((Lp.memLp f).mono_exponent (by norm_num)).coeFn_toLp

/-- On `L²` inputs, the smoothing realization is exactly the existing compressed Hankel
operator, so the new `L¹` route does not define a proxy kernel. -/
theorem suzukiCompressedHankelL1ToL2_asL1
    (omega B : ℝ) (homega : 1 < omega) (hB : 1 < B)
    (f : IntervalL2 0 B) :
    suzukiCompressedHankelL1ToL2 omega B homega
        (suzukiIntervalL2AsL1 B f) =
      suzukiCompressedHankelOperator omega B (by linarith) f := by
  apply Lp.ext
  filter_upwards [suzukiCompressedHankelL1ToL2_coeFn omega B homega
      (suzukiIntervalL2AsL1 B f),
    suzukiCompressedHankelOperator_coeFn omega B (by linarith) (by linarith) f]
      with x hL1 hL2
  rw [hL1, hL2]
  apply integral_congr_ae
  filter_upwards [suzukiIntervalL2AsL1_ae B f] with y hy
  rw [hy]

end RHTower
