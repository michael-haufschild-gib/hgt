import GaloisForLFunctions.RHTower.Suzuki.SuzukiAperturePositionOperator
import GaloisForLFunctions.RHTower.Suzuki.SuzukiH01OperatorDomain

/-!
# Boundary-renormalized hyperbolic form lifts

Literal position-weighted parity probes do not lie in Suzuki's zero-boundary core. Two forced
endpoint counterterms repair this exactly:

* `x sinh x - a tanh(a) cosh x`;
* `x cosh x - a coth(a) sinh x`.

Both are exact interval primitives, hence belong to Connes--Consani's completed
prime--polar--Gamma form domain. Unequal coefficients retain boundary anomaly instead of hiding it
in an abstract domain premise.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

def suzukiTaV2EvenBoundaryCoefficient (a : SuzukiPositiveAperture) : ℝ :=
  a.1 * Real.tanh a.1

def suzukiTaV2EvenBoundaryDerivativeContinuous (a : SuzukiPositiveAperture) :
    C(SuzukiApertureInterval a.1, ℂ) where
  toFun x :=
    ((x.1 * Real.cosh x.1 +
      (1 - suzukiTaV2EvenBoundaryCoefficient a) * Real.sinh x.1 : ℝ) : ℂ)
  continuous_toFun := by fun_prop

def suzukiTaV2EvenBoundaryDerivative (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 :=
  ContinuousMap.toLp 2 volume ℂ (suzukiTaV2EvenBoundaryDerivativeContinuous a)

def suzukiTaV2EvenBoundaryContinuous (a : SuzukiPositiveAperture) :
    C(SuzukiApertureInterval a.1, ℂ) where
  toFun x :=
    ((x.1 * Real.sinh x.1 -
      suzukiTaV2EvenBoundaryCoefficient a * Real.cosh x.1 : ℝ) : ℂ)
  continuous_toFun := by fun_prop

def suzukiTaV2EvenBoundary (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 :=
  ContinuousMap.toLp 2 volume ℂ (suzukiTaV2EvenBoundaryContinuous a)

theorem suzukiTaV2EvenBoundary_lower (a : SuzukiPositiveAperture) :
    suzukiTaV2EvenBoundaryContinuous a ⟨-a.1, by constructor <;> linarith [a.2]⟩ = 0 := by
  simp only [suzukiTaV2EvenBoundaryContinuous, suzukiTaV2EvenBoundaryCoefficient,
    ContinuousMap.coe_mk]
  rw [Real.sinh_neg, Real.cosh_neg, Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh a.1 ≠ 0 := ne_of_gt (Real.cosh_pos a.1)
  field_simp [hc]
  norm_num

theorem hasDerivAt_suzukiTaV2EvenBoundary (a : SuzukiPositiveAperture) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ((y * Real.sinh y -
        suzukiTaV2EvenBoundaryCoefficient a * Real.cosh y : ℝ) : ℂ))
      ((x * Real.cosh x +
        (1 - suzukiTaV2EvenBoundaryCoefficient a) * Real.sinh x : ℝ) : ℂ) x := by
  convert (((hasDerivAt_id x).mul (Real.hasDerivAt_sinh x)).sub
    ((Real.hasDerivAt_cosh x).const_mul
      (suzukiTaV2EvenBoundaryCoefficient a))).ofReal_comp using 1 <;>
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq, one_mul, Complex.ofReal_sub] <;>
    push_cast <;> ring

theorem suzukiTaV2EvenBoundary_primitive (a : SuzukiPositiveAperture) :
    suzukiAperturePrimitive a.1 (suzukiTaV2EvenBoundaryDerivative a) =
      suzukiTaV2EvenBoundary a := by
  apply Lp.ext
  filter_upwards [suzukiAperturePrimitive_coeFn a.1 (suzukiTaV2EvenBoundaryDerivative a),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaV2EvenBoundaryContinuous a)] with t hprim hboundary
  rw [hprim, suzukiAperturePrefix_eq_intervalIntegral a]
  change _ = ((ContinuousMap.toLp 2 volume ℂ
    (suzukiTaV2EvenBoundaryContinuous a) : SuzukiApertureIntervalL2 a.1) t)
  rw [hboundary]
  have hderiv :
      ∀ᵐ x ∂volume.restrict (Icc (-a.1) a.1),
        suzukiApertureZeroExtend (suzukiTaV2EvenBoundaryDerivative a) x =
          ((x * Real.cosh x +
            (1 - suzukiTaV2EvenBoundaryCoefficient a) * Real.sinh x : ℝ) : ℂ) := by
    rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [suzukiApertureRepresentative_ae (suzukiTaV2EvenBoundaryDerivative a),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
        (suzukiTaV2EvenBoundaryDerivativeContinuous a)] with x hx hdx
    rw [suzukiApertureZeroExtend_apply, hx]
    change ((ContinuousMap.toLp 2 volume ℂ
      (suzukiTaV2EvenBoundaryDerivativeContinuous a) : SuzukiApertureIntervalL2 a.1) x) = _
    rw [hdx]
    rfl
  have hsub : uIoc (-a.1) (t : ℝ) ⊆ Icc (-a.1) a.1 := by
    rw [uIoc_of_le t.2.1]
    intro x hx
    exact ⟨hx.1.le, le_trans hx.2 t.2.2⟩
  have hderivU :
      ∀ᵐ x ∂volume.restrict (uIoc (-a.1) (t : ℝ)),
        suzukiApertureZeroExtend (suzukiTaV2EvenBoundaryDerivative a) x =
          ((x * Real.cosh x +
            (1 - suzukiTaV2EvenBoundaryCoefficient a) * Real.sinh x : ℝ) : ℂ) :=
    hderiv.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
  rw [intervalIntegral.integral_congr_ae
    (MeasureTheory.ae_imp_of_ae_restrict hderivU)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_suzukiTaV2EvenBoundary a x)]
  · change ((t.1 * Real.sinh t.1 -
        suzukiTaV2EvenBoundaryCoefficient a * Real.cosh t.1 : ℝ) : ℂ) -
      (((-a.1) * Real.sinh (-a.1) -
        suzukiTaV2EvenBoundaryCoefficient a * Real.cosh (-a.1) : ℝ) : ℂ) = _
    have hlower : (-a.1) * Real.sinh (-a.1) -
        suzukiTaV2EvenBoundaryCoefficient a * Real.cosh (-a.1) = 0 := by
      simpa only [suzukiTaV2EvenBoundaryContinuous, ContinuousMap.coe_mk,
        Complex.ofReal_eq_zero] using suzukiTaV2EvenBoundary_lower a
    rw [hlower, Complex.ofReal_zero, sub_zero]
    rfl
  · exact (Complex.continuous_ofReal.comp
      ((continuous_id.mul Real.continuous_cosh).add
        (continuous_const.mul Real.continuous_sinh))).intervalIntegrable _ _

def suzukiTaV2OddBoundaryCoefficient (a : SuzukiPositiveAperture) : ℝ :=
  a.1 * Real.cosh a.1 / Real.sinh a.1

def suzukiTaV2OddBoundaryDerivativeContinuous (a : SuzukiPositiveAperture) :
    C(SuzukiApertureInterval a.1, ℂ) where
  toFun x :=
    ((x.1 * Real.sinh x.1 +
      (1 - suzukiTaV2OddBoundaryCoefficient a) * Real.cosh x.1 : ℝ) : ℂ)
  continuous_toFun := by fun_prop

def suzukiTaV2OddBoundaryDerivative (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 :=
  ContinuousMap.toLp 2 volume ℂ (suzukiTaV2OddBoundaryDerivativeContinuous a)

def suzukiTaV2OddBoundaryContinuous (a : SuzukiPositiveAperture) :
    C(SuzukiApertureInterval a.1, ℂ) where
  toFun x :=
    ((x.1 * Real.cosh x.1 -
      suzukiTaV2OddBoundaryCoefficient a * Real.sinh x.1 : ℝ) : ℂ)
  continuous_toFun := by fun_prop

def suzukiTaV2OddBoundary (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 :=
  ContinuousMap.toLp 2 volume ℂ (suzukiTaV2OddBoundaryContinuous a)

theorem suzukiTaV2OddBoundary_lower (a : SuzukiPositiveAperture) :
    suzukiTaV2OddBoundaryContinuous a ⟨-a.1, by constructor <;> linarith [a.2]⟩ = 0 := by
  simp only [suzukiTaV2OddBoundaryContinuous, suzukiTaV2OddBoundaryCoefficient,
    ContinuousMap.coe_mk]
  rw [Real.sinh_neg, Real.cosh_neg]
  have hs : Real.sinh a.1 ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr a.2)
  field_simp [hs]
  norm_num

theorem hasDerivAt_suzukiTaV2OddBoundary (a : SuzukiPositiveAperture) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ((y * Real.cosh y -
        suzukiTaV2OddBoundaryCoefficient a * Real.sinh y : ℝ) : ℂ))
      ((x * Real.sinh x +
        (1 - suzukiTaV2OddBoundaryCoefficient a) * Real.cosh x : ℝ) : ℂ) x := by
  convert (((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
    ((Real.hasDerivAt_sinh x).const_mul
      (suzukiTaV2OddBoundaryCoefficient a))).ofReal_comp using 1 <;>
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq, one_mul, Complex.ofReal_sub] <;>
    push_cast <;> ring

theorem suzukiTaV2OddBoundary_primitive (a : SuzukiPositiveAperture) :
    suzukiAperturePrimitive a.1 (suzukiTaV2OddBoundaryDerivative a) =
      suzukiTaV2OddBoundary a := by
  apply Lp.ext
  filter_upwards [suzukiAperturePrimitive_coeFn a.1 (suzukiTaV2OddBoundaryDerivative a),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaV2OddBoundaryContinuous a)] with t hprim hboundary
  rw [hprim, suzukiAperturePrefix_eq_intervalIntegral a]
  change _ = ((ContinuousMap.toLp 2 volume ℂ
    (suzukiTaV2OddBoundaryContinuous a) : SuzukiApertureIntervalL2 a.1) t)
  rw [hboundary]
  have hderiv :
      ∀ᵐ x ∂volume.restrict (Icc (-a.1) a.1),
        suzukiApertureZeroExtend (suzukiTaV2OddBoundaryDerivative a) x =
          ((x * Real.sinh x +
            (1 - suzukiTaV2OddBoundaryCoefficient a) * Real.cosh x : ℝ) : ℂ) := by
    rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [suzukiApertureRepresentative_ae (suzukiTaV2OddBoundaryDerivative a),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
        (suzukiTaV2OddBoundaryDerivativeContinuous a)] with x hx hdx
    rw [suzukiApertureZeroExtend_apply, hx]
    change ((ContinuousMap.toLp 2 volume ℂ
      (suzukiTaV2OddBoundaryDerivativeContinuous a) : SuzukiApertureIntervalL2 a.1) x) = _
    rw [hdx]
    rfl
  have hsub : uIoc (-a.1) (t : ℝ) ⊆ Icc (-a.1) a.1 := by
    rw [uIoc_of_le t.2.1]
    intro x hx
    exact ⟨hx.1.le, le_trans hx.2 t.2.2⟩
  have hderivU :
      ∀ᵐ x ∂volume.restrict (uIoc (-a.1) (t : ℝ)),
        suzukiApertureZeroExtend (suzukiTaV2OddBoundaryDerivative a) x =
          ((x * Real.sinh x +
            (1 - suzukiTaV2OddBoundaryCoefficient a) * Real.cosh x : ℝ) : ℂ) :=
    hderiv.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
  rw [intervalIntegral.integral_congr_ae
    (MeasureTheory.ae_imp_of_ae_restrict hderivU)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_suzukiTaV2OddBoundary a x)]
  · change ((t.1 * Real.cosh t.1 -
        suzukiTaV2OddBoundaryCoefficient a * Real.sinh t.1 : ℝ) : ℂ) -
      (((-a.1) * Real.cosh (-a.1) -
        suzukiTaV2OddBoundaryCoefficient a * Real.sinh (-a.1) : ℝ) : ℂ) = _
    have hlower : (-a.1) * Real.cosh (-a.1) -
        suzukiTaV2OddBoundaryCoefficient a * Real.sinh (-a.1) = 0 := by
      simpa only [suzukiTaV2OddBoundaryContinuous, ContinuousMap.coe_mk,
        Complex.ofReal_eq_zero] using suzukiTaV2OddBoundary_lower a
    rw [hlower, Complex.ofReal_zero, sub_zero]
    rfl
  · exact (Complex.continuous_ofReal.comp
      ((continuous_id.mul Real.continuous_sinh).add
        (continuous_const.mul Real.continuous_cosh))).intervalIntegrable _ _

theorem suzukiApertureCoordinate_coshVecC_one_ae (a : SuzukiPositiveAperture) :
    (((suzukiApertureCoordinate a.2.le).coshVecC 1 :
      SuzukiApertureInterval a.1 → ℂ)) =ᵐ[volume]
      fun x => (Real.cosh x.1 : ℂ) := by
  let B := suzukiApertureCoordinate a.2.le
  have hc := ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM (B.coshVec 1)
  have hr := B.coeFn_coshVec 1
  change (B.coshVecC 1 : SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume] _
  change (Complex.ofRealCLM.compLpL 2 volume (B.coshVec 1) :
    SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume] _
  filter_upwards [hc, hr] with x hx hrx
  rw [hx, hrx]
  simp [B]

theorem suzukiApertureCoordinate_sinhVecC_one_ae (a : SuzukiPositiveAperture) :
    (((suzukiApertureCoordinate a.2.le).sinhVecC 1 :
      SuzukiApertureInterval a.1 → ℂ)) =ᵐ[volume]
      fun x => (Real.sinh x.1 : ℂ) := by
  let B := suzukiApertureCoordinate a.2.le
  have hc := ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM (B.sinhVec 1)
  have hr := B.coeFn_sinhVec 1
  change (B.sinhVecC 1 : SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume] _
  change (Complex.ofRealCLM.compLpL 2 volume (B.sinhVec 1) :
    SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume] _
  filter_upwards [hc, hr] with x hx hrx
  rw [hx, hrx]
  simp [B]

theorem suzukiTaV2EvenBoundary_eq_position (a : SuzukiPositiveAperture) :
    suzukiTaV2EvenBoundary a =
      suzukiAperturePosition a
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1) -
        (suzukiTaV2EvenBoundaryCoefficient a : ℂ) •
          ((suzukiApertureCoordinate a.2.le).coshVecC 1) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaV2EvenBoundaryContinuous a),
    suzukiAperturePosition_ae a
      ((suzukiApertureCoordinate a.2.le).sinhVecC 1),
    suzukiApertureCoordinate_sinhVecC_one_ae a, suzukiApertureCoordinate_coshVecC_one_ae a,
    Lp.coeFn_sub
      (suzukiAperturePosition a
        ((suzukiApertureCoordinate a.2.le).sinhVecC 1))
      ((suzukiTaV2EvenBoundaryCoefficient a : ℂ) •
        ((suzukiApertureCoordinate a.2.le).coshVecC 1)),
    Lp.coeFn_smul (suzukiTaV2EvenBoundaryCoefficient a : ℂ)
      ((suzukiApertureCoordinate a.2.le).coshVecC 1)] with x hb hp hs hc hsub hsmul
  change ((ContinuousMap.toLp 2 volume ℂ
    (suzukiTaV2EvenBoundaryContinuous a) : SuzukiApertureIntervalL2 a.1) x) = _
  rw [hb, hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hp, hs, hc]
  simp only [suzukiTaV2EvenBoundaryContinuous, ContinuousMap.coe_mk]
  push_cast
  ring

theorem suzukiTaV2OddBoundary_eq_position (a : SuzukiPositiveAperture) :
    suzukiTaV2OddBoundary a =
      suzukiAperturePosition a
          ((suzukiApertureCoordinate a.2.le).coshVecC 1) -
        (suzukiTaV2OddBoundaryCoefficient a : ℂ) •
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaV2OddBoundaryContinuous a),
    suzukiAperturePosition_ae a
      ((suzukiApertureCoordinate a.2.le).coshVecC 1),
    suzukiApertureCoordinate_coshVecC_one_ae a, suzukiApertureCoordinate_sinhVecC_one_ae a,
    Lp.coeFn_sub
      (suzukiAperturePosition a
        ((suzukiApertureCoordinate a.2.le).coshVecC 1))
      ((suzukiTaV2OddBoundaryCoefficient a : ℂ) •
        ((suzukiApertureCoordinate a.2.le).sinhVecC 1)),
    Lp.coeFn_smul (suzukiTaV2OddBoundaryCoefficient a : ℂ)
      ((suzukiApertureCoordinate a.2.le).sinhVecC 1)] with x hb hp hc hs hsub hsmul
  change ((ContinuousMap.toLp 2 volume ℂ
    (suzukiTaV2OddBoundaryContinuous a) : SuzukiApertureIntervalL2 a.1) x) = _
  rw [hb, hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hp, hc, hs]
  simp only [suzukiTaV2OddBoundaryContinuous, ContinuousMap.coe_mk]
  push_cast
  ring

/-- Completed source-form lift of the even boundary-renormalized position probe. -/
def suzukiTaV2EvenBoundaryFormVector (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a :=
  suzukiAperturePrimitiveCCMFormVector a
    (suzukiTaV2EvenBoundaryDerivative a)

/-- Completed source-form lift of the odd boundary-renormalized position probe. -/
def suzukiTaV2OddBoundaryFormVector (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a :=
  suzukiAperturePrimitiveCCMFormVector a
    (suzukiTaV2OddBoundaryDerivative a)

theorem suzukiWeilIntervalFormEmbedding_evenBoundaryFormVector
    (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalFormEmbedding a
        (suzukiTaV2EvenBoundaryFormVector a) =
      suzukiTaV2EvenBoundary a := by
  rw [suzukiTaV2EvenBoundaryFormVector,
    suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector,
    suzukiTaV2EvenBoundary_primitive]

theorem suzukiWeilIntervalFormEmbedding_oddBoundaryFormVector
    (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalFormEmbedding a
        (suzukiTaV2OddBoundaryFormVector a) =
      suzukiTaV2OddBoundary a := by
  rw [suzukiTaV2OddBoundaryFormVector,
    suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector,
    suzukiTaV2OddBoundary_primitive]

end RHTower
