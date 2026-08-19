import GaloisForLFunctions.RHTower.SuzukiTaCovarianceReflection
import GaloisForLFunctions.RHTower.SuzukiCoalescingTangentGeneral
import GaloisForLFunctions.HTGeometry.L2DerivativeFourier

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform LinearPMap
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem suzukiApertureMonomialC_zero_eq_exponential_zero
    (a : SuzukiPositiveAperture) :
    (suzukiApertureCoordinate a.2.le).monomialC 0 =
      suzukiTaExponentialL2 a 0 := by
  apply Lp.ext
  filter_upwards [
    (suzukiApertureCoordinate a.2.le).coeFn_monomialC 0,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaExponentialContinuous a 0)] with x hmono hexp
  change ((suzukiApertureCoordinate a.2.le).monomialC 0 :
      SuzukiApertureInterval a.1 → ℂ) x =
    (suzukiTaExponentialL2 a 0 : SuzukiApertureInterval a.1 → ℂ) x
  rw [hmono]
  change ((suzukiApertureCoordinate a.2.le).coord x : ℂ) ^ 0 =
    ((ContinuousMap.toLp 2 volume ℂ) (suzukiTaExponentialContinuous a 0) :
      SuzukiApertureInterval a.1 → ℂ) x
  rw [hexp]
  simp [suzukiTaExponentialContinuous]

theorem suzukiApertureCoshVecC_ae
    (a : SuzukiPositiveAperture) (c : ℝ) :
    ((suzukiApertureCoordinate a.2.le).coshVecC c :
        SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume]
      fun x => (Real.cosh (c * (x : ℝ)) : ℂ) := by
  let B := suzukiApertureCoordinate a.2.le
  change (GaloisForLFunctions.HTGeometry.ofRealLp (B.coshVec c) :
      SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume] _
  filter_upwards [
      GaloisForLFunctions.HTGeometry.coeFn_ofRealLp (B.coshVec c),
      B.coeFn_coshVec c] with x hcomplex hreal
  rw [hcomplex, hreal]
  simp [B]

theorem suzukiApertureSinhVecC_ae
    (a : SuzukiPositiveAperture) (c : ℝ) :
    ((suzukiApertureCoordinate a.2.le).sinhVecC c :
        SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume]
      fun x => (Real.sinh (c * (x : ℝ)) : ℂ) := by
  let B := suzukiApertureCoordinate a.2.le
  change (GaloisForLFunctions.HTGeometry.ofRealLp (B.sinhVec c) :
      SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume] _
  filter_upwards [
      GaloisForLFunctions.HTGeometry.coeFn_ofRealLp (B.sinhVec c),
      B.coeFn_sinhVec c] with x hcomplex hreal
  rw [hcomplex, hreal]
  simp [B]

/-- The movable exponential source is exactly its even plus odd hyperbolic
parts on Suzuki's literal interval. -/
theorem suzukiTaExponentialL2_eq_cosh_add_sinh
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiTaExponentialL2 a c =
      (suzukiApertureCoordinate a.2.le).coshVecC c +
        (suzukiApertureCoordinate a.2.le).sinhVecC c := by
  apply Lp.ext
  filter_upwards [
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
        (suzukiTaExponentialContinuous a c),
      suzukiApertureCoshVecC_ae a c,
      suzukiApertureSinhVecC_ae a c,
      Lp.coeFn_add
        ((suzukiApertureCoordinate a.2.le).coshVecC c)
        ((suzukiApertureCoordinate a.2.le).sinhVecC c)] with
      x hexp hcosh hsinh hadd
  rw [show (suzukiTaExponentialL2 a c : SuzukiApertureInterval a.1 → ℂ) x =
      (Real.exp (c * (x : ℝ)) : ℂ) by
        simpa [suzukiTaExponentialL2, suzukiTaExponentialContinuous] using hexp,
    hadd, Pi.add_apply, hcosh, hsinh]
  norm_cast
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- Reflection of the movable exponential is exactly even minus odd. -/
theorem suzukiTaExponentialL2_neg_eq_cosh_sub_sinh
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiTaExponentialL2 a (-c) =
      (suzukiApertureCoordinate a.2.le).coshVecC c -
        (suzukiApertureCoordinate a.2.le).sinhVecC c := by
  apply Lp.ext
  filter_upwards [
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
        (suzukiTaExponentialContinuous a (-c)),
      suzukiApertureCoshVecC_ae a c,
      suzukiApertureSinhVecC_ae a c,
      Lp.coeFn_sub
        ((suzukiApertureCoordinate a.2.le).coshVecC c)
        ((suzukiApertureCoordinate a.2.le).sinhVecC c)] with
      x hexp hcosh hsinh hsub
  rw [show (suzukiTaExponentialL2 a (-c) : SuzukiApertureInterval a.1 → ℂ) x =
      (Real.exp ((-c) * (x : ℝ)) : ℂ) by
        simpa [suzukiTaExponentialL2, suzukiTaExponentialContinuous] using hexp,
    hsub, Pi.sub_apply, hcosh, hsinh]
  norm_cast
  have hneg : (-c) * (x : ℝ) = -(c * (x : ℝ)) := by ring
  rw [hneg, Real.cosh_eq, Real.sinh_eq]
  ring

/-- Even part of the actual movable raw deficiency. -/
def suzukiTaRawCoalescingEven
    (a : SuzukiPositiveAperture) (c : ℝ) : SuzukiTaHilbert a :=
  (2 : ℂ)⁻¹ • (suzukiTaRawDeficiency a c + suzukiTaRawDeficiency a (-c))

/-- Odd part of the actual movable raw deficiency. -/
def suzukiTaRawCoalescingOdd
    (a : SuzukiPositiveAperture) (c : ℝ) : SuzukiTaHilbert a :=
  (2 : ℂ)⁻¹ • (suzukiTaRawDeficiency a c - suzukiTaRawDeficiency a (-c))

/-- Actual even covariance energy of Suzuki's movable exponential anchor. -/
def suzukiTaCoalescingEvenEnergy
    (a : SuzukiPositiveAperture) (c : ℝ) : ℝ :=
  coalescingEvenEnergy (suzukiApertureCoordinate a.2.le)
    (suzukiWeilIntervalCovariance a) c

/-- Actual odd covariance energy of Suzuki's movable exponential anchor. -/
def suzukiTaCoalescingOddEnergy
    (a : SuzukiPositiveAperture) (c : ℝ) : ℝ :=
  coalescingOddEnergy (suzukiApertureCoordinate a.2.le)
    (suzukiWeilIntervalCovariance a) c

theorem suzukiTaPhysicalEmbedding_rawCoalescingEven
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiTaPhysicalEmbedding a (suzukiTaRawCoalescingEven a c) =
      suzukiWeilIntervalCovariance a
        ((suzukiApertureCoordinate a.2.le).coshVecC c) := by
  rw [suzukiTaRawCoalescingEven, map_smul, map_add,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
    ← map_add, suzukiTaExponentialL2_eq_cosh_add_sinh,
    suzukiTaExponentialL2_neg_eq_cosh_sub_sinh]
  norm_num
  module

theorem suzukiTaPhysicalEmbedding_rawCoalescingOdd
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiTaPhysicalEmbedding a (suzukiTaRawCoalescingOdd a c) =
      suzukiWeilIntervalCovariance a
        ((suzukiApertureCoordinate a.2.le).sinhVecC c) := by
  rw [suzukiTaRawCoalescingOdd, map_smul, map_sub,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
    ← map_sub, suzukiTaExponentialL2_eq_cosh_add_sinh,
    suzukiTaExponentialL2_neg_eq_cosh_sub_sinh]
  norm_num
  module

theorem suzukiTaRawCoalescingEven_inner
    (a : SuzukiPositiveAperture) (c : ℝ) (w : SuzukiTaHilbert a) :
    inner ℂ (suzukiTaRawCoalescingEven a c) w =
      inner ℂ ((suzukiApertureCoordinate a.2.le).coshVecC c)
        (suzukiTaPhysicalEmbedding a w) := by
  rw [suzukiTaRawCoalescingEven, inner_smul_left, inner_add_left,
    suzukiTaRawDeficiency_inner, suzukiTaRawDeficiency_inner,
    suzukiTaMoment, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    suzukiTaMoment, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    suzukiTaExponentialL2_eq_cosh_add_sinh,
    suzukiTaExponentialL2_neg_eq_cosh_sub_sinh,
    inner_add_left, inner_sub_left]
  have hstarTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using Complex.conj_ofNat 2
  rw [map_inv₀, hstarTwo]
  norm_num
  ring_nf

theorem suzukiTaRawCoalescingOdd_inner
    (a : SuzukiPositiveAperture) (c : ℝ) (w : SuzukiTaHilbert a) :
    inner ℂ (suzukiTaRawCoalescingOdd a c) w =
      inner ℂ ((suzukiApertureCoordinate a.2.le).sinhVecC c)
        (suzukiTaPhysicalEmbedding a w) := by
  rw [suzukiTaRawCoalescingOdd, inner_smul_left, inner_sub_left,
    suzukiTaRawDeficiency_inner, suzukiTaRawDeficiency_inner,
    suzukiTaMoment, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    suzukiTaMoment, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    suzukiTaExponentialL2_eq_cosh_add_sinh,
    suzukiTaExponentialL2_neg_eq_cosh_sub_sinh,
    inner_add_left, inner_sub_left]
  have hstarTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using Complex.conj_ofNat 2
  rw [map_inv₀, hstarTwo]
  norm_num
  ring_nf

/-- The abstract-looking even covariance energy is exactly the squared norm
of the even part of Suzuki's actual raw deficiency. -/
theorem suzukiTaCoalescingEvenEnergy_eq_norm_sq
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiTaCoalescingEvenEnergy a c =
      ‖suzukiTaRawCoalescingEven a c‖ ^ 2 := by
  rw [suzukiTaCoalescingEvenEnergy, coalescingEvenEnergy,
    ← suzukiTaPhysicalEmbedding_rawCoalescingEven a c,
    ← suzukiTaRawCoalescingEven_inner a c,
    inner_self_eq_norm_sq_to_K]
  rw [pow_two, Complex.mul_re]
  simp
  ring

/-- The odd covariance energy is exactly the squared norm of the odd part of
Suzuki's actual raw deficiency. -/
theorem suzukiTaCoalescingOddEnergy_eq_norm_sq
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiTaCoalescingOddEnergy a c =
      ‖suzukiTaRawCoalescingOdd a c‖ ^ 2 := by
  rw [suzukiTaCoalescingOddEnergy, coalescingOddEnergy,
    ← suzukiTaPhysicalEmbedding_rawCoalescingOdd a c,
    ← suzukiTaRawCoalescingOdd_inner a c,
    inner_self_eq_norm_sq_to_K]
  rw [pow_two, Complex.mul_re]
  simp
  ring

/-- Literal position-to-constant resolvent quotient of Suzuki's completed
prime--polar--Gamma covariance. -/
def suzukiTaPositionResolventTangent
    (a : SuzukiPositiveAperture) : ℝ :=
  positionResolventTangent (suzukiApertureCoordinate a.2.le)
    (suzukiWeilIntervalCovariance a)

theorem suzukiTaCovariance_constant_energy_pos
    (a : SuzukiPositiveAperture) :
    0 < (inner ℂ
      ((suzukiApertureCoordinate a.2.le).monomialC 0)
      (suzukiWeilIntervalCovariance a
        ((suzukiApertureCoordinate a.2.le).monomialC 0)) : ℂ).re := by
  let v := suzukiTaRawDeficiency a 0
  have hv : v ≠ 0 := suzukiTaRawDeficiency_ne_zero a 0
  have hnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hinner :
      inner ℂ v v =
        inner ℂ (suzukiTaExponentialL2 a 0)
          (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a 0)) := by
    rw [suzukiTaRawDeficiency_inner, suzukiTaMoment,
      ContinuousLinearMap.comp_apply,
      suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
      innerSL_apply_apply]
  have hre := congrArg Complex.re hinner
  rw [inner_self_eq_norm_sq_to_K] at hre
  rw [suzukiApertureMonomialC_zero_eq_exponential_zero]
  rw [← hre]
  have hpow_re : ((↑‖v‖ : ℂ) ^ 2).re = ‖v‖ ^ 2 := by
    rw [pow_two, Complex.mul_re]
    simp
    ring
  calc
    0 < ‖v‖ ^ 2 := hnorm
    _ = ((↑‖v‖ : ℂ) ^ 2).re := hpow_re.symm

/-- Positivity of Suzuki's completed covariance forces the source-faithful
coalescing rate to have the physically correct sign. -/
theorem suzukiTaPositionResolventTangent_nonneg
    (a : SuzukiPositiveAperture) :
    0 ≤ suzukiTaPositionResolventTangent a := by
  rw [suzukiTaPositionResolventTangent, positionResolventTangent]
  exact div_nonneg
    ((suzukiWeilIntervalCovariance_isPositive a).re_inner_nonneg_right _)
    (le_of_lt (suzukiTaCovariance_constant_energy_pos a))

/-- Actual Suzuki covariance has the model-free coalescing tangent, with no
unrealized operator premise left. -/
theorem tendsto_one_sub_suzukiTaCoalescingDefect_rate
    (a : SuzukiPositiveAperture) :
    Tendsto (fun c : ℝ =>
        (1 - GaloisForLFunctions.RHTower.suzukiDefectAngle
          (suzukiTaCoalescingEvenEnergy a c)
          (suzukiTaCoalescingOddEnergy a c)) / (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (suzukiTaPositionResolventTangent a)) := by
  exact tendsto_one_sub_coalescingDefect_rate
    (suzukiApertureCoordinate a.2.le)
    (suzukiWeilIntervalCovariance a)
    (suzukiTaCovariance_constant_energy_pos a)

end RHTower
