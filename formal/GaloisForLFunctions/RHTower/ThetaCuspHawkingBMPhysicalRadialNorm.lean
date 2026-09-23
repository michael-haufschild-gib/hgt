import GaloisForLFunctions.HTGeometry.HalfOrderBetaFinitePart
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceHorizonModeLimits
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalTimeActionContinuation

/-! The original fundamental-mode norm in tortoise coordinates and its forced horizon finite part. -/
namespace RHTower.D4BMFundamentalNorm
open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The original elementary fundamental mode, before integrating its bilinear square. -/
def mode (w : ℂ) (t : ℝ) : ℂ :=
  power (w/2) (horizonCoordinate t)*power (1/2) (1-horizonCoordinate t)

theorem mode_square (w : ℂ) (t : ℝ) (ht : t < 0) :
    mode w t^(2 : ℕ)=(horizonCoordinate t:ℂ)^w*(radialUnit t:ℂ)^(2 : ℕ) := by
  have hz := horizonCoordinate_interior t ht
  have hs : Real.sqrt (1-horizonCoordinate t)=radialUnit t := by
    rw [horizonCoordinate,sub_sub_cancel,Real.sqrt_sq (radialUnit_bounds t ht).1.le]
  have hp : power (w/2) (horizonCoordinate t)^(2 : ℕ)=(horizonCoordinate t:ℂ)^w := by
    rw [power,pow_two,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)),
      show w/2+w/2=w by ring]
  rw [mode,mul_pow,hp,power_half_eq_sqrt (sub_nonneg.mpr hz.2.le),hs]

private theorem density_coordinate (w : ℂ) (t : ℝ) (ht : t < 0) :
    coordinateFirst t • ((horizonCoordinate t:ℂ)^(w-1)*(Real.sqrt (1-horizonCoordinate t):ℂ))=
      2*mode w t^(2 : ℕ) := by
  have hz := horizonCoordinate_interior t ht
  have hs : Real.sqrt (1-horizonCoordinate t)=radialUnit t := by
    rw [horizonCoordinate,sub_sub_cancel,Real.sqrt_sq (radialUnit_bounds t ht).1.le]
  have hp : (horizonCoordinate t:ℂ)*(horizonCoordinate t:ℂ)^(w-1)=(horizonCoordinate t:ℂ)^w := by
    calc
      _ = (horizonCoordinate t:ℂ)^(1:ℂ)*(horizonCoordinate t:ℂ)^(w-1) := by rw [Complex.cpow_one]
      _ = _ := by rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)),show 1+(w-1)=w by ring]
  rw [Complex.real_smul,coordinateFirst,hs,mode_square w t ht]
  push_cast
  calc
    _ = 2*((horizonCoordinate t:ℂ)*(horizonCoordinate t:ℂ)^(w-1))*(radialUnit t:ℂ)^(2 : ℕ) := by ring
    _ = _ := by rw [hp]; ring

/-- Every finite original cutoff interval admits the bilinear mode square as an ordinary integral. -/
theorem mode_square_intervalIntegrable (w : ℂ) (L : ℝ) (hL : L < 0) :
    IntervalIntegrable (fun t : ℝ => mode w t^(2 : ℕ)) volume L 0 := by
  have hc : Continuous horizonCoordinate := continuous_iff_continuousAt.mpr
    (fun t => (horizonCoordinate_hasDerivAt t).continuousAt)
  have hp : ContinuousOn (fun t : ℝ => power (w/2) (horizonCoordinate t)) (uIcc L 0) := by
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    have hz : 0 < horizonCoordinate t := by
      rcases lt_or_eq_of_le ht.2 with h | h
      · exact (horizonCoordinate_interior t h).1
      · subst t; norm_num [horizonCoordinate,radialUnit]
    exact (((power_derivatives (w/2) hz).1.scomp t (horizonCoordinate_hasDerivAt t)).continuousAt).continuousWithinAt
  have hs : Continuous (fun t : ℝ => (Real.sqrt (1-horizonCoordinate t):ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.sub hc))
  have he (t : ℝ) : mode w t=power (w/2) (horizonCoordinate t)*(Real.sqrt (1-horizonCoordinate t):ℂ) := by
    rw [mode,power_half_eq_sqrt (by dsimp only [horizonCoordinate]; nlinarith [sq_nonneg (radialUnit t)])]
  simp_rw [he]
  exact ((hp.mul hs.continuousOn).pow 2).intervalIntegrable

/-- Exact change of variables from the original tortoise measure to the square-root beta density. -/
theorem mode_square_integral (w : ℂ) (L : ℝ) (hL : L < 0) :
    (∫ t in L..0, mode w t^(2 : ℕ))=
      (1/2:ℂ)*(∫ z in horizonCoordinate L..1, (z:ℂ)^(w-1)*(Real.sqrt (1-z):ℂ)) := by
  have hc : Continuous horizonCoordinate := continuous_iff_continuousAt.mpr
    (fun t => (horizonCoordinate_hasDerivAt t).continuousAt)
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (f := horizonCoordinate) (f' := coordinateFirst)
    (g := fun z : ℝ => (z:ℂ)^(w-1)*(Real.sqrt (1-z):ℂ))
    (a := L) (b := 0) hc.continuousOn
    (fun t _ => horizonCoordinate_hasDerivAt t)
    (fun t ht => by
      have ht0 : t < 0 := by simpa only [max_eq_right hL.le] using ht.2
      exact mul_nonneg (mul_nonneg (by norm_num) (radialUnit_bounds t ht0).1.le)
        (horizonCoordinate_interior t ht0).1.le)
  have hzero : horizonCoordinate 0=1 := by norm_num [horizonCoordinate,radialUnit]
  rw [hzero] at hsub
  have he : (∫ t in L..0, coordinateFirst t •
      ((horizonCoordinate t:ℂ)^(w-1)*(Real.sqrt (1-horizonCoordinate t):ℂ)))=
      2*(∫ t in L..0, mode w t^(2 : ℕ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hL.le] at ht
    exact density_coordinate w t ht.2
  change (∫ t in L..0, coordinateFirst t •
    ((horizonCoordinate t:ℂ)^(w-1)*(Real.sqrt (1-horizonCoordinate t):ℂ)))=_ at hsub
  rw [he] at hsub
  linear_combination (1/2:ℂ)*hsub

/-- The horizon coordinate approaches zero through the actual positive interior. -/
theorem horizonCoordinate_tendsto_positive :
    Tendsto horizonCoordinate atBot (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨horizonCoordinate_tendsto_horizon,?_⟩
  filter_upwards [eventually_lt_atBot (0:ℝ)] with t ht
  exact (horizonCoordinate_interior t ht).1

/-- Precisely the two counterterms of the original radial density, expressed in the original coordinate. -/
def counterterm (w : ℂ) (L : ℝ) : ℂ :=
  (horizonCoordinate L:ℂ)^w/(2*w)-(horizonCoordinate L:ℂ)^(w+1)/(4*(w+1))

/-- The actual horizon-exhausted fundamental norm. -/
def normFinitePart (w : ℂ) : ℂ := (1/2:ℂ)*HalfOrderBeta.finitePart w

/-- The original radial cutoff integral has the restored limit; no value is assigned independently of this limit. -/
theorem mode_square_cutoff_tendsto (w : ℂ) (hw : -2 < w.re) (hw0 : w ≠ 0) (hw1 : w+1 ≠ 0) :
    Tendsto (fun L : ℝ => (∫ t in L..0, mode w t^(2 : ℕ))+counterterm w L)
      atBot (𝓝 (normFinitePart w)) := by
  have h := ((HalfOrderBeta.finitePart_cutoff_tendsto w hw hw0 hw1).comp
    horizonCoordinate_tendsto_positive).const_mul (1/2:ℂ)
  apply h.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with L hL
  rw [mode_square_integral w L hL]
  dsimp only [counterterm,Function.comp_def]
  simp only [div_mul_eq_div_div]
  ring

/-- Exact nonreal-frequency evaluation of the original radial finite part. -/
theorem normFinitePart_eq_gamma (w : ℂ) (hw : -2 < w.re) (hi : w.im ≠ 0) :
    normFinitePart w=Complex.Gamma w*Complex.Gamma (3/2)/(2*Complex.Gamma (w+3/2)) := by
  rw [normFinitePart,HalfOrderBeta.finitePart_eq_gamma w hw hi]
  ring

theorem normFinitePart_ne_zero (w : ℂ) (hw : -2 < w.re) (hi : w.im ≠ 0) :
    normFinitePart w ≠ 0 :=
  mul_ne_zero (by norm_num) (HalfOrderBeta.finitePart_ne_zero w hw hi)

end
end RHTower.D4BMFundamentalNorm

namespace RHTower.D4BMPhysicalModeAction
open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMJointWave D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The radially constant coefficient of the actual temporal Einstein Laurent density. -/
def physicalRadialResidueFactor (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (z : D4BMHorizon.Point) : ℂ :=
  -2*physicalFundamentalFrequency q side*(physicalAngularParameter q^(2 : ℕ)-1/4-2)*
    (physicalSelfSourceCoefficient q*
      fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a*
      clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side)/
      physicalFundamentalDenominatorSlope q branch side)*modeAngularSquare (physicalModeAngularJet q z)

/-- Multiplication by the original radius Jacobian cancels precisely the denominator in the actual Einstein current. -/
theorem physicalTimeResidue_radial_density (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (outer : Bool) (t : ℝ) (ht : t < 0) (z : D4BMHorizon.Point) :
    ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*physicalTimeResidue q branch side a outer t z =
      physicalRadialResidueFactor q branch side a z*
        D4BMFundamentalNorm.mode (physicalFundamentalFrequency q side) t^(2 : ℕ) := by
  have hR : (tortoiseRadius t:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show tortoiseRadius t^(2 : ℕ)-1 ≠ 0 by nlinarith [tortoiseRadius_exterior t ht])
  rw [physicalTimeResidue_fundamental_value q branch side a outer t ht z]
  dsimp only [physicalRadialResidueFactor,D4BMFundamentalNorm.mode]
  field_simp [hR]

/-- The actual finite-radius integral of the temporal Laurent coefficient, in the original tortoise chart. -/
theorem physicalTimeResidue_radial_integral (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (outer : Bool) (L : ℝ) (hL : L < 0) (z : D4BMHorizon.Point) :
    (∫ t in L..0, ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*physicalTimeResidue q branch side a outer t z)=
      physicalRadialResidueFactor q branch side a z*
        (∫ t in L..0, D4BMFundamentalNorm.mode (physicalFundamentalFrequency q side) t^(2 : ℕ)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  rw [uIoo_of_le hL.le] at ht
  exact physicalTimeResidue_radial_density q branch side a outer t ht.2 z

/-- The finite part is the limit of the original integrated Laurent density with its two derived horizon terms. -/
def physicalRadialResidueFinitePart (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (z : D4BMHorizon.Point) : ℂ :=
  physicalRadialResidueFactor q branch side a z*
    D4BMFundamentalNorm.normFinitePart (physicalFundamentalFrequency q side)

/-- Every actual Xi fundamental frequency admits the original radial Laurent-density finite part. -/
theorem physicalTimeResidue_radial_cutoff_tendsto (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (outer : Bool) (z : D4BMHorizon.Point) :
    Tendsto (fun L : ℝ =>
      (∫ t in L..0, ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*physicalTimeResidue q branch side a outer t z)+
      physicalRadialResidueFactor q branch side a z*
        D4BMFundamentalNorm.counterterm (physicalFundamentalFrequency q side) L)
      atBot (𝓝 (physicalRadialResidueFinitePart q branch side a z)) := by
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hw0 : w ≠ 0 := by intro he; apply hw.1; change w.im=0; rw [he]; rfl
  have hw1 : w+1 ≠ 0 := by
    intro he
    apply hw.1
    have hh := congrArg Complex.im he
    simpa using hh
  have h := (D4BMFundamentalNorm.mode_square_cutoff_tendsto w
    (abs_lt.mp hw.2).1 hw0 hw1).const_mul (physicalRadialResidueFactor q branch side a z)
  apply h.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with L hL
  rw [physicalTimeResidue_radial_integral q branch side a outer L hL z]
  ring

/-- The integrated radial coefficient has a completely explicit Gamma factor. -/
theorem physicalRadialResidueFinitePart_eq_gamma (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (z : D4BMHorizon.Point) :
    physicalRadialResidueFinitePart q branch side a z=
      physicalRadialResidueFactor q branch side a z*
        (Complex.Gamma (physicalFundamentalFrequency q side)*Complex.Gamma (3/2)/
          (2*Complex.Gamma (physicalFundamentalFrequency q side+3/2))) := by
  rw [physicalRadialResidueFinitePart,D4BMFundamentalNorm.normFinitePart_eq_gamma _
    (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
    (physicalFundamentalFrequency_strip q side).1]

/-- Horizon integration contributes no zero factor at either fundamental QNM of any Xi copy. -/
theorem physicalRadialResidueFinitePart_eq_zero_iff (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (z : D4BMHorizon.Point) :
    physicalRadialResidueFinitePart q branch side a z=0 ↔
      physicalRadialResidueFactor q branch side a z=0 := by
  rw [physicalRadialResidueFinitePart,mul_eq_zero]
  exact or_iff_left (D4BMFundamentalNorm.normFinitePart_ne_zero _
    (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
    (physicalFundamentalFrequency_strip q side).1)

end
end RHTower.D4BMPhysicalModeAction
