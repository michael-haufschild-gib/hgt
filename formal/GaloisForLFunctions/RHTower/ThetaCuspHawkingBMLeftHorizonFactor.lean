import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalModeAction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalRadialModes
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHorizonCoordinateJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceHorizonFactor

/-! Exact horizon factor of the original opposite-time-frequency left QNM. -/
open Complex Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMLeftHorizonFactor
open GaloisForLFunctions.HTGeometry D4BMLaplaceRadial D4BMJointSource D4BMJointWave
open D4BMPhysicalModeAction D4BMModularCore

private theorem roots (q : XiZeroCopy) (side : Bool) :
    physicalFundamentalFrequency q side=-3/2-I*physicalRadialFrequency q ∨
    physicalFundamentalFrequency q side=-3/2+I*physicalRadialFrequency q := by
  rw [physicalFundamentalFrequency_connection_root]
  cases side <;> simp

private theorem mode_value (q : XiZeroCopy) (side outer : Bool) (t : ℝ) (ht : t<0) :
    tortoiseMode outer (physicalFundamentalFrequency q side) (physicalRadialFrequency q) t=
      power (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*(radialUnit t:ℂ) := by
  have h : tortoiseMode outer (physicalFundamentalFrequency q side) (physicalRadialFrequency q) t=
      power (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*power (1/2) (1-horizonCoordinate t) := by
    cases outer
    · change horizon _ _ _ = _
      rw [horizon_eq_normalizable_fundamental _ _ (physicalFundamentalFrequency_strip q side).1
        (roots q side) (horizonCoordinate_interior t ht)]
      exact normalizable_fundamental_value _ _ (roots q side) _
    · exact normalizable_fundamental_value _ _ (roots q side) _
  rw [h,power_half_eq_sqrt (sub_nonneg.mpr (horizonCoordinate_interior t ht).2.le),
    ← radialUnit_eq_sqrt t ht]

private theorem ingoing_power (w : ℂ) (p t : ℝ) (ht : t<0) :
    Complex.exp ((-w)*((p-t):ℂ))*power (w/2) (horizonCoordinate t)=
      Complex.exp ((-w)*(p:ℂ))*power w (1-radialUnit t) := by
  have hplus := radialUnit_add_one_pos t
  have hminus : 0<1-radialUnit t := sub_pos.mpr (radialUnit_bounds t ht).2
  have hl : Real.log (1-radialUnit t)=2*t+Real.log (1+radialUnit t) := by
    rw [radialUnit_one_sub t,Real.log_mul (Real.exp_ne_zero _) hplus.ne',Real.log_exp]
  rw [horizonPower_tortoise w t ht]
  unfold power
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hplus.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hminus.ne'),
    ← Complex.ofReal_log hplus.le,← Complex.ofReal_log hminus.le,hl]
  rw [← Complex.exp_add,← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Both original radial normalizations yield the same explicit left-stream horizon factor. -/
theorem physicalLeftModeStream_ingoing (q : XiZeroCopy) (side outer : Bool)
    (p : ℝ) (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (j : Fin 2) :
    physicalLeftModeStream q (physicalFundamentalFrequency q side) outer j
      ![p-t.val,tortoiseRadius t.val,z 0,z 1]=
      Complex.exp ((-physicalFundamentalFrequency q side)*(p:ℂ))*
        power (physicalFundamentalFrequency q side) (1-radialUnit t.val)*
        D4BMLiteralCusp.vector (physicalAngularParameter q) j z := by
  have hr : (tortoiseRadius t.val:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (lt_trans zero_lt_one (tortoiseRadius_exterior _ t.property)).ne'
  have hang : D4BMMetricReconstruction.angularPoint ![p-t.val,tortoiseRadius t.val,z 0,z 1]=z := by
    ext i
    fin_cases i <;> rfl
  unfold physicalLeftModeStream radiusLift
  dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [hang,tortoise_original_inverse t.val t.property,mode_value q side outer _ t.property,
    radialUnit_inverse_radius]
  push_cast
  have hcancel (A B : ℂ) : A*((tortoiseRadius t.val:ℂ)*(B*(tortoiseRadius t.val:ℂ)⁻¹))=A*B := by
    field_simp
  rw [hcancel]
  rw [ingoing_power _ p t.val t.property,radialUnit_inverse_radius]

/-- The original angular action eigenvalue in the left fundamental frequency. -/
theorem physical_angular_eigenvalue (q : XiZeroCopy) (side : Bool) :
    physicalAngularParameter q^(2 : ℕ)-1/4-2=
      physicalFundamentalFrequency q side*(physicalFundamentalFrequency q side+3) := by
  rw [physicalFundamentalFrequency_connection_root,physicalRadialFrequency]
  cases side <;> simp only [Bool.false_eq_true,ite_true,ite_false]
  all_goals (ring_nf; norm_num [Complex.I_sq])

/-- The original left stream along the exact ingoing chart, without a frequency shift. -/
def ingoingField (q : XiZeroCopy) (side outer : Bool) (p t : ℝ)
    (z : D4BMHorizon.Point) (j : Fin 2) : ℂ :=
  physicalLeftModeStream q (physicalFundamentalFrequency q side) outer j
    ![p-t,tortoiseRadius t,z 0,z 1]

private theorem ingoingField_value (q : XiZeroCopy) (side outer : Bool)
    (p t : ℝ) (ht : t<0) (z : D4BMHorizon.Point) (j : Fin 2) :
    ingoingField q side outer p t z j=
      Complex.exp ((-physicalFundamentalFrequency q side)*(p:ℂ))*
        power (physicalFundamentalFrequency q side) (1-radialUnit t)*
        D4BMLiteralCusp.vector (physicalAngularParameter q) j z :=
  physicalLeftModeStream_ingoing q side outer p ⟨t,ht⟩ z j

/-- Actual ingoing-time derivative of the original left QNM. -/
theorem ingoingField_time_hasDerivAt (q : XiZeroCopy) (side outer : Bool)
    (p : ℝ) (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (j : Fin 2) :
    HasDerivAt (fun v => ingoingField q side outer v t.val z j)
      (-physicalFundamentalFrequency q side*ingoingField q side outer p t.val z j) p := by
  have h := (((hasDerivAt_id p).ofReal_comp.const_mul
    (-physicalFundamentalFrequency q side)).cexp.mul_const
    (power (physicalFundamentalFrequency q side) (1-radialUnit t.val))).mul_const
    (D4BMLiteralCusp.vector (physicalAngularParameter q) j z)
  convert! h using 1
  · ext v
    exact ingoingField_value q side outer v t.val t.property z j
  · rw [ingoingField_value q side outer p t.val t.property z j]
    simp only [id_eq,Complex.ofReal_one,mul_one]
    ring

/-- Actual radial-chart derivative: its only singularity is the original mode power. -/
theorem ingoingField_radial_hasDerivAt (q : XiZeroCopy) (side outer : Bool)
    (p : ℝ) (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (j : Fin 2) :
    HasDerivAt (fun v => ingoingField q side outer p v z j)
      (physicalFundamentalFrequency q side*(1+(radialUnit t.val:ℂ))*
        ingoingField q side outer p t.val z j) t.val := by
  have hm : 0<1-radialUnit t.val := sub_pos.mpr (radialUnit_bounds t.val t.property).2
  have hmc : 1-(radialUnit t.val:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have h := (((power_derivatives (physicalFundamentalFrequency q side) hm).1.scomp t.val
    ((radialUnit_hasDerivAt t.val).const_sub 1)).const_mul
    (Complex.exp ((-physicalFundamentalFrequency q side)*(p:ℂ)))).mul_const
    (D4BMLiteralCusp.vector (physicalAngularParameter q) j z)
  have he : (fun v => ingoingField q side outer p v z j)=ᶠ[𝓝 t.val]
      (fun v => Complex.exp ((-physicalFundamentalFrequency q side)*(p:ℂ))*
        power (physicalFundamentalFrequency q side) (1-radialUnit v)*
        D4BMLiteralCusp.vector (physicalAngularParameter q) j z) := by
    filter_upwards [isOpen_Iio.mem_nhds t.property] with v hv
    exact ingoingField_value q side outer p v hv z j
  apply (h.congr_of_eventuallyEq he).congr_deriv
  rw [ingoingField_value q side outer p t.val t.property z j]
  dsimp [powerFirst]
  push_cast
  field_simp [hmc]
  ring

/-- The original characteristic derivative cancels its extra horizon pole exactly. -/
theorem ingoingField_transport (q : XiZeroCopy) (side outer : Bool)
    (p : ℝ) (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (j : Fin 2) :
    deriv (fun v => ingoingField q side outer p v z j) t.val+
      deriv (fun v => ingoingField q side outer v t.val z j) p=
      physicalFundamentalFrequency q side*(radialUnit t.val:ℂ)*
        ingoingField q side outer p t.val z j := by
  rw [(ingoingField_radial_hasDerivAt q side outer p t z j).deriv,
    (ingoingField_time_hasDerivAt q side outer p t z j).deriv]
  ring

end RHTower.D4BMLeftHorizonFactor
