import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCommonSourceGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCharacteristicContact

/-! Original source-radius differentiation of the native causal kernel, including both
closed characteristic faces and the full angular-action integral. -/
namespace RHTower.D4BMNativeSourceDerivative
open D4BMCommonSourceGreen D4BMNativeCircle D4BMCausalKernel D4BMJointSource
open D4BMModularCore D4BMHorizon D4BMGlobalAngularResponse
open Set Filter Topology MeasureTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private def sourceInvariant (image : Bool) (h target y : ℝ) : ℝ :=
  invariant (h-target+y) target (if image then -y else y)

private theorem sourceInvariant_closed (image : Bool) {h target y : ℝ}
    (hh : 0 ≤ h) (hx : target ≤ 0) (hy : sourceCharacteristic image h target ≤ y) :
    1 ≤ sourceInvariant image h target y := by
  have ha : |target-(if image then -y else y)| ≤ h-target+y := by
    rw [abs_le]
    cases image <;> simp only [sourceCharacteristic,Bool.false_eq_true,if_false,if_true] at hy ⊢
    all_goals constructor <;> linarith
  have ht : 0 ≤ h-target+y := (abs_nonneg _).trans ha
  have hc : Real.cosh (target-(if image then -y else y)) ≤ Real.cosh (h-target+y) := by
    apply Real.cosh_le_cosh.mpr
    rwa [abs_of_nonneg ht]
  rw [Real.cosh_sub] at hc
  unfold sourceInvariant invariant
  apply (le_div_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))).mpr
  linarith

private theorem sourceInvariant_derivative (image : Bool) (h target y : ℝ) :
    HasDerivAt (sourceInvariant image h target)
      (kernelArgumentSlope image h target*(1-radialUnit y^2)) y := by
  have hD := ((radialUnit_hasDerivAt y).const_mul (kernelArgumentSlope image h target)).const_sub
    (kernelArgumentBase h target)
  have he : sourceInvariant image h target=
      fun r => kernelArgumentBase h target-kernelArgumentSlope image h target*radialUnit r :=
    funext (kernel_invariant_affine image h target)
  rw [he]
  apply hD.congr_deriv
  ring

/-- Original source-radius derivative: the ingoing delay is fixed, and both
static separation and source position vary in the literal causal kernel. -/
def sourceFirst (image : Bool) (q : XiZeroCopy) (h target X k y : ℝ) : ℂ :=
  characteristicFirst q (sourceInvariant image h target y) X k*
    (kernelArgumentSlope image h target*(1-radialUnit y^2):ℝ)

/-- The full native causal kernel has its integral-valued source derivative on
both closed physical characteristic rays, including zero delay. -/
theorem kernelField_source_derivative (image : Bool) (q : XiZeroCopy)
    (h : Ici (0:ℝ)) (target : Iic (0:ℝ)) (X k : ℝ)
    (y : Ici (sourceCharacteristic image h.val target.val)) :
    HasDerivWithinAt (fun r => kernelField image q h target ![r,X,k])
      (sourceFirst image q h target X k y) (Ici (sourceCharacteristic image h target)) y.val := by
  have hz := sourceInvariant_closed image h.property target.property y.property
  have hm := angularKernel_closed_derivative q X k
    ⟨sourceInvariant image h target y,hz⟩
  have hd := sourceInvariant_derivative image h target y
  have he := hm.scomp y.val hd.hasDerivWithinAt
    (fun r hr => sourceInvariant_closed image h.property target.property hr)
  simpa only [Function.comp_def,Complex.real_smul,mul_comm,sourceFirst,sourceInvariant,
    kernelField,nativeRiemannKernel,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two] using! he

/-- No inverse-coordinate singularity remains in the actual source derivative. -/
theorem sourceFirst_continuousOn (image : Bool) (q : XiZeroCopy)
    (h : Ici (0:ℝ)) (target : Iic (0:ℝ)) (X k : ℝ) :
    ContinuousOn (sourceFirst image q h target X k) (Ici (sourceCharacteristic image h target)) := by
  have hi : Continuous (sourceInvariant image h target) :=
    continuous_iff_continuousAt.mpr (fun y => (sourceInvariant_derivative image h target y).continuousAt)
  have hm := (characteristicFirst_continuousOn q X k).comp hi.continuousOn
    (fun r hr => sourceInvariant_closed image h.property target.property hr)
  have hu : Continuous radialUnit :=
    continuous_iff_continuousAt.mpr (fun y => (radialUnit_hasDerivAt y).continuousAt)
  exact hm.mul (Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_const.sub (hu.pow 2)))).continuousOn

private theorem sourceInvariant_characteristic (image : Bool) (h target : ℝ) :
    sourceInvariant image h target (sourceCharacteristic image h target)=1 := by
  cases image
  · simp only [sourceInvariant,sourceCharacteristic,Bool.false_eq_true,if_false]
    rw [show h-target+(target-h/2)=target-(target-h/2) by ring]
    exact invariant_characteristic target (target-h/2)
  · simp only [sourceInvariant,sourceCharacteristic,if_true]
    rw [show h-target+-h/2=-(target- -(-h/2)) by ring]
    unfold invariant
    rw [Real.cosh_neg]
    change invariant (target- -(-h/2)) target (-(-h/2))=1
    exact invariant_characteristic target (-(-h/2))

private theorem kernelField_characteristic (image : Bool) (q : XiZeroCopy)
    (h target X k : ℝ) :
    kernelField image q h target ![sourceCharacteristic image h target,X,k]=
      fullSquarePotential q ![X,Real.exp k] := by
  change mean q (Real.arcosh (sourceInvariant image h target (sourceCharacteristic image h target))) X k=_
  rw [sourceInvariant_characteristic,Real.arcosh_zero,mean_zero]

/-- Both original characteristic values and the entire source-radius integral
reconstruct the full native kernel, with every angular source term retained. -/
theorem kernelField_source_integral (image : Bool) (q : XiZeroCopy)
    (h : Ici (0:ℝ)) (target : Iic (0:ℝ)) (X k : ℝ)
    (y : Ici (sourceCharacteristic image h.val target.val)) :
    kernelField image q h target ![y.val,X,k]=fullSquarePotential q ![X,Real.exp k]+
      ∫ r in sourceCharacteristic image h target..y.val, sourceFirst image q h target X k r := by
  have hd := fun r hr => kernelField_source_derivative image q h target X k ⟨r,hr⟩
  have hc : ContinuousOn (fun r => kernelField image q h target ![r,X,k])
      (Ici (sourceCharacteristic image h target)) := fun r hr => (hd r hr).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le y.property
    (hc.mono Icc_subset_Ici_self)
    (fun r hr => (hd r hr.1.le).hasDerivAt (Ici_mem_nhds hr.1))
    (((sourceFirst_continuousOn image q h target X k).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc y.property)
  rw [kernelField_characteristic] at h
  exact (eq_add_of_sub_eq h.symm).trans (add_comm _ _)


/-- The physical source-radius characteristic derivative retains the original
Laplacian contact and the actual direct/image geometric slope. -/
theorem kernelField_source_characteristic_derivative (image : Bool) (q : XiZeroCopy)
    (h : Ici (0:ℝ)) (target : Iic (0:ℝ)) (X k : ℝ) :
    HasDerivWithinAt (fun r => kernelField image q h target ![r,X,k])
      ((scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
        (kernelArgumentSlope image h target*
          (1-radialUnit (sourceCharacteristic image h target)^2):ℝ))
      (Ici (sourceCharacteristic image h target)) (sourceCharacteristic image h target) := by
  have hd := kernelField_source_derivative image q h target X k
    ⟨sourceCharacteristic image h target,by simp⟩
  simpa only [sourceFirst,sourceInvariant_characteristic,characteristicFirst_at_one] using! hd

/-- The actual interior source derivative converges to its physical characteristic
contact; the derivative is taken before the characteristic limit. -/
theorem kernelField_source_derivative_tendsto (image : Bool) (q : XiZeroCopy)
    (h : Ici (0:ℝ)) (target : Iic (0:ℝ)) (X k : ℝ) :
    Tendsto (deriv (fun r => kernelField image q h target ![r,X,k]))
      (𝓝[>] (sourceCharacteristic image h target))
      (𝓝 ((scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
        (kernelArgumentSlope image h target*
          (1-radialUnit (sourceCharacteristic image h target)^2):ℝ))) := by
  have hc := ((sourceFirst_continuousOn image q h target X k)
    (sourceCharacteristic image h target) (by simp)).mono Ioi_subset_Ici_self
  have hl := hc.tendsto
  simp only [sourceFirst,sourceInvariant_characteristic,characteristicFirst_at_one] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : sourceCharacteristic image h target < r := hr
  have hd := kernelField_source_derivative image q h target X k
    ⟨r,by change sourceCharacteristic image h target ≤ r; exact hr'.le⟩
  exact ((hd.hasDerivAt (Ici_mem_nhds hr')).deriv).symm

end
end RHTower.D4BMNativeSourceDerivative
