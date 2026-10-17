import GaloisForLFunctions.BiScaleUncertainty.PhysicalTranslation

/-!
# Anchored physical affine action and its exact commutator defect

Primitive injectivity promotes the substitution formulas to actual operator
covariance. Anchors compose exactly. A positive antiperiodic residual measures
the full physical commutator deficit for every scale and shift.
-/

noncomputable section
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem physicalTranslation_dilation (a b : ℝ) (q : Velocity) :
    physicalTranslation b (physicalDilation a q) =
      physicalDilation a (physicalTranslation (a*b) q) := by
  apply primitive_injective
  funext t
  simp only [primitive_physicalTranslation, primitive_physicalDilation]
  rw [mul_add]

abbrev AnchoredPhysicalState := ℝ × Velocity

def anchoredPhysicalValue (v : AnchoredPhysicalState) (t : ℝ) : ℝ :=
  v.1+primitive v.2 t

def anchoredPhysicalTranslation (b : ℝ) (v : AnchoredPhysicalState) : AnchoredPhysicalState :=
  (v.1+primitive v.2 b, physicalTranslation b v.2)

def anchoredPhysicalDilation (a : ℝ) (v : AnchoredPhysicalState) : AnchoredPhysicalState :=
  (v.1, physicalDilation a v.2)

theorem anchoredPhysicalValue_translation (b : ℝ) (v : AnchoredPhysicalState) (t : ℝ) :
    anchoredPhysicalValue (anchoredPhysicalTranslation b v) t = anchoredPhysicalValue v (t+b) := by
  simp only [anchoredPhysicalValue, anchoredPhysicalTranslation, primitive_physicalTranslation]
  ring

theorem anchoredPhysicalValue_dilation (a : ℝ) (v : AnchoredPhysicalState) (t : ℝ) :
    anchoredPhysicalValue (anchoredPhysicalDilation a v) t = anchoredPhysicalValue v (a*t) := by
  simp only [anchoredPhysicalValue, anchoredPhysicalDilation, primitive_physicalDilation]

theorem anchoredPhysicalTranslation_comp (b c : ℝ) (v : AnchoredPhysicalState) :
    anchoredPhysicalTranslation b (anchoredPhysicalTranslation c v) =
      anchoredPhysicalTranslation (b+c) v := by
  apply Prod.ext
  · simp only [anchoredPhysicalTranslation, primitive_physicalTranslation]
    ring
  · exact physicalTranslation_comp b c v.2

theorem anchoredPhysicalTranslation_zero (v : AnchoredPhysicalState) :
    anchoredPhysicalTranslation 0 v = v := by
  simp only [anchoredPhysicalTranslation, primitive_at_zero, add_zero, physicalTranslation_zero]

theorem anchoredPhysicalTranslation_inverse (b : ℝ) (v : AnchoredPhysicalState) :
    anchoredPhysicalTranslation (-b) (anchoredPhysicalTranslation b v) = v := by
  rw [anchoredPhysicalTranslation_comp, neg_add_cancel, anchoredPhysicalTranslation_zero]

theorem anchoredPhysicalDilation_comp (a c : ℝ) (v : AnchoredPhysicalState) :
    anchoredPhysicalDilation a (anchoredPhysicalDilation c v) = anchoredPhysicalDilation (a*c) v := by
  apply Prod.ext
  · rfl
  · exact physicalDilation_comp a c v.2

theorem anchoredPhysicalTranslation_dilation (a b : ℝ) (v : AnchoredPhysicalState) :
    anchoredPhysicalTranslation b (anchoredPhysicalDilation a v) =
      anchoredPhysicalDilation a (anchoredPhysicalTranslation (a*b) v) := by
  apply Prod.ext
  · simp only [anchoredPhysicalTranslation, anchoredPhysicalDilation, primitive_physicalDilation]
  · exact physicalTranslation_dilation a b v.2

def physicalAffineCommutator (a b : ℝ) : Velocity →L[ℝ] Velocity :=
  physicalDilation a ∘L (physicalTranslation b).toContinuousLinearMap -
    (physicalTranslation b).toContinuousLinearMap ∘L physicalDilation a

theorem physicalAffineCommutator_apply (a b : ℝ) (q : Velocity) :
    physicalAffineCommutator a b q = physicalDilation a (physicalTranslation b q)-
      physicalTranslation b (physicalDilation a q) := rfl

theorem physicalAffineCommutator_factor (a b : ℝ) (q : Velocity) :
    physicalAffineCommutator a b q =
      physicalDilation a (physicalTranslation b q-physicalTranslation (a*b) q) := by
  rw [physicalAffineCommutator_apply, physicalTranslation_dilation, map_sub]

theorem primitive_physicalAffineCommutator (a b : ℝ) (q : Velocity) (t : ℝ) :
    primitive (physicalAffineCommutator a b q) t =
      primitive q (a*t+b)-primitive q b-primitive q (a*t+a*b)+primitive q (a*b) := by
  rw [physicalAffineCommutator_factor, primitive_physicalDilation, primitive_sub_velocity,
    primitive_physicalTranslation, primitive_physicalTranslation]
  ring

theorem physicalTranslation_sub_norm (b c : ℝ) (q : Velocity) :
    ‖physicalTranslation b q-physicalTranslation c q‖ = ‖physicalTranslation (c-b) q-q‖ := by
  have h := (physicalTranslation (-b)).norm_map (physicalTranslation b q-physicalTranslation c q)
  rw [map_sub, physicalTranslation_comp, physicalTranslation_comp,
    neg_add_cancel, physicalTranslation_zero] at h
  rw [show -b+c = c-b by ring, norm_sub_rev] at h
  exact h.symm

theorem physicalAffineCommutator_energy (a b : ℝ) (q : Velocity) :
    ‖physicalAffineCommutator a b q‖^2 = |a| * ‖physicalTranslation (b*(a-1)) q-q‖^2 := by
  rw [physicalAffineCommutator_factor, physicalDilation_energy, physicalTranslation_sub_norm,
    show a*b-b = b*(a-1) by ring]

theorem physicalTranslation_parallelogram (c : ℝ) (q : Velocity) :
    ‖physicalTranslation c q-q‖^2+‖physicalTranslation c q+q‖^2 = 4*‖q‖^2 := by
  rw [norm_sub_sq_real, norm_add_sq_real, physicalTranslation_norm]
  ring

theorem physicalAffineCommutator_defect (a b : ℝ) (q : Velocity) :
    4*|a| * ‖q‖^2-‖physicalAffineCommutator a b q‖^2 =
      |a| * ‖physicalTranslation (b*(a-1)) q+q‖^2 := by
  rw [physicalAffineCommutator_energy]
  have h := congrArg (fun x : ℝ => |a| * x) (physicalTranslation_parallelogram (b*(a-1)) q)
  nlinarith only [h]

theorem physicalAffineCommutator_energy_le (a b : ℝ) (q : Velocity) :
    ‖physicalAffineCommutator a b q‖^2 ≤ 4*|a| * ‖q‖^2 := by
  have h := physicalAffineCommutator_defect a b q
  have hn := mul_nonneg (abs_nonneg a) (sq_nonneg ‖physicalTranslation (b*(a-1)) q+q‖)
  linarith only [h, hn]

theorem physicalAffineCommutator_norm_le (a b : ℝ) (q : Velocity) :
    ‖physicalAffineCommutator a b q‖ ≤ 2*Real.sqrt |a| * ‖q‖ := by
  have h := physicalAffineCommutator_energy_le a b q
  have hs : (2*Real.sqrt |a| * ‖q‖)^2 = 4*|a| * ‖q‖^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg a)]
    ring
  nlinarith only [h, hs, norm_nonneg (physicalAffineCommutator a b q),
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg |a|)) (norm_nonneg q)]

theorem norm_physicalAffineCommutator_le (a b : ℝ) :
    ‖physicalAffineCommutator a b‖ ≤ 2*Real.sqrt |a| :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (physicalAffineCommutator_norm_le a b)

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
