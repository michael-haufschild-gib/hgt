import GaloisForLFunctions.BiScaleUncertainty.PhysicalAffineAction
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# Strong physical translations and bounded primitive evaluation

The actual translation orbit is norm-continuous. Oriented interval vectors
represent primitive evaluation as a bounded linear functional, so physical
primitive traces commute with Bochner integration of translation orbits.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem continuous_physicalTranslation (q : Velocity) :
    Continuous (fun b : ℝ => physicalTranslation b q) := by
  let g : ℝ → C(ℝ, ℝ) := fun b => ⟨fun t => t+b, continuous_id.add continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  have h := (continuous_const : Continuous (fun _ : ℝ => q)).compMeasurePreservingLp hg
    (fun b => measurePreserving_add_right (volume : Measure ℝ) b) (by norm_num)
  exact h

theorem intervalIntegrable_physicalTranslation (q : Velocity) (a b : ℝ) :
    IntervalIntegrable (fun u => physicalTranslation u q) volume a b :=
  (continuous_physicalTranslation q).intervalIntegrable a b

def physicalOrbitPrimitive (q : Velocity) (t : ℝ) : Velocity :=
  ∫ u in 0..t, physicalTranslation u q

theorem physicalOrbitPrimitive_zero (q : Velocity) : physicalOrbitPrimitive q 0 = 0 := by
  simp [physicalOrbitPrimitive]

theorem physicalOrbitPrimitive_sub (q : Velocity) (a b : ℝ) :
    physicalOrbitPrimitive q b-physicalOrbitPrimitive q a =
      ∫ u in a..b, physicalTranslation u q :=
  intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_physicalTranslation q 0 b) (intervalIntegrable_physicalTranslation q 0 a)

theorem hasDerivAt_physicalOrbitPrimitive (q : Velocity) (t : ℝ) :
    HasDerivAt (physicalOrbitPrimitive q) (physicalTranslation t q) t :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_physicalTranslation q 0 t)
    (continuous_physicalTranslation q).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_physicalTranslation q).continuousAt

def physicalPrimitiveKernel (t : ℝ) : Velocity :=
  indicatorConstLp 2 (measurableSet_Ioc (a := (0 : ℝ)) (b := t)) measure_Ioc_lt_top.ne 1 -
    indicatorConstLp 2 (measurableSet_Ioc (a := t) (b := (0 : ℝ))) measure_Ioc_lt_top.ne 1

theorem inner_physicalPrimitiveKernel (t : ℝ) (q : Velocity) :
    ⟪physicalPrimitiveKernel t, q⟫ = primitive q t := by
  rw [physicalPrimitiveKernel, inner_sub_left, L2.inner_indicatorConstLp_one,
    L2.inner_indicatorConstLp_one]
  rfl

def physicalPrimitiveFunctional (t : ℝ) : Velocity →L[ℝ] ℝ :=
  innerSL ℝ (physicalPrimitiveKernel t)

theorem physicalPrimitiveFunctional_apply (t : ℝ) (q : Velocity) :
    physicalPrimitiveFunctional t q = primitive q t :=
  inner_physicalPrimitiveKernel t q

theorem primitive_integral_physicalTranslation (q : Velocity) (a b t : ℝ) :
    primitive (∫ u in a..b, physicalTranslation u q) t =
      ∫ u in a..b, primitive (physicalTranslation u q) t := by
  simpa only [physicalPrimitiveFunctional_apply] using
    ((physicalPrimitiveFunctional t).intervalIntegral_comp_comm
      (intervalIntegrable_physicalTranslation q a b)).symm

theorem integral_inner_physicalTranslation (q r : Velocity) (a b : ℝ) :
    (∫ u in a..b, ⟪r, physicalTranslation u q⟫) =
      ⟪r, ∫ u in a..b, physicalTranslation u q⟫ :=
  (innerSL ℝ r).intervalIntegral_comp_comm (intervalIntegrable_physicalTranslation q a b)

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
