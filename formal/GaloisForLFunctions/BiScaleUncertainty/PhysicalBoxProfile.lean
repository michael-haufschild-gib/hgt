import GaloisForLFunctions.BiScaleUncertainty.PhysicalBoxAverage

/-!
# Continuous representatives and actual derivatives of box averages

Primitive evaluation identifies the Bochner average with its moving physical
interval integral. Its continuous representative is an anchored primitive
of an explicitly constructed L² finite difference.
-/

noncomputable section
open MeasureTheory
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def physicalSecondPrimitive (q : Velocity) (t : ℝ) : ℝ :=
  ∫ u in 0..t, primitive q u

theorem continuous_physicalPrimitive (q : Velocity) : Continuous (primitive q) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_velocity q) 0

theorem physicalSecondPrimitive_sub (q : Velocity) (a b : ℝ) :
    physicalSecondPrimitive q b-physicalSecondPrimitive q a = ∫ u in a..b, primitive q u :=
  intervalIntegral.integral_interval_sub_left
    ((continuous_physicalPrimitive q).intervalIntegrable 0 b)
    ((continuous_physicalPrimitive q).intervalIntegrable 0 a)

theorem hasDerivAt_physicalSecondPrimitive (q : Velocity) (t : ℝ) :
    HasDerivAt (physicalSecondPrimitive q) (primitive q t) t :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_physicalPrimitive q).intervalIntegrable 0 t)
    (continuous_physicalPrimitive q).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_physicalPrimitive q).continuousAt

theorem primitive_physicalBoxAverage (s : ℝ) (q : Velocity) (t : ℝ) :
    primitive (physicalBoxAverage s q) t = (Real.exp s)⁻¹ *
      (physicalSecondPrimitive q (t+Real.exp s)-physicalSecondPrimitive q t-
        physicalSecondPrimitive q (Real.exp s)) := by
  rw [physicalBoxAverage_apply, ← physicalPrimitiveFunctional_apply, map_smul,
    physicalPrimitiveFunctional_apply, primitive_integral_physicalTranslation]
  simp only [primitive_physicalTranslation, smul_eq_mul]
  have hi : IntervalIntegrable (fun u => primitive q (t+u)) volume 0 (Real.exp s) :=
    ((continuous_physicalPrimitive q).comp
      (continuous_const.add continuous_id)).intervalIntegrable 0 (Real.exp s)
  rw [intervalIntegral.integral_sub hi
    ((continuous_physicalPrimitive q).intervalIntegrable 0 (Real.exp s))]
  rw [intervalIntegral.integral_comp_add_left (a := 0) (b := Real.exp s)
    (primitive q) t, add_zero, ← physicalSecondPrimitive_sub]
  rfl

def physicalBoxProfile (s : ℝ) (q : Velocity) (t : ℝ) : ℝ :=
  (Real.exp s)⁻¹ * (primitive q (t+Real.exp s)-primitive q t)

theorem physicalBoxProfile_eq_integral (s : ℝ) (q : Velocity) (t : ℝ) :
    physicalBoxProfile s q t = (Real.exp s)⁻¹ * ∫ u in t..t+Real.exp s, q u := by
  rw [physicalBoxProfile, primitive_sub]

theorem continuous_physicalBoxProfile (s : ℝ) (q : Velocity) :
    Continuous (physicalBoxProfile s q) :=
  continuous_const.mul (((continuous_physicalPrimitive q).comp
    (continuous_id.add continuous_const)).sub (continuous_physicalPrimitive q))

theorem hasDerivAt_primitive_physicalBoxAverage (s : ℝ) (q : Velocity) (t : ℝ) :
    HasDerivAt (primitive (physicalBoxAverage s q)) (physicalBoxProfile s q t) t := by
  have h := ((((hasDerivAt_physicalSecondPrimitive q (t+Real.exp s)).comp_add_const
    t (Real.exp s)).sub (hasDerivAt_physicalSecondPrimitive q t)).sub_const
      (physicalSecondPrimitive q (Real.exp s))).const_smul (Real.exp s)⁻¹
  simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← primitive_physicalBoxAverage,
    physicalBoxProfile] using h

theorem ae_physicalBoxAverage (s : ℝ) (q : Velocity) :
    physicalBoxAverage s q =ᵐ[volume] physicalBoxProfile s q := by
  filter_upwards [ae_hasDerivAt_primitive (physicalBoxAverage s q)] with t ht
  exact ht.unique (hasDerivAt_primitive_physicalBoxAverage s q t)

theorem physicalBoxProfile_eq_anchored (s : ℝ) (q : Velocity) (t : ℝ) :
    physicalBoxProfile s q t = primitive (physicalBoxDerivative s q) t+
      (Real.exp s)⁻¹ * primitive q (Real.exp s) := by
  rw [physicalBoxDerivative_apply, ← physicalPrimitiveFunctional_apply,
    map_smul, physicalPrimitiveFunctional_apply, primitive_sub_velocity,
    primitive_physicalTranslation, physicalBoxProfile]
  change _ = (Real.exp s)⁻¹ * _ + _
  ring

theorem ae_hasDerivAt_physicalBoxProfile (s : ℝ) (q : Velocity) :
    ∀ᵐ t, HasDerivAt (physicalBoxProfile s q) (physicalBoxDerivative s q t) t := by
  filter_upwards [ae_hasDerivAt_primitive (physicalBoxDerivative s q)] with t ht
  simpa only [← physicalBoxProfile_eq_anchored] using
    ht.add_const ((Real.exp s)⁻¹ * primitive q (Real.exp s))

theorem ae_deriv_physicalBoxProfile (s : ℝ) (q : Velocity) :
    deriv (physicalBoxProfile s q) =ᵐ[volume] physicalBoxDerivative s q := by
  filter_upwards [ae_hasDerivAt_physicalBoxProfile s q] with t ht
  exact ht.deriv

theorem memLp_physicalBoxProfile (s : ℝ) (q : Velocity) :
    MemLp (physicalBoxProfile s q) 2 volume :=
  MemLp.ae_eq (ae_physicalBoxAverage s q) (Lp.memLp (physicalBoxAverage s q))

theorem memLp_deriv_physicalBoxProfile (s : ℝ) (q : Velocity) :
    MemLp (deriv (physicalBoxProfile s q)) 2 volume :=
  MemLp.ae_eq (ae_deriv_physicalBoxProfile s q).symm
    (Lp.memLp (physicalBoxDerivative s q))

theorem absolutelyContinuous_physicalBoxProfile (s : ℝ) (q : Velocity) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (physicalBoxProfile s q) a b := by
  have h := (absolutelyContinuous_primitive (physicalBoxDerivative s q) a b).add
    ((contDiffOn_const : ContDiffOn ℝ 1
      (fun _ : ℝ => (Real.exp s)⁻¹ * primitive q (Real.exp s)) (Set.uIcc a b)).absolutelyContinuousOnInterval)
  simpa only [Pi.add_apply, ← physicalBoxProfile_eq_anchored] using h

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
