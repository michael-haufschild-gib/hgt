import GaloisForLFunctions.SelbergClass.Primon.PrincipalSeries
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Recovering continuous boundary data from its modular inversion defect

The principal-series inversion law in Hartnoll–Yang, arXiv:2502.02661v2,
(38), has weight of modulus `1/|x|`. On continuous periodic data, the weighted
inverted value therefore vanishes along integer translates. The inversion
defect recovers the original circle function in the limit. Its norm on the
half-line `x ≥ 1` lies between the original norm and twice that norm.
-/

open Set Filter Topology

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Principal-series inversion weight, including its totalized value at zero. -/
def boundaryInversionWeight (ε x : ℝ) : ℂ :=
  (|x|⁻¹ : ℝ) * Complex.exp (-principalParameter ε * (Real.log |x| : ℂ))

/-- The phase has unit modulus, leaving precisely the reciprocal dilation weight. -/
theorem norm_boundaryInversionWeight (ε x : ℝ) :
    ‖boundaryInversionWeight ε x‖ = |x|⁻¹ := by
  rw [boundaryInversionWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (abs_nonneg x)), Complex.norm_exp]
  simp [principalParameter]

/-- On a positive exponential coordinate the weight is exactly `exp (-2Δ log x)`. -/
theorem boundaryInversionWeight_exp (ε u : ℝ) :
    boundaryInversionWeight ε (Real.exp u) =
      Complex.exp (-2 * principalConformalWeight ε * (u : ℂ)) := by
  rw [boundaryInversionWeight, abs_of_pos (Real.exp_pos u), Real.log_exp,
    ← Real.exp_neg, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold principalParameter principalConformalWeight
  push_cast
  ring

/-- Failure of the weighted modular inversion law for continuous circle data. -/
def boundaryInversionDefect (ε : ℝ) (f : C(UnitAddCircle, ℂ)) (x : ℝ) : ℂ :=
  f (x : UnitAddCircle) - boundaryInversionWeight ε x * f ((-x⁻¹ : ℝ) : UnitAddCircle)

/-- The part of the defect lost in recovering the circle value decays explicitly. -/
theorem norm_boundaryInversionDefect_sub_le (ε : ℝ) (f : C(UnitAddCircle, ℂ)) (x : ℝ) :
    ‖boundaryInversionDefect ε f x - f (x : UnitAddCircle)‖ ≤ |x|⁻¹ * ‖f‖ := by
  have he : boundaryInversionDefect ε f x - f (x : UnitAddCircle) =
      -(boundaryInversionWeight ε x * f ((-x⁻¹ : ℝ) : UnitAddCircle)) := by
    unfold boundaryInversionDefect
    ring
  rw [he, norm_neg, norm_mul, norm_boundaryInversionWeight]
  exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f _)
    (inv_nonneg.mpr (abs_nonneg x))

private theorem circle_lift_nat_add (f : C(UnitAddCircle, ℂ)) (x : ℝ) (n : ℕ) :
    f ((x + (n : ℝ) : ℝ) : UnitAddCircle) = f (x : UnitAddCircle) := by
  have hp : Function.Periodic (fun x : ℝ => f (x : UnitAddCircle)) 1 := by
    intro y
    simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  simpa using hp.nat_mul n x

/-- Integer translates of the inversion defect recover every original circle value. -/
theorem tendsto_boundaryInversionDefect_nat_add (ε : ℝ)
    (f : C(UnitAddCircle, ℂ)) (x : ℝ) :
    Tendsto (fun n : ℕ => boundaryInversionDefect ε f (x + (n : ℝ)))
      atTop (𝓝 (f (x : UnitAddCircle))) := by
  have ht : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => |x + (n : ℝ)|⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_abs_atTop_atTop.comp ht)
  have hz : Tendsto (fun n : ℕ => boundaryInversionDefect ε f (x + (n : ℝ)) -
      f (x : UnitAddCircle)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa using hi.mul_const ‖f‖)
    simpa only [circle_lift_nat_add] using norm_boundaryInversionDefect_sub_le ε f (x + (n : ℝ))
  have h := hz.add_const (f (x : UnitAddCircle))
  simpa only [sub_add_cancel, zero_add] using h

private theorem continuous_boundaryInversionWeight_tail (ε : ℝ) :
    Continuous (fun x : Ici (1 : ℝ) => boundaryInversionWeight ε x) := by
  have hx : ∀ x : Ici (1 : ℝ), |(x : ℝ)| ≠ 0 := by
    intro x
    exact abs_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one x.property))
  have hl := (continuous_subtype_val.abs).log hx
  have hi := (continuous_subtype_val.abs).inv₀ hx
  exact (Complex.continuous_ofReal.comp hi).mul
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hl)))

private theorem continuous_boundaryInversionDefect_tail (ε : ℝ) (f : C(UnitAddCircle, ℂ)) :
    Continuous (fun x : Ici (1 : ℝ) => boundaryInversionDefect ε f x) := by
  have hc := f.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hi : Continuous (fun x : Ici (1 : ℝ) => -(x : ℝ)⁻¹) :=
    (continuous_subtype_val.inv₀ (fun x =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one x.property))).neg
  exact (hc.comp continuous_subtype_val).sub
    ((continuous_boundaryInversionWeight_tail ε).mul (hc.comp hi))

private theorem norm_boundaryInversionDefect_tail_le (ε : ℝ)
    (f : C(UnitAddCircle, ℂ)) (x : Ici (1 : ℝ)) :
    ‖boundaryInversionDefect ε f x‖ ≤ 2 * ‖f‖ := by
  have hx : 0 < (x : ℝ) := lt_of_lt_of_le zero_lt_one x.property
  have hi : |(x : ℝ)|⁻¹ ≤ 1 := by
    rw [abs_of_pos hx, ← one_div, div_le_iff₀ hx]
    simpa only [one_mul] using (show 1 ≤ (x : ℝ) from x.property)
  have hb := norm_boundaryInversionDefect_sub_le ε f x
  have hf := ContinuousMap.norm_coe_le_norm f (x : UnitAddCircle)
  have ht := norm_add_le
    (boundaryInversionDefect ε f x - f (x : UnitAddCircle)) (f (x : UnitAddCircle))
  rw [sub_add_cancel] at ht
  have hm := mul_le_mul_of_nonneg_right hi (norm_nonneg f)
  linarith

/-- The modular inversion defect restricted to `x ≥ 1` is bounded and continuous. -/
def tailBoundaryDefect (ε : ℝ) (f : C(UnitAddCircle, ℂ)) : BoundedContinuousFunction (Ici (1 : ℝ)) ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => boundaryInversionDefect ε f x, continuous_boundaryInversionDefect_tail ε f⟩
    (4 * ‖f‖) (by
      intro x y
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by
        have hx := norm_boundaryInversionDefect_tail_le ε f x
        have hy := norm_boundaryInversionDefect_tail_le ε f y
        change ‖boundaryInversionDefect ε f x‖ + ‖boundaryInversionDefect ε f y‖ ≤ 4 * ‖f‖
        linarith only [hx, hy]))

@[simp] theorem tailBoundaryDefect_apply (ε : ℝ) (f : C(UnitAddCircle, ℂ)) (x : Ici (1 : ℝ)) :
    tailBoundaryDefect ε f x = boundaryInversionDefect ε f x := rfl

/-- Upper norm control of the explicit defect map. -/
theorem norm_tailBoundaryDefect_le (ε : ℝ) (f : C(UnitAddCircle, ℂ)) :
    ‖tailBoundaryDefect ε f‖ ≤ 2 * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  exact norm_boundaryInversionDefect_tail_le ε f

/-- The defect retains at least the entire norm of the original circle data. -/
theorem norm_le_norm_tailBoundaryDefect (ε : ℝ) (f : C(UnitAddCircle, ℂ)) :
    ‖f‖ ≤ ‖tailBoundaryDefect ε f‖ := by
  apply (ContinuousMap.norm_le f (norm_nonneg _)).mpr
  intro z
  have hz : z ∈ ((↑) : ℝ → UnitAddCircle) '' Icc 0 (0 + 1) := by
    rw [AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨x, _, rfl⟩ := hz
  apply le_of_tendsto (tendsto_boundaryInversionDefect_nat_add ε f x).norm
  have ht : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
  exact BoundedContinuousFunction.norm_coe_le_norm (tailBoundaryDefect ε f) ⟨x + (n : ℝ), hn⟩

/-- The inversion defect is a linear, quantitatively faithful encoding of circle data. -/
def tailBoundaryDefectLinear (ε : ℝ) :
    C(UnitAddCircle, ℂ) →ₗ[ℂ] (BoundedContinuousFunction (Ici (1 : ℝ)) ℂ) where
  toFun := tailBoundaryDefect ε
  map_add' f g := by
    ext x
    change boundaryInversionDefect ε (f + g) x =
      boundaryInversionDefect ε f x + boundaryInversionDefect ε g x
    dsimp [boundaryInversionDefect]
    ring
  map_smul' c f := by
    ext x
    change boundaryInversionDefect ε (c • f) x = c * boundaryInversionDefect ε f x
    dsimp [boundaryInversionDefect]
    ring

/-- Continuity of the explicit defect encoding. -/
def tailBoundaryDefectContinuous (ε : ℝ) :
    C(UnitAddCircle, ℂ) →L[ℂ] (BoundedContinuousFunction (Ici (1 : ℝ)) ℂ) :=
  (tailBoundaryDefectLinear ε).mkContinuous 2 (norm_tailBoundaryDefect_le ε)

/-- Equality of modular defects forces equality of the original continuous boundary data. -/
theorem tailBoundaryDefect_injective (ε : ℝ) : Function.Injective (tailBoundaryDefect ε) := by
  intro f g h
  have hn := norm_le_norm_tailBoundaryDefect ε (f - g)
  change ‖f - g‖ ≤ ‖tailBoundaryDefectLinear ε (f - g)‖ at hn
  rw [map_sub, show tailBoundaryDefectLinear ε f = tailBoundaryDefectLinear ε g from h,
    sub_self, norm_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

/-- The weighted inversion law has no nonzero continuous periodic fixed vector. -/
theorem tailBoundaryDefect_eq_zero_iff (ε : ℝ) (f : C(UnitAddCircle, ℂ)) :
    tailBoundaryDefect ε f = 0 ↔ f = 0 := by
  have hzero : tailBoundaryDefect ε 0 = 0 := (tailBoundaryDefectLinear ε).map_zero
  rw [← hzero, (tailBoundaryDefect_injective ε).eq_iff]

/-- Recovery of continuous boundary data is stable under perturbations of the defect. -/
theorem antilipschitz_tailBoundaryDefect (ε : ℝ) :
    AntilipschitzWith 1 (tailBoundaryDefect ε) := by
  change AntilipschitzWith 1 (tailBoundaryDefectContinuous ε)
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro f
  have he : tailBoundaryDefectContinuous ε f = tailBoundaryDefect ε f := rfl
  simpa only [he, NNReal.coe_one, one_mul] using norm_le_norm_tailBoundaryDefect ε f

/-- Uniform limits of realizable inversion defects remain realizable. -/
theorem isClosed_range_tailBoundaryDefect (ε : ℝ) :
    IsClosed (Set.range (tailBoundaryDefect ε)) :=
  (antilipschitz_tailBoundaryDefect ε).isClosed_range
    (tailBoundaryDefectContinuous ε).uniformContinuous

end
end GaloisForLFunctions.SelbergClass.Primon
