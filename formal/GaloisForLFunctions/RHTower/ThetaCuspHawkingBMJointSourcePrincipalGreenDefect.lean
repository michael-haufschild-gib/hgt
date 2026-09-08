import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalLaplaceClassical
import GaloisForLFunctions.HTGeometry.RealSobolevBoundedProfile
import GaloisForLFunctions.HTGeometry.BoundedComplexDerivative
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGreenProfileBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalEquation

/-! Original transformed response minus original endpoint Green correction: actual homogeneous jets and bounds. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

def principalGreenDefect (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (x : ℝ) : ℂ :=
  principalLaplaceProfile q branch a i w hw x-
    principalDifference q branch w a (onsetTransform (2*physicalRate q branch) w) i x

def principalGreenDefectFirst (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (x : ℝ) : ℂ :=
  deriv (principalLaplaceProfile q branch a i w hw) x-
    principalDifferenceFirst q branch w a (onsetTransform (2*physicalRate q branch) w) i x

def principalHomogeneousCoefficient (q : XiZeroCopy) (i : Fin 3) (w : ℂ) (x : ℝ) : ℂ :=
  w^2-(horizonCoordinate x:ℂ)*principalExponent q i*(principalExponent q i-1)

/-- The actual Sobolev transform is uniformly bounded in space. -/
theorem principalLaplaceProfile_bounded (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖principalLaplaceProfile q branch a i w hw x‖ ≤ C :=
  continuous_sobolev_bounded _ 2 (by norm_num) (principalTimeLaplace_memSobolev q branch a i w hw)
    _ (principalLaplaceProfile_continuous q branch a i w hw) (principalLaplaceProfile_ae q branch a i w hw)

/-- Literal source cancellation gives the actual two-jet homogeneous comparison equation. -/
theorem principalGreenDefect_hasDerivAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (hc : PrincipalChamber q w)
    (x : ℝ) (hx : x < 0) :
    HasDerivAt (principalGreenDefect q branch a i w hw) (principalGreenDefectFirst q branch a i w hw x) x ∧
      HasDerivAt (principalGreenDefectFirst q branch a i w hw)
        (principalHomogeneousCoefficient q i w x*principalGreenDefect q branch a i w hw x) x := by
  have hu := principalLaplaceProfile_hasDerivAt q branch a i w hw x hx
  have hg := principalDifference_hasDerivAt q branch w a (onsetTransform (2*physicalRate q branch) w) hc i x hx
  constructor
  · exact hu.1.sub hg.1
  · apply (hu.2.sub hg.2).congr_deriv
    have he := principalDifference_equation q branch w a (onsetTransform (2*physicalRate q branch) w) hc i x hx
    rw [principalDifference_secondDerivative q branch w a _ hc i x hx] at he
    dsimp only [principalLaplaceSecond,principalHomogeneousCoefficient,principalGreenDefect]
    linear_combination he

/-- Both original endpoint limits force the actual comparison's endpoint to vanish. -/
theorem principalGreenDefect_boundary (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (hc : PrincipalChamber q w) :
    Tendsto (principalGreenDefect q branch a i w hw) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have h := (principalLaplaceProfile_boundary q branch a i w hw).sub
    (principalDifference_boundary q branch w a (onsetTransform (2*physicalRate q branch) w) hc i)
  simpa only [principalGreenDefect,sub_zero] using! h

/-- The actual homogeneous comparison has a uniform negative-ray value bound. -/
theorem principalGreenDefect_bounded (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (hc : PrincipalChamber q w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x < 0 → ‖principalGreenDefect q branch a i w hw x‖ ≤ C := by
  obtain ⟨C,hC,hf⟩ := principalLaplaceProfile_bounded q branch a i w hw
  obtain ⟨D,hD,hg⟩ := principalDifference_bounded q branch w a (onsetTransform (2*physicalRate q branch) w) hc i
  refine ⟨C+D,add_nonneg hC hD,fun x hx => (norm_sub_le _ _).trans (add_le_add (hf x) (hg x hx))⟩

/-- The original homogeneous coefficient has an explicit full-interior norm bound. -/
theorem principalHomogeneousCoefficient_norm_le (q : XiZeroCopy) (i : Fin 3) (w : ℂ)
    (x : ℝ) (hx : x < 0) :
    ‖principalHomogeneousCoefficient q i w x‖ ≤ ‖w‖^2+‖principalExponent q i‖*‖principalExponent q i-1‖ := by
  have hz := horizonCoordinate_interior x hx
  have hh : ‖(horizonCoordinate x:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg hz.1.le]
    exact hz.2.le
  unfold principalHomogeneousCoefficient
  calc
    _ ≤ ‖w^2‖+‖(horizonCoordinate x:ℂ)*principalExponent q i*(principalExponent q i-1)‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_pow,norm_mul,norm_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg (principalExponent q i)) hh)
        (norm_nonneg (principalExponent q i-1)))

/-- No horizon derivative condition is assumed: the actual equation and value bound supply it. -/
theorem principalGreenDefectFirst_bounded_tail (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (hc : PrincipalChamber q w) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, x < -1 → ‖principalGreenDefectFirst q branch a i w hw x‖ ≤ D := by
  obtain ⟨C,hC,hb⟩ := principalGreenDefect_bounded q branch a i w hw hc
  let M := ‖w‖^2+‖principalExponent q i‖*‖principalExponent q i-1‖
  have hM : 0 ≤ M := add_nonneg (sq_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨4*C+M*C,add_nonneg (mul_nonneg (by norm_num) hC) (mul_nonneg hM hC),fun x hx => ?_⟩
  have ht (t : ℝ) (ht : t ∈ Icc x (x+1)) : t < 0 := by linarith [ht.2]
  have hD : ContinuousOn (principalGreenDefect q branch a i w hw) (Icc x (x+1)) :=
    fun t ht' => (principalGreenDefect_hasDerivAt q branch a i w hw hc t (ht t ht')).1.continuousAt.continuousWithinAt
  have hQ : Continuous (principalHomogeneousCoefficient q i w) := by
    have hz := horizonCoordinate_continuous
    unfold principalHomogeneousCoefficient
    fun_prop
  exact norm_complex_deriv_le_of_bounded
    (fun t ht' => (principalGreenDefect_hasDerivAt q branch a i w hw hc t (ht t ht')).1)
    (fun t ht' => (principalGreenDefect_hasDerivAt q branch a i w hw hc t (ht t ht')).2)
    (hQ.continuousOn.mul hD) (fun t ht' => hb t (ht t ht')) (fun t ht' => by
      rw [norm_mul]
      exact mul_le_mul (principalHomogeneousCoefficient_norm_le q i w t (ht t ht')) (hb t (ht t ht'))
        (norm_nonneg _) hM)

end
end RHTower.D4BMJointSource
