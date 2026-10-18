import GaloisForLFunctions.BiScaleUncertainty.SuccessorSequenceHilbert
import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearAndMultiplicativeGraphUncertainty

/-!
# Integer affine shear on the actual sequence Hilbert space

The adjoints of integer multiplicative pullback and additive successor produce
two distinct output coordinates. At a cofinal input index, either coordinate
recovers its own scale and annihilates every other scale, including larger ones.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.IntegerAffineShear
open SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

abbrev State := SequenceData ℝ

private theorem dilation_orthonormal (d : ℕ) :
    Orthonormal ℝ (fun n : ℕ => (lp.single 2 ((d+2)*n) (1 : ℝ) : State)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply, eq_comm]

/-- Integer dilation as a literal isometry, without a domain admission premise. -/
def dilation (d : ℕ) : State →ₗᵢ[ℝ] State :=
  (dilation_orthonormal d).orthogonalFamily.linearIsometry

theorem dilation_single (d n : ℕ) (a : ℝ) :
    dilation d (lp.single 2 n a) = lp.single 2 ((d+2)*n) a := by
  rw [dilation, (dilation_orthonormal d).orthogonalFamily.linearIsometry_apply_single]
  ext k
  by_cases h : k = (d+2)*n
  · subst k
    simp [lp.single_apply]
  · simp [lp.single_apply, Pi.single_eq_of_ne h]

/-- The adjoint is exactly the multiplicative pullback already used by discrete shear. -/
theorem dilation_adjoint_apply (d : ℕ) (v : State) (n : ℕ) :
    (dilation d).toContinuousLinearMap.adjoint v n = mulShift (d+2) v n := by
  have h := (dilation d).toContinuousLinearMap.adjoint_inner_right
    (lp.single 2 n (1 : ℝ)) v
  simpa [dilation_single, lp.inner_single_left, mulShift] using h

/-- Successor followed by dilation minus dilation followed by successor. -/
def shear (d : ℕ) : State →L[ℝ] State :=
  (sequenceRightShift ℝ).toContinuousLinearMap ∘L (dilation d).toContinuousLinearMap -
    (dilation d).toContinuousLinearMap ∘L (sequenceRightShift ℝ).toContinuousLinearMap

theorem shear_single (d n : ℕ) (a : ℝ) :
    shear d (lp.single 2 n a) =
      lp.single 2 ((d+2)*n+1) a - lp.single 2 ((d+2)*(n+1)) a := by
  simp only [shear, sub_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, dilation_single, sequenceRightShift_single]

/-- The new bounded operator is the adjoint of the existing discrete commutator, up to sign. -/
theorem shear_adjoint_apply (d : ℕ) (v : State) (n : ℕ) :
    (shear d).adjoint v n =
      mulShift (d+2) (addShift v) n - addShift (mulShift (d+2) v) n := by
  have h := (shear d).adjoint_inner_right (lp.single 2 n (1 : ℝ)) v
  simpa [shear_single, inner_sub_left, lp.inner_single_left, mulShift, addShift] using h

theorem norm_shear_le (d : ℕ) : ‖shear d‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  change ‖sequenceRightShift ℝ (dilation d v) - dilation d (sequenceRightShift ℝ v)‖ ≤ _
  calc
    _ ≤ ‖sequenceRightShift ℝ (dilation d v)‖ +
        ‖dilation d (sequenceRightShift ℝ v)‖ := norm_sub_le _ _
    _ = 2*‖v‖ := by simp [two_mul]

private theorem plus_ne_other_minus (d e n : ℕ)
    (he : 2 ≤ e) (hn : d ≤ n) : d*n+1 ≠ e*(n+1) := by
  intro h
  rw [Nat.mul_add, Nat.mul_one] at h
  by_cases hde : d ≤ e
  · have hm := Nat.mul_le_mul_right n hde
    omega
  · have hm := Nat.mul_le_mul_right n (show e+1 ≤ d by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega

private theorem minus_ne_other_plus (d e n : ℕ)
    (hd : 2 ≤ d) (hn : d ≤ n) : d*(n+1) ≠ e*n+1 := by
  intro h
  rw [Nat.mul_add, Nat.mul_one] at h
  by_cases hed : e ≤ d
  · have hm := Nat.mul_le_mul_right n hed
    omega
  · have hm := Nat.mul_le_mul_right n (show d+1 ≤ e by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega

/-- The positive output coordinate distinguishes one scale from every other scale. -/
theorem shear_single_plus (d e n : ℕ) (hn : d+2 ≤ n) :
    shear e (lp.single 2 n (1 : ℝ)) ((d+2)*n+1) = if e=d then 1 else 0 := by
  have hcross := plus_ne_other_minus (d+2) (e+2) n (by omega) hn
  have hn0 : n ≠ 0 := by omega
  simp [shear_single, lp.single_apply, Pi.single_apply, hcross, hn0, eq_comm]

/-- The negative output coordinate supplies a second independent scale readout. -/
theorem shear_single_minus (d e n : ℕ) (hn : d+2 ≤ n) :
    shear e (lp.single 2 n (1 : ℝ)) ((d+2)*(n+1)) = if e=d then -1 else 0 := by
  have hcross := minus_ne_other_plus (d+2) (e+2) n (by omega) hn
  by_cases h : e=d
  · subst e
    simp [shear_single, lp.single_apply, hcross]
  · simp [shear_single, lp.single_apply, hcross, h]

/-- The two arithmetic readouts are distinct even across different scale labels. -/
theorem output_coordinates_disjoint (d e n : ℕ) (hn : d+2 ≤ n) :
    (d+2)*n+1 ≠ (e+2)*(n+1) :=
  plus_ne_other_minus (d+2) (e+2) n (by omega) hn

end GaloisForLFunctions.BiScaleUncertainty.IntegerAffineShear
