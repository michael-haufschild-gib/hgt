import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicNormForm
import Mathlib.RingTheory.Discriminant

/-!
# Exact discriminant and minimum norm of the monogenic trace dual

The ordinary trace matrix in the reciprocal basis is multiplication by
the inverse weighted-trace generator. Consequently the discriminant is
(m²−m+7)² and the positive codifferent generator has reciprocal norm.
The minimum of the absolute norm on the punctured codifferent is attained
precisely on its translates by order units. This gives parameter ν=1 in
Oller, arXiv:2611.17965, Proposition 2.1, for the monogenic lattice.
-/

noncomputable section
namespace RHTower.OrbitCubic.NumberFieldTrace
open Matrix Module

/-- Ordinary field discriminant of the displayed basis of the order. -/
def orderDiscriminant (m : ℤ) := Algebra.discr ℚ (reciprocalBasis m)

private def invGenerator (m : ℤ) := coords m 3 (2-(m:ℚ)) (-(m:ℚ)-1)

private theorem generator_cancel (m : ℤ) : delta m*invGenerator m=1 := by
  obtain ⟨_,_,_,_,hu,hv⟩ := reciprocal_table m
  have h := inverse_delta_square_sum m
  rw [hu,hv] at h
  unfold invGenerator coords
  simp only [Algebra.smul_def,map_ofNat,map_sub,map_neg,map_intCast,map_one,mul_one]
  linear_combination h

private theorem dual_reading (m : ℤ) (i : Fin 3) (z : K m) :
    Algebra.trace ℚ (K m) (delta m*(reciprocalBasis m i*z)) = (reciprocalEquiv m).symm z i := by
  obtain ⟨w,rfl⟩ := (reciprocalEquiv m).surjective z
  rw [reciprocalBasis_apply,LinearEquiv.symm_apply_apply]
  have h (v : Fin 3 → ℚ) : Algebra.trace ℚ (K m) (delta m*(reciprocalEquiv m v*reciprocalEquiv m w)) =
      v ⬝ᵥ w := by
    change Algebra.trace ℚ (K m) (delta m*(coords m _ _ _*coords m _ _ _)) = _
    rw [trace_coords_product]
    simp only [dotProduct,Fin.sum_univ_three]
  rw [h]
  simp [dotProduct,Pi.single_apply]

/-- The trace Gram matrix is the regular representation of the inverse
different generator in the trace-orthonormal coordinates. -/
theorem order_trace_matrix (m : ℤ) :
    Algebra.traceMatrix ℚ (reciprocalBasis m) = reciprocalMatrix (m:ℚ) 3 (2-m) (-m-1) := by
  rw [← reciprocal_leftMulMatrix]
  ext i j
  rw [Algebra.traceMatrix_apply,Algebra.traceForm_apply,Algebra.leftMulMatrix_eq_repr_mul]
  change Algebra.trace ℚ (K m) (reciprocalBasis m i*reciprocalBasis m j) =
    (reciprocalEquiv m).symm (invGenerator m*reciprocalBasis m j) i
  rw [← dual_reading]
  congr 1
  linear_combination -(reciprocalBasis m i*reciprocalBasis m j)*generator_cancel m

private theorem det_inverse_matrix (m : ℚ) :
    (reciprocalMatrix m 3 (2-m) (-m-1)).det = (m^2-m+7)^2 := by
  rw [reciprocalMatrix_det]
  ring

/-- The square discriminant is computed inside the actual cubic field. -/
theorem actual_order_discriminant (m : ℤ) : orderDiscriminant m = ((m:ℚ)^2-m+7)^2 := by
  rw [orderDiscriminant,Algebra.discr_def,order_trace_matrix,det_inverse_matrix]

/-- Exact product of the discriminant with the positive generator's field norm. -/
theorem dual_generator_norm (m : ℤ) : Algebra.norm ℚ (delta m)*orderDiscriminant m = 1 := by
  have h := congrArg (Algebra.norm ℚ) (generator_cancel m)
  rw [actual_order_discriminant]
  simpa only [map_mul,map_one,invGenerator,norm_coordinates,det_inverse_matrix] using h

private def firstCofactors {R : Type*} [CommRing R] (m a b c : R) : Fin 3 → R :=
  let u := a+(1-m)*b-c
  let v := c-b
  let w := a+b-m*c
  ![u*w-v^2,c*v-b*w,b*v-c*u]

private theorem cofactor_product {R : Type*} [CommRing R] (m a b c : R) :
    (reciprocalMatrix m a b c).mulVec (firstCofactors m a b c) =
      ![(reciprocalMatrix m a b c).det,0,0] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,reciprocalMatrix,firstCofactors,
    Matrix.det_fin_three] <;> ring

/-- The numerator of the reciprocal of an order element is again in the
order, without assuming the norm is a unit. -/
theorem integral_inverse_numerator (m : ℤ) (z : {z : K m // z ∈ powerOrder m}) :
    ∃ y ∈ powerOrder m, z.val*y = algebraMap ℚ (K m) (Algebra.norm ℚ z.val) := by
  obtain ⟨a,b,c,h⟩ := (powerOrder_eq_coords m _).mp z.property
  let v := firstCofactors m a b c
  refine ⟨coords m (v 0) (v 1) (v 2),(powerOrder_eq_coords m _).mpr ⟨v 0,v 1,v 2,rfl⟩,?_⟩
  have hcast : (fun i => (v i:ℚ)) = firstCofactors (m:ℚ) a b c := by
    funext i
    fin_cases i <;> simp [v,firstCofactors]
  rw [h,norm_coordinates]
  change coords m (a:ℚ) b c * reciprocalEquiv m (fun i => (v i:ℚ)) = _
  rw [hcast,reciprocalMatrix_action,cofactor_product]
  change coords m _ 0 0 = _
  simp [coords,Algebra.smul_def]

/-- Norm ±1 is equivalent to invertibility inside the chosen order. -/
theorem order_unit_norm_iff (m : ℤ) (z : {z : K m // z ∈ powerOrder m}) :
    (∃ y ∈ powerOrder m, z.val*y=1) ↔ |Algebra.norm ℚ z.val|=1 := by
  constructor
  · rintro ⟨y,hy,he⟩
    obtain ⟨i,hi⟩ := integral_norm m z
    obtain ⟨j,hj⟩ := integral_norm m ⟨y,hy⟩
    have h := congrArg (Algebra.norm ℚ) he
    rw [map_mul,map_one,hi,hj] at h
    have hij : i*j=1 := by exact_mod_cast h
    rw [hi]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hij with h|h <;> simp [h]
  · intro h
    obtain ⟨y,hy,he⟩ := integral_inverse_numerator m z
    rcases (abs_eq (by norm_num : 0 ≤ (1:ℚ))).mp h with hp|hn
    · exact ⟨y,hy,by simpa [hp] using he⟩
    · obtain ⟨P,hP⟩ := hy
      have hneg : -y ∈ powerOrder m := ⟨-P,by simp [← hP]⟩
      exact ⟨-y,hneg,by rw [mul_neg,he,hn,map_neg,map_one,neg_neg]⟩

private theorem discr_pos (m : ℤ) : 0 < orderDiscriminant m := by
  rw [actual_order_discriminant]
  have h : 0 < (m:ℚ)^2-m+7 := by nlinarith only [sq_nonneg (2*(m:ℚ)-1)]
  exact sq_pos_of_pos h

/-- Every nonzero dual vector has a positive integral discriminant-scaled
absolute norm. The generator is a minimizer and all minimizers are exactly
its order-unit multiples. -/
theorem codifferent_minimum (m : ℤ) (y : {y : K m // y ∈ orderTraceDual m ∧ y ≠ 0}) :
    let S := |Algebra.norm ℚ y.val| * orderDiscriminant m
    (∃ k : ℤ, 1 ≤ k ∧ S=k) ∧ (S=1 ↔ ∃ z : {z : K m // z ∈ powerOrder m},
      (∃ w ∈ powerOrder m, z.val*w=1) ∧ y.val=delta m*z.val) := by
  have hpos := discr_pos m
  have hd := dual_generator_norm m
  have nd : 0 < Algebra.norm ℚ (delta m) :=
    pos_of_mul_pos_left (by rw [hd]; exact zero_lt_one) hpos.le
  have calcNorm (z : K m) : |Algebra.norm ℚ (delta m*z)| * orderDiscriminant m =
      |Algebra.norm ℚ z| := by rw [map_mul,abs_mul,abs_of_pos nd,mul_right_comm,hd,one_mul]
  obtain ⟨z,hz,he⟩ := (congrArg (fun S : Set (K m) => y.val ∈ S)
    (codifferent_powerOrder m)).mp y.property.1
  change delta m*z=y.val at he
  have hn : z ≠ 0 := by intro h; exact y.property.2 (by rw [← he,h,mul_zero])
  obtain ⟨k,hk⟩ := integral_norm m ⟨z,hz⟩
  change Algebra.norm ℚ z=(k:ℚ) at hk
  have hk0 : k ≠ 0 := by
    intro h
    have nz : Algebra.norm ℚ z ≠ 0 := (Algebra.norm_ne_zero_iff_of_basis (reciprocalBasis m)).mpr hn
    exact nz (hk.trans (by rw [h,Int.cast_zero]))
  have val : |Algebra.norm ℚ y.val| * orderDiscriminant m = |Algebra.norm ℚ z| := he ▸ calcNorm z
  refine ⟨⟨|k|,by have hh := abs_pos.mpr hk0; omega,by rw [val,hk,Int.cast_abs]⟩,?_⟩
  constructor
  · intro h
    exact ⟨⟨z,hz⟩,(order_unit_norm_iff m ⟨z,hz⟩).mpr (val.symm.trans h),he.symm⟩
  · rintro ⟨w,hw,hew⟩
    change |Algebra.norm ℚ y.val| * orderDiscriminant m=1
    rw [hew,calcNorm,(order_unit_norm_iff m w).mp hw]

end RHTower.OrbitCubic.NumberFieldTrace
