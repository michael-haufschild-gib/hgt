import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicFieldTrace
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

/-!
# Norms in reciprocal coordinates on the cubic order

Multiplication is symmetric in the trace-orthonormal basis. On the triangular
height-one array the norm has a subtraction-free cyclic expression. Its least
value is attained exactly at the three vertices, and the centroid is the unique
maximizer in the real triangle.
-/

noncomputable section
namespace RHTower.OrbitCubic.NumberFieldTrace
open Matrix Module

/-- Multiplication in the reciprocal basis 1,U,V. -/
def reciprocalMatrix {R : Type*} [CommRing R] (m a b c : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a,b,c; b,a+(1-m)*b-c,c-b; c,c-b,a+b-m*c]

private def fromVector (m : ℤ) : (Fin 3 → ℚ) →ₗ[ℚ] K m where
  toFun x := coords m (x 0) (x 1) (x 2)
  map_add' x y := by simp only [Pi.add_apply,coords,add_smul]; abel
  map_smul' r x := by
    change coords m (r*x 0) (r*x 1) (r*x 2) = r • coords m (x 0) (x 1) (x 2)
    simp only [coords,smul_add,smul_smul]

/-- Synthesis from the three rational reciprocal coordinates. -/
def reciprocalEquiv (m : ℤ) : (Fin 3 → ℚ) ≃ₗ[ℚ] K m := by
  apply LinearEquiv.ofBijective (fromVector m)
  constructor
  · intro v w he
    have h := (coords_bijective m).1 (a₁ := (v 0,v 1,v 2)) (a₂ := (w 0,w 1,w 2)) he
    obtain ⟨h0,h12⟩ := Prod.mk.inj h
    obtain ⟨h1,h2⟩ := Prod.mk.inj h12
    funext j
    fin_cases j <;> assumption
  · intro z
    obtain ⟨⟨a,b,c⟩,he⟩ := (coords_bijective m).2 z
    exact ⟨![a,b,c],he⟩

/-- Product expansion in any commutative ring with the reciprocal multiplication table. -/
private theorem multiply_coordinates {R : Type*} [CommRing R]
    (m u v a b c x y z : R) (hu : u^2 = 1+(1-m)*u-v)
    (hv : v^2 = 1+u-m*v) (huv : u*v = v-u) :
    (a+b*u+c*v)*(x+y*u+z*v) =
      (a*x+b*y+c*z)+(b*x+(a+(1-m)*b-c)*y+(c-b)*z)*u+
        (c*x+(c-b)*y+(a+b-m*c)*z)*v := by
  linear_combination (b*y)*hu + (c*z)*hv + (b*z+c*y)*huv

/-- Multiplication by an arbitrary field element in reciprocal coordinates. -/
theorem reciprocalMatrix_action (m : ℤ) (a b c : ℚ) (v : Fin 3 → ℚ) :
    coords m a b c * reciprocalEquiv m v = reciprocalEquiv m ((reciprocalMatrix (m:ℚ) a b c).mulVec v) := by
  obtain ⟨_,_,_,huv,hu,hv⟩ := reciprocal_table m
  change coords m a b c * coords m (v 0) (v 1) (v 2) = coords m _ _ _
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  change _ = coords m (a*v 0+b*v 1+c*v 2)
    (b*v 0+(a+(1-(m:ℚ))*b-c)*v 1+(c-b)*v 2)
    (c*v 0+(c-b)*v 1+(a+b-(m:ℚ)*c)*v 2)
  simp only [coords,Algebra.smul_def,map_add,map_sub,map_one,map_mul,map_intCast,mul_one]
  exact multiply_coordinates _ _ _ _ _ _ _ _ _ hu hv huv

/-- Rational basis underlying the reciprocal integral lattice. -/
def reciprocalBasis (m : ℤ) := Basis.ofEquivFun (reciprocalEquiv m).symm

theorem reciprocalBasis_apply (m : ℤ) (j : Fin 3) :
    reciprocalBasis m j = reciprocalEquiv m (Pi.single j 1) := by
  simp [reciprocalBasis,Basis.coe_ofEquivFun]

/-- The regular representation of the cubic field in its integral basis. -/
theorem reciprocal_leftMulMatrix (m : ℤ) (a b c : ℚ) :
    Algebra.leftMulMatrix (reciprocalBasis m) (coords m a b c) =
      reciprocalMatrix (m:ℚ) a b c := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (Basis.ofEquivFun (reciprocalEquiv m).symm).repr (coords m a b c * reciprocalBasis m j) i = _
  rw [Basis.ofEquivFun_repr_apply,reciprocalBasis_apply,reciprocalMatrix_action,
    LinearEquiv.symm_apply_apply,Matrix.mulVec_single_one]
  rfl

/-- The determinant is the actual algebraic number-field norm. -/
theorem norm_coordinates (m : ℤ) (a b c : ℚ) :
    Algebra.norm ℚ (coords m a b c) = (reciprocalMatrix (m:ℚ) a b c).det := by
  rw [← reciprocal_leftMulMatrix]
  exact Algebra.norm_eq_matrix_det (reciprocalBasis m) (coords m a b c)

/-- Six-term determinant expansion in the three reciprocal coordinates. -/
theorem reciprocalMatrix_det {R : Type*} [CommRing R] (m a b c : R) :
    let d := a+(1-m)*b-c
    let e := c-b
    let f := a+b-m*c
    (reciprocalMatrix m a b c).det =
      a*d*f-a*e*e-b*b*f+b*e*c+c*b*e-c*d*c :=
  Matrix.det_fin_three _

/-- Every element of the order has an integral field norm. -/
theorem integral_norm (m : ℤ) (z : {w : K m // w ∈ powerOrder m}) :
    ∃ k : ℤ, Algebra.norm ℚ z.val = (k:ℚ) := by
  obtain ⟨a,b,c,he⟩ := (powerOrder_eq_coords m z.val).mp z.property
  refine ⟨(reciprocalMatrix m a b c).det,?_⟩
  rw [he,norm_coordinates]
  simp [reciprocalMatrix_det]

/-- The three cyclic factors in barycentric coordinates. -/
def arm {R : Type*} [CommSemiring R] (x y : R) := 1+x*(1+y)

def triangleNorm {R : Type*} [CommSemiring R] (a b c : R) :=
  arm a c * arm b a + arm b a * arm c b + arm c b * arm a c

theorem triangle_norm_cycle {R : Type*} [CommSemiring R] (a b c : R) :
    triangleNorm a b c = triangleNorm c a b := by unfold triangleNorm; ring

/-- Subtraction-free norm formula at every face and vertex of the triangular array. -/
theorem norm_barycentric (a b c : ℤ) :
    let m := a+b+c+2
    Algebra.norm ℚ (coords m 1 (-(a:ℚ)) (-(b+1:ℚ))) = (triangleNorm a b c : ℤ) := by
  intro m
  rw [norm_coordinates]
  rw [reciprocalMatrix_det]
  dsimp only [m,triangleNorm,arm]
  push_cast
  ring

private theorem excess {R : Type*} [CommRing R] (a b c : R) :
    triangleNorm a b c - (2*(a+b+c)+3) =
      2*(a*b+b*c+c*a) + (a*(1+c))*(b*(1+a))+
        (b*(1+a))*(c*(1+b))+(c*(1+b))*(a*(1+c)) := by unfold triangleNorm arm; ring

/-- On each triangle of fixed coordinate sum, the minimum occurs exactly at its vertices. -/
theorem lower_triangle_norm {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : {t : R // 0 ≤ t}) :
    let x : R := a
    let y : R := b
    let z : R := c
    2*(x+y+z)+3 ≤ triangleNorm x y z ∧
      (triangleNorm x y z = 2*(x+y+z)+3 ↔ x*y+y*z+z*x = 0) := by
  intro x y z
  have hx : 0 ≤ x := a.2
  have hy : 0 ≤ y := b.2
  have hz : 0 ≤ z := c.2
  have h := excess x y z
  have hxy : 0 ≤ x*y+y*z+z*x := by positivity
  have h1 : 0 ≤ x*(1+z)*(y*(1+x)) := by positivity
  have h2 : 0 ≤ y*(1+x)*(z*(1+y)) := by positivity
  have h3 : 0 ≤ z*(1+y)*(x*(1+z)) := by positivity
  refine ⟨by linarith only [h,hxy,h1,h2,h3],⟨fun he => by linarith only [h,he,hxy,h1,h2,h3],?_⟩⟩
  intro he
  have xy : x*y = 0 := by linarith only [he,mul_nonneg hx hy,mul_nonneg hy hz,mul_nonneg hz hx]
  have yz : y*z = 0 := by linarith only [he,mul_nonneg hx hy,mul_nonneg hy hz,mul_nonneg hz hx]
  have zx : z*x = 0 := by linarith only [he,mul_nonneg hx hy,mul_nonneg hy hz,mul_nonneg hz hx]
  apply sub_eq_zero.mp
  rw [h,he]
  linear_combination (1+z)*(1+x)*xy + (1+x)*(1+y)*yz + (1+y)*(1+z)*zx

private theorem spread {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (A B C : R) :
    (A+B+C)^2 - 3*(A*B+B*C+C*A) = ((A-B)^2+(B-C)^2+(C-A)^2)/2 := by ring

/-- The discriminant divided by 27 is the sharp norm ceiling. Equality characterizes the centroid. -/
theorem upper_triangle_norm {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : {t : R // 0 ≤ t}) :
    let x : R := a
    let y : R := b
    let z : R := c
    let s := x+y+z
    27*triangleNorm x y z ≤ (s^2+3*s+9)^2 ∧
      (27*triangleNorm x y z = (s^2+3*s+9)^2 ↔ x=y ∧ y=z) := by
  intro x y z s
  have hx : 0 ≤ x := a.2
  have hy : 0 ≤ y := b.2
  have hz : 0 ≤ z := c.2
  let S := arm x z+arm y x+arm z y
  have hA : 0 < S := by dsimp [S,arm]; positivity
  have hB : 3*triangleNorm x y z ≤ S^2 := by
    have h := spread (arm x z) (arm y x) (arm z y)
    unfold triangleNorm
    dsimp only [S]
    linarith only [h,sq_nonneg (arm x z-arm y x),sq_nonneg (arm y x-arm z y),sq_nonneg (arm z y-arm x z)]
  have he : s^2+3*s+9 - 3*S = ((x-y)^2+(y-z)^2+(z-x)^2)/2 := by dsimp [s,S,arm]; ring
  have hC : 3*S ≤ s^2+3*s+9 := by linarith only [he,sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]
  have hD := mul_self_le_mul_self (by linarith only [hA] : 0 ≤ 3*S) hC
  refine ⟨by nlinarith only [hB,hD],⟨?_,?_⟩⟩
  · intro hmax
    have eq : s^2+3*s+9 = 3*S := by
      by_contra hne
      have lt := lt_of_le_of_ne hC (Ne.symm hne)
      have hlt := mul_self_lt_mul_self (by linarith only [hA] : 0 ≤ 3*S) lt
      nlinarith only [hB,hmax,hlt]
    rw [eq,sub_self] at he
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp (by linarith only [he,sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)])),
      sub_eq_zero.mp (sq_eq_zero_iff.mp (by linarith only [he,sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]))⟩
  · rintro ⟨hxy,hyz⟩
    dsimp only [s]
    rw [hxy,hyz]
    unfold triangleNorm arm
    ring

#print axioms norm_coordinates
#print axioms integral_norm
#print axioms norm_barycentric
#print axioms lower_triangle_norm
#print axioms upper_triangle_norm
end RHTower.OrbitCubic.NumberFieldTrace
