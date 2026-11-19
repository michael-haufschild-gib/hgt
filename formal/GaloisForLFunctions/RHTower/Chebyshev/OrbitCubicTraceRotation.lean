import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceOneElements
import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicNormForm

/-!
# The cyclic symmetry of the height-one triangle

The field substitution x ↦ 1−1/x cyclically permutes the conjugates.
It changes the positive codifferent generator by the unit 1/x².
Multiplying the substituted element by that same unit gives a linear
rotation preserving height, norm and the positive integral slice.
The three unit squares form an orbit and the other orbits rotate the
three barycentric coordinates of the Shanks triangle.
-/

noncomputable section
namespace RHTower.OrbitCubic.NumberFieldTrace
open Polynomial

/-- Factorization over the cubic field, before choosing a real embedding. -/
theorem conjugate_factorization (m : ℤ) (z : K m) :
    (equation m).eval₂ (algebraMap ℚ (K m)) z =
      (z-root m)*(z-(1-U m))*(z-(-V m)) := by
  obtain ⟨hu,hv,he,huv,_⟩ := reciprocal_table m
  have e₁ : root m+(1-U m)+(-V m) = (m:K m)+1 := by linear_combination he
  have e₂ : root m*(1-U m)+root m*(-V m)+(1-U m)*(-V m) = (m:K m)-2 := by
    linear_combination he-hu-hv+huv
  have e₃ : root m*(1-U m)*(-V m) = -1 := by linear_combination (V m)*hu-hv
  rw [equation_normal]
  simp only [eval₂_add,eval₂_sub,eval₂_pow,eval₂_X,eval₂_mul,eval₂_C,eval₂_one,
    map_add,map_sub,map_one,map_ofNat,map_intCast]
  linear_combination z^2*e₁-z*e₂+e₃

/-- The generator of the ordinary Galois action. -/
def turn (m : ℤ) : K m →+* K m :=
  AdjoinRoot.lift (algebraMap ℚ (K m)) (1-U m) (by rw [conjugate_factorization]; simp)

theorem turn_root (m : ℤ) : turn m (root m) = 1-U m := AdjoinRoot.lift_root _

/-- The images of both reciprocal units under the ordinary field automorphism. -/
theorem turn_units (m : ℤ) : turn m (U m) = 1+V m ∧ turn m (V m) = -root m := by
  obtain ⟨hu,hv,_,huv,_⟩ := reciprocal_table m
  have h1 := congrArg (turn m) hu
  have h2 := congrArg (turn m) hv
  simp only [map_mul,map_sub,map_one,turn_root] at h1 h2
  have cancel {x y z : K m} (hy : x*y=1) (hz : x*z=1) : y=z := by
    apply mul_left_cancel₀ (a := x) _ (hy.trans hz.symm)
    intro h
    rw [h,zero_mul] at hy
    exact zero_ne_one hy
  exact ⟨cancel h1 (by linear_combination -huv),cancel h2 (by linear_combination hu)⟩

private theorem ext_generator {m : ℤ} {f g : K m →+* K m} (h : f (root m) = g (root m)) : f=g :=
  AdjoinRoot.ringHom_ext (Subsingleton.elim _ _) h

/-- Every element returns after three substitutions. -/
theorem turn_cube (m : ℤ) (z : K m) : turn m (turn m (turn m z)) = z := by
  have h : (turn m).comp ((turn m).comp (turn m)) = RingHom.id _ := by
    apply ext_generator
    simp only [RingHom.comp_apply,RingHom.id_apply,turn_root,map_sub,map_neg,map_one,
      (turn_units m).1,(turn_units m).2,map_add]
    ring
  exact DFunLike.congr_fun h z

/-- The displayed three endomorphisms exhaust the rational cubic's internal embeddings. -/
theorem all_field_maps (m : ℤ) (σ : K m →+* K m) :
    σ = RingHom.id _ ∨ σ = turn m ∨ σ = (turn m).comp (turn m) := by
  have h := AdjoinRoot.eval₂_root (equation m)
  have hx : (equation m).eval₂ (algebraMap ℚ (K m)) (σ (root m)) = 0 := by
    have he := congrArg σ h
    rw [Polynomial.hom_eval₂] at he
    simpa only [show σ.comp (AdjoinRoot.of (equation m)) = algebraMap ℚ (K m) from
      Subsingleton.elim _ _,map_zero] using he
  rw [conjugate_factorization,mul_eq_zero,mul_eq_zero] at hx
  rcases hx with (hx|hx)|hx
  · exact Or.inl (ext_generator (sub_eq_zero.mp hx))
  · exact Or.inr (Or.inl (ext_generator ((sub_eq_zero.mp hx).trans (turn_root m).symm)))
  · right; right
    apply ext_generator
    simp only [RingHom.comp_apply,turn_root,map_sub,map_one,(turn_units m).1]
    linear_combination hx

/-- Twist of a field conjugation by the square unit preserving the weighted trace. -/
def rotate (m : ℤ) (z : K m) := U m^2*turn m z

/-- In the reciprocal integral basis the twisted action has integral coefficients. -/
theorem rotate_coords (m : ℤ) (a b c : ℚ) :
    rotate m (coords m a b c) = coords m a ((1-(m:ℚ))*a-b-c) (b-a) := by
  obtain ⟨hu,_,_,huv,hU,_⟩ := reciprocal_table m
  have hUV : U m*(1+V m)=V m := by linear_combination huv
  have hc (r : ℚ) : turn m (algebraMap ℚ (K m) r) = algebraMap ℚ (K m) r :=
    DFunLike.congr_fun (Subsingleton.elim ((turn m).comp (algebraMap ℚ (K m))) (algebraMap ℚ (K m))) r
  simp only [rotate,coords,Algebra.smul_def,map_add,map_sub,map_mul,map_one,mul_one,
    hc,(turn_units m).1,(turn_units m).2,map_intCast]
  linear_combination (algebraMap ℚ (K m) a)*hU +
    (algebraMap ℚ (K m) b)*(U m)*hUV + (algebraMap ℚ (K m) b)*huv -
    (algebraMap ℚ (K m) c)*(U m)*hu

/-- The rotated codifferent generator changes by the square unit U². -/
theorem turn_generator (m : ℤ) : turn m (delta m) = U m^2*delta m := by
  obtain ⟨hu,hv,_⟩ := reciprocal_table m
  have hd := inverse_delta_square_sum m
  have ht := congrArg (turn m) hd
  simp only [map_mul,map_add,map_one,map_pow,(turn_units m).1,(turn_units m).2] at ht
  have hV : root m*V m = 1+V m := by linear_combination hv
  have hsq : root m^2*(1+U m^2+V m^2) = 1+(1+V m)^2+(-root m)^2 := by
    rw [show root m^2*(1+U m^2+V m^2) = root m^2+(root m*U m)^2+(root m*V m)^2 by ring,
      hu,hV]
    ring
  have he : turn m (delta m)*root m^2 = delta m := by
    have hc : 1+U m^2+V m^2 ≠ 0 := by intro h; rw [h,mul_zero] at hd; exact zero_ne_one hd
    apply mul_right_cancel₀ hc
    rw [mul_assoc,hsq,ht,hd]
  have h1 : (root m)^2*(U m)^2=1 := by rw [← mul_pow,hu,one_pow]
  linear_combination (U m)^2*he - turn m (delta m)*h1

/-- The twisted action preserves both rational height and actual field norm. -/
theorem rotation_invariants (m : ℤ) (z : K m) :
    height m (rotate m z) = height m z ∧ Algebra.norm ℚ (rotate m z) = Algebra.norm ℚ z ∧
    rotate m (rotate m (rotate m z)) = z := by
  obtain ⟨⟨a,b,c⟩,rfl⟩ := (coords_bijective m).surjective z
  simp only [rotate_coords,height,trace_coords,norm_coordinates]
  refine ⟨rfl,?_,?_⟩
  · simp only [reciprocalMatrix_det] <;> ring
  · congr 1 <;> ring

private theorem positive_rotates {m : ℤ} {z : K m} (h : totallyPositive m z) :
    totallyPositive m (rotate m z) := by
  intro σ
  have hu := congrArg σ (reciprocal_table m).1
  simp only [map_mul,map_one] at hu
  have hU : σ (U m) ≠ 0 := by intro hz; rw [hz,mul_zero] at hu; exact zero_ne_one hu
  simpa only [rotate,map_mul,map_pow] using mul_pos (sq_pos_of_ne_zero hU) (h (σ.comp (turn m)))

private theorem in_order_rotates {m : ℤ} {z : K m} (h : z ∈ powerOrder m) :
    rotate m z ∈ powerOrder m := by
  obtain ⟨a,b,c,rfl⟩ := (powerOrder_eq_coords m z).mp h
  apply (powerOrder_eq_coords m _).mpr
  exact ⟨a,(1-m)*a-b-c,b-a,by simpa only [Int.cast_sub,Int.cast_mul,Int.cast_one] using rotate_coords m a b c⟩

/-- On the positive integral slice, twisted conjugation is a permutation of order dividing three. -/
def sliceRotation (m : ℤ) : heightOne m ≃ heightOne m := by
  let f (z : heightOne m) : heightOne m := ⟨rotate m z.val,in_order_rotates z.property.1,
    positive_rotates z.property.2.1,(rotation_invariants m z.val).1.trans z.property.2.2⟩
  have h (z : heightOne m) : f (f (f z)) = z := Subtype.ext (rotation_invariants m z.val).2.2
  exact ⟨f,f ∘ f,h,h⟩

/-- The twisted Galois action rotates the ordered barycentric triple (a,b,c) to (c,a,b). -/
theorem rotate_triangle (a b c : ℤ) :
    let m := a+b+c+2
    rotate m (coords m 1 (-(a:ℚ)) (-((b:ℚ)+1))) = coords m 1 (-(c:ℚ)) (-((a:ℚ)+1)) := by
  intro m
  rw [rotate_coords]
  dsimp only [m]
  push_cast
  congr 1 <;> ring

/-- At rational height one the center is the only fixed point of twisted conjugation. -/
theorem rotation_fixed_point (m : ℤ) (a b : ℚ) :
    rotate m (coords m 1 a b) = coords m 1 a b ↔ 3*a=2-(m:ℚ) ∧ b=a-1 := by
  rw [rotate_coords]
  constructor
  · intro h
    have he := (coords_bijective m).injective (a₁ := (1,(1-(m:ℚ))*1-a-b,a-1)) (a₂ := (1,a,b)) h
    have h₁ := congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) he
    have h₂ := congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) he
    change (1-(m:ℚ))*1-a-b=a at h₁
    change a-1=b at h₂
    exact ⟨by linarith only [h₁,h₂],h₂.symm⟩
  · rintro ⟨h₁,h₂⟩
    congr 1 <;> linarith only [h₁,h₂]

end RHTower.OrbitCubic.NumberFieldTrace
