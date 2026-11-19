import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicIntegralOrder
import GaloisForLFunctions.HTGeometry.MonicResiduePairing

/-!
# The field trace and the monogenic trace dual of the orbit cubic

In the rational cubic field, let x denote the generator and set
δ = x(x−1)/f'(x). The actual field trace of δ times a product is the
ordinary dot product in the reciprocal basis. Thus the trace dual of
the monogenic order is δ times that same order. The reciprocal of δ is
a sum of three unit squares, proving total positivity at real embeddings.
-/

noncomputable section
open Polynomial
namespace RHTower.OrbitCubic.NumberFieldTrace
open GaloisForLFunctions.HTGeometry

def equation (m : ℤ) := (integralModel m).toPoly.map (Int.castRingHom ℚ)
instance irreducible_equation (m : ℤ) : Fact (Irreducible (equation m)) := ⟨integralModel_irreducible m⟩
abbrev K (m : ℤ) := AdjoinRoot (equation m)
abbrev root (m : ℤ) : K m := AdjoinRoot.root _

private theorem monic (m : ℤ) : (equation m).Monic :=
  (Cubic.monic_of_a_eq_one (P := integralModel m) rfl).map _

private theorem degree_three (m : ℤ) : (equation m).natDegree = 3 := by
  rw [equation,(Cubic.monic_of_a_eq_one (P := integralModel m) rfl).natDegree_map]
  exact Cubic.natDegree_of_a_ne_zero (P := integralModel m) (show (1:ℤ) ≠ 0 from one_ne_zero)

/-- Reciprocal units written as integral quadratic polynomials. -/
def U (m : ℤ) : K m := 2-(root m-m)*(root m-1)
def V (m : ℤ) : K m := (root m-m)*root m-2

theorem equation_normal (m : ℤ) :
    equation m = X^3-C ((m:ℚ)+1)*X^2+C ((m:ℚ)-2)*X+1 := by
  simp [equation,integralModel,Cubic.toPoly,Polynomial.C_ofNat]
  ring

/-- Multiplication and reciprocal relations in the cubic field. -/
theorem reciprocal_table (m : ℤ) :
    let x := root m
    x*U m = 1 ∧ (x-1)*V m = 1 ∧ x = m+U m+V m ∧ U m*V m = V m-U m ∧
      U m^2 = 1+(1-m)*U m-V m ∧ V m^2 = 1+U m-m*V m := by
  apply reciprocal_polynomial_table
  have h := congrArg (AdjoinRoot.mk (equation m)) (equation_normal m)
  rw [AdjoinRoot.mk_self] at h
  simp only [map_add,map_sub,map_mul,map_pow,map_one,AdjoinRoot.mk_X,
    map_intCast,map_ofNat] at h
  change 0 = (root m)^3-((m:K m)+1)*(root m)^2+((m:K m)-2)*root m+1 at h
  linear_combination -h

private def different (m : ℤ) : K m := AdjoinRoot.mk (equation m) (equation m).derivative
private theorem different_ne_zero (m : ℤ) : different m ≠ 0 := by
  have hsep : (equation m).Separable := (integralModel_irreducible m).separable
  obtain ⟨p,q,hpq⟩ := hsep
  intro hz
  have h := congrArg (AdjoinRoot.mk (equation m)) hpq
  change AdjoinRoot.mk (equation m) (equation m).derivative = 0 at hz
  simp only [map_add,map_mul,map_one,AdjoinRoot.mk_self,hz,mul_zero,zero_add] at h
  exact zero_ne_one h

/-- Trace-dual generator in the actual cubic number field. -/
def delta (m : ℤ) : K m := root m*(root m-1)/different m

/-- Real embeddings evaluate the generator at roots of the specialized
cubic and the two unit polynomials at the corresponding reciprocals. -/
theorem real_embedding_values (m : ℤ) (σ : K m →+* ℝ) :
    binary ((m:ℝ)-1/2) (σ (root m)) 1 = 0 ∧ σ (U m) = (σ (root m))⁻¹ ∧
      σ (V m) = (σ (root m)-1)⁻¹ := by
  obtain ⟨hu,hv,he,_⟩ := reciprocal_table m
  have a := congrArg σ hu
  have b := congrArg σ hv
  have c := congrArg σ he
  simp only [map_mul,map_one,map_add,map_sub,map_intCast] at a b c
  have nz {s t : ℝ} (h : s*t = 1) : s ≠ 0 := by intro z; rw [z,zero_mul] at h; exact zero_ne_one h
  refine ⟨?_,mul_left_cancel₀ (nz a) (a.trans (mul_inv_cancel₀ (nz a)).symm),
    mul_left_cancel₀ (nz b) (b.trans (mul_inv_cancel₀ (nz b)).symm)⟩
  rw [arrowhead_secular,sub_add_cancel]
  linear_combination (σ (root m)*(σ (root m)-1))*c + (σ (root m)-1)*a + σ (root m)*b

/-- Every real root induces a real embedding of the cubic field. -/
theorem embedding_of_real_root (m : ℤ) (x : ℝ) :
    binary ((m:ℝ)-1/2) x 1 = 0 → ∃ σ : K m →+* ℝ, σ (root m) = x := by
  intro hx
  have he : (equation m).eval₂ (Rat.castHom ℝ) x = 0 := by
    rw [equation,Polynomial.eval₂_map,show (Rat.castHom ℝ).comp (Int.castRingHom ℚ) =
      Int.castRingHom ℝ from Subsingleton.elim _ _,integral_real_specialization,hx]
  exact ⟨AdjoinRoot.lift (Rat.castHom ℝ) x he,by simp only [root,AdjoinRoot.lift_root]⟩

private def weightedTrace (m : ℤ) : K m →ₗ[ℚ] ℚ :=
  (monicResidue (monic m)).comp (Algebra.lmul ℚ (K m) (root m*(root m-1)))

private theorem field_trace (m : ℤ) (z : K m) :
    Algebra.trace ℚ (K m) (delta m*z) = weightedTrace m z := by
  refine (monic_trace_eq_residue_derivative (monic m) (delta m*z)).trans ?_
  change monicResidue (monic m) ((root m*(root m-1)/different m*z)*different m) =
    monicResidue (monic m) (root m*(root m-1)*z)
  congr 1
  rw [mul_right_comm _ z,div_mul_cancel₀ _ (different_ne_zero m)]

private theorem weights (m : ℤ) :
    weightedTrace m 1 = 1 ∧ weightedTrace m (U m) = 0 ∧ weightedTrace m (V m) = 0 := by
  let r := monicResidue (monic m)
  have h (j : ℕ) (hj : j < 3) : r (root m^j) = if j = 2 then 1 else 0 := by
    simpa only [degree_three] using monicResidue_root_pow (monic m) (j := j) (by rwa [degree_three])
  have h0 : r 1 = 0 := by simpa using h 0 (by norm_num)
  have h1 : r (root m) = 0 := by simpa using h 1 (by norm_num)
  have h2 : r (root m^2) = 1 := by simpa using h 2 (by norm_num)
  obtain ⟨hu,hv,_⟩ := reciprocal_table m
  change r (_*1) = 1 ∧ r (_*U m) = 0 ∧ r (_*V m) = 0
  rw [mul_one,show root m*(root m-1)*U m = root m-1 by linear_combination (root m-1)*hu,
    show root m*(root m-1)*V m = root m by linear_combination (root m)*hv,
    show root m*(root m-1) = root m^2-root m by ring,map_sub,map_sub,h0,h1,h2]
  norm_num

/-- Coordinates in the reciprocal basis of the cubic field. -/
def coords (m : ℤ) (a b c : ℚ) : K m := a • (1 : K m)+b • U m+c • V m

/-- The first rational coordinate is exactly the normalized field trace. -/
theorem trace_coords (m : ℤ) (a b c : ℚ) :
    Algebra.trace ℚ (K m) (delta m * coords m a b c) = a := by
  obtain ⟨h1,hU,hV⟩ := weights m
  simp only [field_trace,coords,map_add,map_smul,h1,hU,hV,smul_eq_mul,mul_one,mul_zero,add_zero]

private theorem coordinate_products (m : ℤ) :
    weightedTrace m (U m*U m) = 1 ∧ weightedTrace m (V m*V m) = 1 ∧
      weightedTrace m (U m*V m) = 0 := by
  obtain ⟨_,_,_,huv,hu,hv⟩ := reciprocal_table m
  obtain ⟨h1,hU,hV⟩ := weights m
  have hmu : (1-m:K m)*U m = ((1-(m:ℚ)) • U m) := by simp [Algebra.smul_def]
  have hmv : (m:K m)*V m = (m:ℚ) • V m := by simp [Algebra.smul_def]
  rw [← pow_two,← pow_two,hu,hv,huv,hmu,hmv]
  simp [map_smul,h1,hU,hV]

/-- Weighted trace is an isometry on the full rational field basis. -/
theorem trace_coords_product (m : ℤ) (a b c d e f : ℚ) :
    Algebra.trace ℚ (K m) (delta m*(coords m a b c*coords m d e f)) = a*d+b*e+c*f := by
  obtain ⟨h1,hU,hV⟩ := weights m
  obtain ⟨hu,hv,huv⟩ := coordinate_products m
  rw [field_trace]
  simp only [coords,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
    map_add,map_smul,smul_eq_mul,h1,hU,hV,hu,hv,huv,mul_comm (V m) (U m)]
  ring

private theorem gen_times (m : ℤ) (a b c : ℚ) :
    coords m a b c*root m = coords m ((m:ℚ)*a+b+c) a (a+c) := by
  obtain ⟨hu,hv,he,_⟩ := reciprocal_table m
  have hU : U m*root m=1 := (mul_comm _ _).trans hu
  have hV : V m*root m=1+V m := by linear_combination hv
  have hsc : a • (m:K m) = ((m:ℚ)*a) • (1:K m) := by
    simp only [Algebra.smul_def,map_mul,map_intCast,mul_one]
    exact mul_comm _ _
  have hroot := congrArg (fun z : K m => a • z) he
  change a • root m = a • ((m:K m)+U m+V m) at hroot
  simp only [smul_add,hsc] at hroot
  simp only [coords,add_mul,smul_mul_assoc,one_mul,hU,hV,smul_add,add_smul,hroot]
  abel

private theorem coords_add (m : ℤ) (a b c d e f : ℚ) :
    coords m a b c + coords m d e f = coords m (a+d) (b+e) (c+f) := by
  simp only [coords,add_smul]
  abel

private theorem polynomial_coords {R : Type*} [CommRing R] (m : ℤ) (g : R →+* ℚ) (k : R)
    (hk : g k = (m:ℚ)) (P : R[X]) :
    ∃ a b c : R, AdjoinRoot.mk (equation m) (P.map g) = coords m (g a) (g b) (g c) := by
  induction P using Polynomial.induction_on with
  | C a => exact ⟨a,0,0,by simp [coords,Algebra.smul_def]⟩
  | add P Q ih jh =>
    obtain ⟨a,b,c,h⟩ := ih
    obtain ⟨d,e,f,h'⟩ := jh
    exact ⟨a+d,b+e,c+f,by simp only [Polynomial.map_add,map_add,h,h',coords_add]⟩
  | monomial n a ih =>
    obtain ⟨u,v,w,h⟩ := ih
    exact ⟨k*u+v+w,u,u+w,by rw [pow_succ,← mul_assoc,Polynomial.map_mul,map_mul,Polynomial.map_X,
      AdjoinRoot.mk_X,h,gen_times]; simp only [map_add,map_mul,hk]⟩

/-- The reciprocal coordinates parametrize the entire number field uniquely. -/
theorem coords_bijective (m : ℤ) :
    Function.Bijective (fun p : ℚ × ℚ × ℚ => coords m p.1 p.2.1 p.2.2) := by
  constructor
  · rintro ⟨a,b,c⟩ ⟨d,e,f⟩ h
    change coords m a b c = coords m d e f at h
    have H (A B C : ℚ) : a*A+b*B+c*C = d*A+e*B+f*C := by
      rw [← trace_coords_product m,← trace_coords_product m,h]
    exact Prod.ext (by simpa using H 1 0 0) (Prod.ext (by simpa using H 0 1 0) (by simpa using H 0 0 1))
  · intro z
    obtain ⟨P,rfl⟩ := AdjoinRoot.mk_surjective z
    obtain ⟨a,b,c,h⟩ := polynomial_coords m (RingHom.id ℚ) (m:ℚ) rfl P
    exact ⟨(a,b,c),by simpa only [Polynomial.map_id,RingHom.id_apply] using h.symm⟩

/-- Integral polynomials in the generator, considered inside its number field. -/
def powerOrder (m : ℤ) : Set (K m) :=
  Set.range fun P : ℤ[X] => AdjoinRoot.mk (equation m) (P.map (Int.castRingHom ℚ))

private theorem integer_coords (m : ℤ) (a b c : ℤ) : coords m a b c ∈ powerOrder m := by
  refine ⟨C a + C b*(2-(X-C m)*(X-1)) + C c*((X-C m)*X-2),?_⟩
  simp [coords,U,V,Algebra.smul_def,root,AdjoinRoot.algebraMap_eq,map_ofNat]

/-- Integral coordinates characterize the monogenic order inside the field. -/
theorem powerOrder_eq_coords (m : ℤ) (z : K m) :
    z ∈ powerOrder m ↔ ∃ a b c : ℤ, z = coords m a b c := by
  constructor
  · rintro ⟨P,rfl⟩
    exact polynomial_coords m (Int.castRingHom ℚ) m rfl P
  · rintro ⟨a,b,c,rfl⟩
    exact integer_coords m a b c

/-- The trace dual here is taken against the monogenic order itself. -/
def orderTraceDual (m : ℤ) : Set (K m) := {y | ∀ z ∈ powerOrder m,
  ∃ a : ℤ, Algebra.trace ℚ (K m) (y*z) = (a:ℚ)}

private theorem delta_ne (m : ℤ) : delta m ≠ 0 := by
  obtain ⟨hu,hv,_⟩ := reciprocal_table m
  have nz {x y : K m} (h : x*y = 1) : x ≠ 0 := by intro hz; rw [hz,zero_mul] at h; exact zero_ne_one h
  exact div_ne_zero (mul_ne_zero (nz hu) (nz hv)) (different_ne_zero m)

private theorem different_value (m : ℤ) :
    different m = 3*root m^2-2*(m+1)*root m+(m-2) := by
  unfold different
  conv_lhs => arg 2; rw [equation_normal]
  simp [AdjoinRoot.mk_X,root]
  ring

/-- The inverse codifferent generator is the sum of the three reciprocal
basis squares. This identity holds in the field before choosing an embedding. -/
theorem inverse_delta_square_sum (m : ℤ) :
    delta m*(1+U m^2+V m^2) = 1 := by
  obtain ⟨hu,hv,_⟩ := reciprocal_table m
  have hd : root m*(root m-1)*(1+U m^2+V m^2) = different m := calc
    _ = root m*(root m-1)+(root m-1)*U m+root m*V m := by
      linear_combination (root m-1)*U m*hu + root m*V m*hv
    _ = root m*(root m-1)+2-U m+V m := by linear_combination hu + hv
    _ = _ := by rw [different_value]; unfold U V; ring
  unfold delta
  rw [div_mul_eq_mul_div₀,hd,div_self (different_ne_zero m)]

/-- Every real embedding sends the monogenic codifferent generator into
the open unit interval. Both inequalities are strict at all parameters. -/
theorem delta_real_bounds (m : ℤ) (σ : K m →+* ℝ) : 0 < σ (delta m) ∧ σ (delta m) < 1 := by
  have h := congrArg σ (inverse_delta_square_sum m)
  simp only [map_mul,map_add,map_one,map_pow] at h
  have hu := congrArg σ (reciprocal_table m).1
  simp only [map_mul,map_one] at hu
  have hU : σ (U m) ≠ 0 := by intro he; rw [he,mul_zero] at hu; exact zero_ne_one hu
  have hg : 1 < 1+σ (U m)^2+σ (V m)^2 := by linarith only [sq_pos_of_ne_zero hU,sq_nonneg (σ (V m))]
  have hp := zero_lt_one.trans hg
  rw [show σ (delta m) = 1/(1+σ (U m)^2+σ (V m)^2) from (eq_div_iff hp.ne').mpr h]
  exact ⟨div_pos zero_lt_one hp,(div_lt_one hp).mpr hg⟩

/-- The genuine field trace identifies the codifferent of this order as
a principal lattice. No maximal-order identification is required. -/
theorem codifferent_powerOrder (m : ℤ) :
    orderTraceDual m = (fun z => delta m*z) '' powerOrder m := by
  ext y
  constructor
  · intro hy
    obtain ⟨⟨a,b,c⟩,he⟩ := (coords_bijective m).2 (y/delta m)
    change coords m a b c = y/delta m at he
    have hY : y = delta m*coords m a b c := by rw [he,mul_div_cancel₀ _ (delta_ne m)]
    have read (i j k : ℤ) : ∃ z : ℤ, a*i+b*j+c*k = (z:ℚ) := by
      obtain ⟨z,h⟩ := hy _ (integer_coords m i j k)
      rw [hY,mul_assoc,trace_coords_product] at h
      exact ⟨z,h⟩
    obtain ⟨A,hA⟩ := read 1 0 0
    obtain ⟨B,hB⟩ := read 0 1 0
    obtain ⟨C,hC⟩ := read 0 0 1
    simp only [Int.cast_one,Int.cast_zero,mul_one,mul_zero,add_zero,zero_add] at hA hB hC
    exact ⟨coords m A B C,integer_coords m A B C,by simpa only [hA,hB,hC] using hY.symm⟩
  · rintro ⟨z,hz,rfl⟩ w hw
    obtain ⟨a,b,c,rfl⟩ := (powerOrder_eq_coords m z).mp hz
    obtain ⟨d,e,f,rfl⟩ := (powerOrder_eq_coords m w).mp hw
    exact ⟨a*d+b*e+c*f,by rw [mul_assoc,trace_coords_product]; push_cast; rfl⟩

#print axioms trace_coords
#print axioms real_embedding_values
#print axioms embedding_of_real_root
#print axioms trace_coords_product
#print axioms coords_bijective
#print axioms powerOrder_eq_coords
#print axioms codifferent_powerOrder
#print axioms inverse_delta_square_sum
#print axioms delta_real_bounds
end RHTower.OrbitCubic.NumberFieldTrace
