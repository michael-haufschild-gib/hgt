import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceRotation

/-!
# All rational norm isometries of the cubic field

A linear map preserving field norm is multiplication by a norm-one element
followed by one of the three Galois maps. Comparing norms after translations
by 0, 1 and −1 first forces every vector to go to a conjugate. Four points
on a line parallel to the field generator then force a single conjugation
on the entire field. Preserving the codifferent height leaves exactly the
three rotations of the integral triangle.
-/

noncomputable section
namespace RHTower.OrbitCubic.NumberFieldTrace
open Matrix

private theorem coords_const (m : ℤ) (a : ℚ) : coords m a 0 0=algebraMap ℚ (K m) a := by
  simp [coords,Algebra.smul_def]

private theorem turn_coords (m : ℤ) (a b c : ℚ) :
    turn m (coords m a b c) = coords m (a+b-(m:ℚ)*c) (-c) (b-c) := by
  obtain ⟨_,_,hx,_⟩ := reciprocal_table m
  let g := algebraMap ℚ (K m)
  have hm (r : ℚ) : turn m (g r) = g r :=
    DFunLike.congr_fun (Subsingleton.elim ((turn m).comp g) g) r
  rw [coords_map m g,coords_map m g]
  simp only [map_add,map_mul,map_sub,map_neg,hm,(turn_units m).1,(turn_units m).2,map_intCast,hx]
  ring

private theorem mul_coords (m : ℤ) (a b c d e f : ℚ) :
    coords m a b c * coords m d e f = coords m (a*d+b*e+c*f)
      (b*d+(a+(1-m)*b-c)*e+(c-b)*f) (c*d+(c-b)*e+(a+b-m*c)*f) := by
  have h := reciprocalMatrix_action m a b c ![d,e,f]
  change coords m a b c * coords m d e f = coords m _ _ _ at h
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_three] at h
  exact h

/-- Actual field norm equals the product over the displayed conjugates. -/
theorem norm_conjugate_product (m : ℤ) (z : K m) :
    algebraMap ℚ (K m) (Algebra.norm ℚ z) = z*turn m z*turn m (turn m z) := by
  obtain ⟨⟨a,b,c⟩,rfl⟩ := (coords_bijective m).surjective z
  rw [← coords_const,norm_coordinates]
  simp only [turn_coords,mul_coords]
  rw [reciprocalMatrix_det]
  congr 1 <;> ring

private theorem translated_products {R : Type*} [Field R] [CharZero R] (a b c A B C : R)
    (h₀ : A*B*C=a*b*c)
    (hp : (A+1)*(B+1)*(C+1)=(a+1)*(b+1)*(c+1))
    (hm : (A-1)*(B-1)*(C-1)=(a-1)*(b-1)*(c-1)) :
    A=a ∨ A=b ∨ A=c := by
  have h1 : A+B+C=a+b+c := by linear_combination (hp+hm)/2-h₀
  have h2 : A*B+B*C+C*A=a*b+b*c+c*a := by linear_combination (hp-hm)/2
  have h : (A-a)*(A-b)*(A-c)=0 := by linear_combination A^2*h1-A*h2+h₀
  simpa only [mul_eq_zero,sub_eq_zero,or_assoc] using h

/-- The three rational embeddings of the field into itself. -/
def conjugateMap (m : ℤ) : Fin 3 → (K m →+* K m) :=
  ![RingHom.id _,turn m,(turn m).comp (turn m)]

private theorem pointwise_conjugate {m : ℤ} (B : K m →ₗ[ℚ] K m) (ho : B 1=1)
    (hn : ∀ z, Algebra.norm ℚ (B z)=Algebra.norm ℚ z) (z : K m) :
    ∃ i, B z = conjugateMap m i z := by
  have H (u : K m) := (norm_conjugate_product m (B u)).symm.trans <|
    (congrArg (algebraMap ℚ (K m)) (hn u)).trans (norm_conjugate_product m u)
  have hp := H (z+1)
  have hm := H (z-1)
  simp only [map_add,map_one,ho] at hp
  simp only [map_sub,map_one,ho] at hm
  rcases translated_products _ _ _ _ _ _ (H z) hp hm with e|e|e
  · exact ⟨0,e⟩
  · exact ⟨1,e⟩
  · exact ⟨2,e⟩

private theorem same_generator {m : ℤ} (f g : K m →+* K m) (he : f (root m)=g (root m)) :
    f=g := AdjoinRoot.ringHom_ext (Subsingleton.elim _ _) he

/-- A unital rational norm-preserving linear map is already a field map.
No invertibility assumption on the linear map is needed. -/
theorem unital_norm_rigidity (m : ℤ) (B : K m →ₗ[ℚ] K m) :
    (B 1=1 ∧ ∀ z, Algebra.norm ℚ (B z)=Algebra.norm ℚ z) →
    ∃ i : Fin 3, ∀ z, B z=conjugateMap m i z := by
  rintro ⟨h1,hN⟩
  obtain ⟨o,ho⟩ := pointwise_conjugate B h1 hN (root m)
  refine ⟨o,fun z => ?_⟩
  choose k hk using fun i : Fin 4 => pointwise_conjugate B h1 hN (z+i.val • root m)
  obtain ⟨i,j,hkij,hij⟩ : ∃ i j : Fin 4, k i=k j ∧ i≠j := by
    by_contra! h
    have hi : Function.Injective k := fun _ _ he => h _ _ he
    have hc := Fintype.card_le_of_injective _ hi
    simp at hc
  let f := conjugateMap m (k j)
  have hi := hk i
  have hj := hk j
  rw [hkij] at hi
  change B (z+i.val • root m)=f (z+i.val • root m) at hi
  change B (z+j.val • root m)=f (z+j.val • root m) at hj
  simp only [map_add,map_nsmul] at hi hj
  simp only [nsmul_eq_mul] at hi hj
  have hc : (i.val:K m)-(j.val:K m) ≠ 0 := by
    intro he
    exact hij (Fin.ext (by exact_mod_cast sub_eq_zero.mp he))
  have he : B (root m)=f (root m) := sub_eq_zero.mp <|
    (mul_eq_zero.mp (show ((i.val:K m)-j.val)*(B (root m)-f (root m))=0 by linear_combination hi-hj)).resolve_left hc
  have hh := same_generator f (conjugateMap m o) (he.symm.trans ho)
  rw [he,add_left_inj] at hi
  exact hi.trans (DFunLike.congr_fun hh z)

/-- Every rational linear norm isometry is a norm-one multiple of an actual
field endomorphism, with the multiplier equal to the image of one. -/
theorem norm_isometries (m : ℤ) (F : K m →ₗ[ℚ] K m) :
    (∀ z, Algebra.norm ℚ (F z)=Algebra.norm ℚ z) →
      Algebra.norm ℚ (F 1)=1 ∧ ∃ i : Fin 3, ∀ z, F z=F 1*conjugateMap m i z := by
  intro h
  have hw : Algebra.norm ℚ (F 1)=1 := (h 1).trans (map_one _)
  have h0 : F 1 ≠ 0 := (Algebra.norm_ne_zero_iff_of_basis (reciprocalBasis m)).mp
    (fun hz => one_ne_zero (hw.symm.trans hz))
  have hInv := congrArg (Algebra.norm ℚ) (inv_mul_cancel₀ h0)
  rw [map_mul (Algebra.norm ℚ),hw,mul_one,map_one (Algebra.norm ℚ)] at hInv
  let B := (Algebra.lmul ℚ (K m) (F 1)⁻¹).comp F
  have ho : B 1=1 := inv_mul_cancel₀ h0
  have hn (z : K m) : Algebra.norm ℚ (B z)=Algebra.norm ℚ z := by
    change Algebra.norm ℚ ((F 1)⁻¹*F z)=_
    rw [map_mul,hInv,one_mul,h]
  obtain ⟨i,he⟩ := unital_norm_rigidity m B ⟨ho,hn⟩
  refine ⟨hw,i,fun z => ?_⟩
  change _=F 1*conjugateMap m i z
  rw [← he]
  change _=F 1*((F 1)⁻¹*F z)
  rw [← mul_assoc,mul_inv_cancel₀ h0,one_mul]

private theorem height_separates (m : ℤ) {u v : K m}
    (h : ∀ z, height m (u*z)=height m (v*z)) : u=v := by
  by_contra hn
  have hn' := sub_ne_zero.mpr hn
  have h1 : height m 1=1 := by simpa [height,coords] using trace_coords m 1 0 0
  have h0 (z : K m) : height m ((u-v)*z)=0 := by
    have e := h z
    unfold height at e ⊢
    rw [sub_mul,mul_sub,map_sub,e,sub_self]
  have he := h0 (u-v)⁻¹
  rw [mul_inv_cancel₀ hn',h1] at he
  exact one_ne_zero he

private theorem twice_rotate (m : ℤ) (z : K m) :
    rotate m (rotate m z)=V m^2*turn m (turn m z) := by
  have he : U m*(1+V m)=V m := by linear_combination (reciprocal_table m).2.2.2.1
  rw [rotate,rotate,map_mul,map_pow,(turn_units m).1,← mul_assoc,← mul_pow,he]

/-- The height rotation has exact period three. Its orbit of the identity
already detects the nontrivial action. -/
theorem rotation_exact_period (m : ℤ) :
    (∀ z, rotate m (rotate m (rotate m z))=z) ∧ rotate m 1 ≠ 1 := by
  refine ⟨fun z => (rotation_invariants m z).2.2,?_⟩
  intro h
  have h₀ : coords m 1 0 0=1 := by simp [coords]
  have eq : coords m 1 ((1-(m:ℚ))*1-0-0) (0-1) = coords m 1 0 0 := by
    rw [← rotate_coords,h₀,h]
  have e := (coords_bijective m).injective
    (a₁ := (1,(1-(m:ℚ))*1-0-0,0-1)) (a₂ := (1,0,0)) eq
  have hf := congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) e
  norm_num at hf

/-- The full rational linear stabilizer of both height and field norm is
cyclic of order three. In particular there is no additional rational
reflection preserving these two measurements. -/
theorem norm_height_stabilizer (m : ℤ) (F : K m →ₗ[ℚ] K m) :
    (∀ z, Algebra.norm ℚ (F z)=Algebra.norm ℚ z ∧ height m (F z)=height m z) ↔
      (∀ z, F z=z) ∨ (∀ z, F z=rotate m z) ∨ (∀ z, F z=rotate m (rotate m z)) := by
  constructor
  · intro h
    obtain ⟨_,i,hi⟩ := norm_isometries m F fun z => (h z).1
    have s := fun z => (h z).2
    fin_cases i
    · change ∀ z, F z=F 1*z at hi
      have hw : F 1=1 := height_separates m fun z => by rw [← hi,one_mul,s]
      exact Or.inl fun z => by rw [hi,hw,one_mul]
    · change ∀ z, F z=F 1*turn m z at hi
      have he (z : K m) : height m (F 1*turn m z)=height m (U m^2*turn m z) := by
        rw [← hi,s]; exact (rotation_invariants m z).1.symm
      have hw : F 1=U m^2 := height_separates m fun z => by simpa only [turn_cube] using he (turn m (turn m z))
      exact Or.inr (Or.inl fun z => by rw [hi,hw,rotate])
    · change ∀ z, F z=F 1*turn m (turn m z) at hi
      have he (z : K m) : height m (F 1*turn m (turn m z))=height m (V m^2*turn m (turn m z)) := by
        rw [← hi,s,← twice_rotate,(rotation_invariants m (rotate m z)).1,(rotation_invariants m z).1]
      have hw : F 1=V m^2 := height_separates m fun z => by simpa only [turn_cube] using he (turn m z)
      exact Or.inr (Or.inr fun z => by rw [hi,hw,twice_rotate])
  · rintro (h|h|h) z
    · rw [h]; exact ⟨rfl,rfl⟩
    · rw [h]; exact ⟨(rotation_invariants m z).2.1,(rotation_invariants m z).1⟩
    · rw [h]; exact ⟨(rotation_invariants m _).2.1.trans (rotation_invariants m z).2.1,
        (rotation_invariants m _).1.trans (rotation_invariants m z).1⟩

end RHTower.OrbitCubic.NumberFieldTrace
