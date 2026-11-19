import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicFieldTrace
import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicPositiveTraceSlice

/-!
# Totally positive elements of weighted field trace one

In the actual cubic field, the trace-one integer slice of the monogenic
order has exactly three square directions and a triangular array of other
elements. Every member is additively indecomposable in the totally positive
order: the two summands would have strictly positive integral traces.
-/

noncomputable section
open Polynomial
namespace RHTower.OrbitCubic.NumberFieldTrace

/-- The image of integral polynomials as a subring of the cubic field. -/
def orderRing (m : ℤ) : Subring (K m) :=
  ((AdjoinRoot.mk (equation m)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))).range

theorem in_order {m : ℤ} {z : K m} : z ∈ orderRing m ↔ z ∈ powerOrder m := Iff.rfl

/-- Positivity at every real embedding of the cubic field. -/
def totallyPositive (m : ℤ) (z : K m) := ∀ σ : K m →+* ℝ, 0 < σ z

/-- The first reciprocal coordinate as a genuine weighted field trace. -/
def height (m : ℤ) (z : K m) := Algebra.trace ℚ (K m) (delta m*z)

/-- Monogenic integers in the totally positive height-one slice. -/
def heightOne (m : ℤ) := {z : K m | z ∈ powerOrder m ∧ totallyPositive m z ∧ height m z = 1}

theorem embedding_coordinates (m : ℤ) (σ : K m →+* ℝ) (a b c : ℚ) :
    σ (coords m a b c) = traceBasis a b c (σ (root m)) := by
  obtain ⟨_,hU,hV⟩ := real_embedding_values m σ
  simp [coords,Algebra.smul_def,traceBasis,hU,hV]

private theorem positive_iff_roots (m : ℤ) (a b c : ℚ) :
    totallyPositive m (coords m a b c) ↔
      ∀ x, binary ((m:ℝ)-1/2) x 1 = 0 → 0 < traceBasis a b c x := by
  constructor
  · intro h x hx
    obtain ⟨σ,rfl⟩ := embedding_of_real_root m x hx
    exact embedding_coordinates m σ a b c ▸ h σ
  · intro h σ
    rw [embedding_coordinates]
    exact h _ (real_embedding_values m σ).1

/-- Positive order integers have integral height at least one. -/
theorem positive_height_integral (m : ℤ) (z : {w : K m // w ∈ powerOrder m ∧ totallyPositive m w}) :
    ∃ a : ℤ, 1 ≤ a ∧ height m z.val = (a : ℚ) := by
  obtain ⟨a,b,c,e⟩ := (powerOrder_eq_coords m z.val).mp z.property.1
  have hp := z.property.2
  rw [e,positive_iff_roots] at hp
  obtain ⟨x,y,w,hx,hy,hw,px,py,pw,H⟩ := exists_orthonormal_trace_basis (m:ℝ)
  have ha : 0 < (a:ℝ) := by
    rw [← (H (a:ℝ) (b:ℝ) (c:ℝ)).1]
    apply add_pos (add_pos (mul_pos px _) (mul_pos py _)) (mul_pos pw _) <;>
      first | simpa only [Rat.cast_intCast] using hp _ hx
            | simpa only [Rat.cast_intCast] using hp _ hy
            | simpa only [Rat.cast_intCast] using hp _ hw
  have hi : 0 < a := by exact_mod_cast ha
  exact ⟨a,by omega,by rw [height,e,trace_coords]⟩

/-- Every element of weighted trace one is additively indecomposable among
totally positive monogenic integers. -/
theorem height_one_indecomposable (m : ℤ) (z : heightOne m) :
    ¬ ∃ a b : K m, a ∈ powerOrder m ∧ b ∈ powerOrder m ∧ totallyPositive m a ∧
      totallyPositive m b ∧ a+b = z.val := by
  rintro ⟨a,b,ha,hb,pa,pb,he⟩
  obtain ⟨i,hi,ei⟩ := positive_height_integral m ⟨a,ha,pa⟩
  obtain ⟨j,hj,ej⟩ := positive_height_integral m ⟨b,hb,pb⟩
  have hs : height m a + height m b = 1 := by
    calc
      _ = height m (a+b) := by simp only [height,mul_add,map_add]
      _ = 1 := he.symm ▸ z.property.2.2
  rw [ei,ej] at hs
  have hx : i+j = 1 := by exact_mod_cast hs
  omega

/-- The affine reciprocal-coordinate lattice identifies the actual number-field
slice, including its integral and positivity conditions. -/
def heightOneEquiv (m : ℤ) : {p : ℤ × ℤ // positiveSlice m p} ≃ heightOne m := by
  let f (p : ℤ × ℤ) := coords m 1 (-(p.1:ℚ)) (-(p.2:ℚ))
  have hpos (p : ℤ × ℤ) : totallyPositive m (f p) ↔ positiveSlice m p := by
    change totallyPositive m (coords m 1 _ _) ↔ _
    rw [positive_iff_roots]
    simp only [positiveSlice,Rat.cast_one,Rat.cast_neg,Rat.cast_intCast]
  let F (p : {p : ℤ × ℤ // positiveSlice m p}) : heightOne m := ⟨f p.val,
    (powerOrder_eq_coords _ _).mpr ⟨1,-p.val.1,-p.val.2,by simp [f]⟩,
    (hpos _).mpr p.property,trace_coords _ _ _ _⟩
  apply Equiv.ofBijective F
  constructor
  · intro p q he
    apply Subtype.ext
    have H : f p.val = f q.val := congrArg Subtype.val he
    have h := (coords_bijective m).1 (a₁ := ((1:ℚ),-(p.val.1:ℚ),-(p.val.2:ℚ)))
      (a₂ := ((1:ℚ),-(q.val.1:ℚ),-(q.val.2:ℚ))) H
    have h1 := congrArg (fun v : ℚ × ℚ × ℚ => v.2.1) h
    have h2 := congrArg (fun v : ℚ × ℚ × ℚ => v.2.2) h
    exact Prod.ext (by simpa using h1) (by simpa using h2)
  · intro z
    obtain ⟨a,b,c,he⟩ := (powerOrder_eq_coords _ _).mp z.property.1
    have ha := z.property.2.2
    rw [height,he,trace_coords] at ha
    have e : a = 1 := by exact_mod_cast ha
    subst a
    have hz : f (-b,-c) = z.val := by simpa only [f,Int.cast_neg,Int.cast_one,neg_neg] using he.symm
    exact ⟨⟨(-b,-c),(hpos _).mp (hz.symm ▸ z.property.2.1)⟩,Subtype.ext hz⟩

/-- Exact number of totally positive monogenic integers of normalized
field trace one in every nonnegative simplest cubic parameter. -/
theorem number_of_positive_height_one (n : ℕ) :
    Nat.card (heightOne ((n:ℤ)+2)) = 3+(n+2)*(n+1)/2 :=
  (Nat.card_congr (heightOneEquiv _).symm).trans (card_positive_slice n)

#print axioms positive_height_integral
#print axioms height_one_indecomposable
#print axioms heightOneEquiv
#print axioms number_of_positive_height_one
end RHTower.OrbitCubic.NumberFieldTrace
