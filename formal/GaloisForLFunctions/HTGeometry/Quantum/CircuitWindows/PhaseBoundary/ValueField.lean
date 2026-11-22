import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic

/-! # Lifting polynomial coefficients over a field of specialized real values -/
open Polynomial
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
variable {A : Type*} [CommRing A]

/-- The fraction field of the image of an evaluation, embedded in the reals. -/
def valueField (φ : A→+*ℝ) : Subfield ℝ where
  carrier := {x | ∃ a b : A, φ b≠0 ∧ x*φ b=φ a}
  zero_mem' := ⟨0,1,by simp,by simp⟩
  one_mem' := ⟨1,1,by simp,by simp⟩
  add_mem' := by
    rintro x y ⟨a,b,hb,hx⟩ ⟨c,d,hd,hy⟩
    refine ⟨a*d+c*b,b*d,by rw [map_mul]; exact mul_ne_zero hb hd,?_⟩
    simp only [map_add,map_mul]
    rw [←hx,←hy]; ring
  neg_mem' := by
    rintro x ⟨a,b,hb,hx⟩
    exact ⟨-a,b,hb,by rw [neg_mul,hx,map_neg]⟩
  mul_mem' := by
    rintro x y ⟨a,b,hb,hx⟩ ⟨c,d,hd,hy⟩
    refine ⟨a*c,b*d,by rw [map_mul]; exact mul_ne_zero hb hd,?_⟩
    simp only [map_mul]; rw [←hx,←hy]; ring
  inv_mem' := by
    rintro x ⟨a,b,hb,hx⟩
    by_cases hz : x=0
    · subst x; exact ⟨0,1,by simp,by simp⟩
    · exact ⟨b,a,hx ▸ mul_ne_zero hz hb,by rw [←hx,←mul_assoc,inv_mul_cancel₀ hz,one_mul]⟩

/-- Evaluation with its natural field of values as codomain. -/
def specialize (φ : A→+*ℝ) : A→+*valueField φ where
  toFun a := ⟨φ a,a,1,by simp,by simp⟩
  map_one' := Subtype.ext φ.map_one
  map_zero' := Subtype.ext φ.map_zero
  map_add' a b := Subtype.ext (φ.map_add a b)
  map_mul' a b := Subtype.ext (φ.map_mul a b)

/-- Clear a whole polynomial at once. Only the value at the chosen base
point must have nonzero denominator. -/
theorem clear_polynomial (φ : A→+*ℝ) (p : (valueField φ)[X]) :
    ∃ d : A, φ d≠0 ∧ ∃ P : A[X], P.map (specialize φ)=C (specialize φ d)*p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨d,hd,P,hP⟩ := hp
    obtain ⟨e,he,Q,hQ⟩ := hq
    refine ⟨d*e,by rw [map_mul]; exact mul_ne_zero hd he,C e*P+C d*Q,?_⟩
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,hP,hQ,map_mul]
    ring
  | monomial n c =>
    obtain ⟨a,b,hb,h⟩ := c.property
    have he : specialize φ b*c=specialize φ a := Subtype.ext (by change φ b*c.val=φ a; rwa [mul_comm])
    refine ⟨b,hb,monomial n a,?_⟩
    rw [Polynomial.map_monomial,Polynomial.C_mul_monomial,he]

end GaloisForLFunctions.HTGeometry.PhaseBoundary
