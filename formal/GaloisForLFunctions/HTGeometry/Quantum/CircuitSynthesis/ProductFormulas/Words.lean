import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NoncommRing

/-! # Entire exponential words and real rescalings -/
open NormedSpace Filter Set
namespace GaloisForLFunctions.HTGeometry.ProductFormula
noncomputable section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

/-- Evaluate the factors in their listed order, allowing complex time. -/
def word (w : List A) (z : ℂ) : A := (w.map fun x => exp (z • x)).prod

@[simp] theorem word_zero (w : List A) : word w 0 = 1 := by simp [word]

@[simp] theorem word_append (u v : List A) (z : ℂ) :
    word (u ++ v) z = word u z * word v z := by simp [word]

/-- Multiplying every generator by the same real coefficient rescales time. -/
def scaleWord (a : ℝ) (w : List A) : List A := w.map fun x => (a:ℂ) • x

@[simp] theorem word_scale (a : ℝ) (w : List A) (z : ℂ) :
    word (scaleWord a w) z = word w ((a:ℂ)*z) := by
  simp only [word,scaleWord,List.map_map,Function.comp_def,smul_smul,mul_comm z]

variable [CompleteSpace A]

theorem flow_add (x : A) (a b : ℂ) :
    exp (a • x) * exp (b • x) = exp ((a+b) • x) := by
  rw [add_smul,exp_add_of_commute (((Commute.refl x).smul_left a).smul_right b)]

/-- Negating time and reversing the order gives an entire inverse word. -/
theorem word_mul_reverse (w : List A) (z : ℂ) : word w z * word w.reverse (-z) = 1 := by
  induction w with
  | nil => simp [word]
  | cons x w ih =>
    simp only [List.reverse_cons,word_append]
    change (exp (z • x)*word w z)*(word w.reverse (-z)* (exp ((-z) • x)*1)) = 1
    rw [mul_one,mul_assoc,← mul_assoc (word w z),ih,one_mul,flow_add]
    simp

omit [CompleteSpace A] in
private theorem word_cons_fun (x : A) (w : List A) : word (x::w) =
    (fun z : ℂ => exp (z • x)) * word w := funext fun _ => by simp [word]

omit [CompleteSpace A] in
private theorem word_nil_fun : word ([] : List A) = fun _ => 1 := funext fun _ => by simp [word]

theorem word_entire (w : List A) : Differentiable ℂ (word w) := by
  induction w with
  | nil => rw [word_nil_fun]; exact differentiable_const _
  | cons x w ih =>
    rw [word_cons_fun]
    have hd : Differentiable ℂ (fun z : ℂ => exp (z • x)) := fun z => (hasDerivAt_exp_smul_const x z).differentiableAt
    exact hd.mul ih

theorem word_derivative_zero (w : List A) : HasDerivAt (word w) w.sum 0 := by
  induction w with
  | nil => simpa only [word_nil_fun,List.sum_nil] using (hasDerivAt_const (0:ℂ) (1:A))
  | cons x w ih =>
    have h := (hasDerivAt_exp_smul_const x (0:ℂ)).mul ih
    simpa only [zero_smul,exp_zero,one_mul,word_zero,mul_one,List.sum_cons,word_cons_fun] using h

/-- The total norm of a word bounds exponential growth at complex times. -/
def mass (w : List A) : ℝ := (w.map norm).sum

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem mass_nonneg (w : List A) : 0 ≤ mass w :=
  List.sum_nonneg (fun _ h => by obtain ⟨x,_,rfl⟩ := List.mem_map.mp h; exact norm_nonneg x)

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
@[simp] theorem mass_append (u v : List A) : mass (u++v) = mass u + mass v := by
  simp [mass]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
@[simp] theorem mass_reverse (w : List A) : mass w.reverse = mass w := by simp [mass,List.map_reverse]

omit [CompleteSpace A] in
@[simp] theorem mass_scale (a : ℝ) (w : List A) : mass (scaleWord a w) = |a| * mass w := by
  simp only [mass,scaleWord,List.map_map,Function.comp_def,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact List.sum_map_mul_left w norm |a|

end
end GaloisForLFunctions.HTGeometry.ProductFormula
