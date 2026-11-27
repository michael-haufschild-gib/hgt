import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Flow
import GaloisForLFunctions.HTGeometry.ZeroListBridge

/-! # Signed exponent multiplicities of a centered thermal comparison -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Zeros

open Finset Real
open GaloisForLFunctions.HTGeometry (expSum iteratedDeriv_expSum VanishesTo)

variable {I : Type*} [Fintype I]

private def frequency (E : I → ℝ) (r : ℝ) : ℝ := ∑ i, if E i=r then 1 else 0

def imbalance (E : I → ℝ) (r : ℝ) := frequency E r-frequency (fun i => -E i) r

private def shells (E : I → ℝ) := univ.image E ∪ univ.image (fun i => -E i)

def active (E : I → ℝ) := (shells E).filter (fun r => imbalance E r≠0)

/-- Signed exponent at a given rank after the multiplicities at opposite levels cancel. -/
def radius (E : I → ℝ) (i : Fin (active E).card) : ℝ := ((active E).orderIsoOfFin rfl i).val

theorem ordered (E : I → ℝ) : StrictMono (radius E) := fun _ _ h => ((active E).orderIsoOfFin rfl).strictMono h

theorem survives (E : I → ℝ) (i : Fin (active E).card) : imbalance E (radius E i)≠0 :=
  (mem_filter.mp (((active E).orderIsoOfFin rfl i).property)).2

theorem active_bound (E : I → ℝ) : (active E).card≤2*Fintype.card I := by
  calc (active E).card ≤ (shells E).card := card_filter_le _ _
       _ ≤ _ := card_union_le _ _
       _ ≤ univ.card+univ.card := add_le_add card_image_le card_image_le
       _ = _ := by rw [card_univ,two_mul]

private theorem count_sum (E : I → ℝ) (f : ℝ → ℝ) {B : Finset ℝ} (hb : ∀ i, E i∈B) :
    ∑ r ∈ B, frequency E r*f r=∑ i, f (E i) := by
  simp only [frequency,sum_mul,ite_mul,one_mul,zero_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => by simp [hb i]

/-- Combining repeated positive and negative exponents leaves precisely the signed
multiplicity of each surviving real level. This identity holds for every test function. -/
theorem expand (E : I → ℝ) (f : ℝ → ℝ) :
    ∑ i, imbalance E (radius E i)*f (radius E i)=∑ i, (f (E i)-f (-E i)) := by
  let g := fun r => imbalance E r*f r
  have fiber : (∑ i, g (radius E i)) = ∑ r ∈ active E, g r := by
    calc _ = ∑ r : active E, g r.val := Equiv.sum_comp ((active E).orderIsoOfFin rfl).toEquiv _
         _ = _ := sum_attach (active E) g
  change (∑ i, g (radius E i))=_
  rw [fiber]
  have ext : (∑ r ∈ active E, g r) = ∑ r ∈ shells E, g r := by
    apply sum_subset (filter_subset _ _)
    intro r hr absent
    have zero : imbalance E r=0 := by
      by_contra ne; exact absent (mem_filter.mpr ⟨hr,ne⟩)
    simp only [g,zero,zero_mul]
  rw [ext]
  simp only [g,imbalance,sub_mul,sum_sub_distrib]
  rw [count_sum (B := shells E) E f (fun i => mem_union_left _ (mem_image_of_mem _ (mem_univ i))),
    count_sum (B := shells E) (fun i => -E i) f (fun i => mem_union_right _ (mem_image_of_mem _ (mem_univ i)))]

theorem as_expSum (E : I → ℝ) :
    expSum (fun i => imbalance E (radius E i)) (radius E)=oddTrace E := by
  funext t
  have e := expand E (fun r => exp (r*t))
  simpa only [expSum,oddTrace,oddTerm,mul_comm t,neg_mul,mul_neg] using e

theorem active_pos {E : I → ℝ} {u : ℝ} (hu : oddTrace E u≠0) : 0<(active E).card := by
  by_contra! empty
  have no : IsEmpty (Fin (active E).card) := ⟨fun i => by have := i.isLt; omega⟩
  letI := no
  have h := congrFun (as_expSum E) u
  simp only [expSum,univ_eq_empty,sum_empty] at h
  exact hu h.symm

/-- Centering cancels the first derivative. Oddness cancels the zeroth and second
derivatives, giving at least a triple zero for every centered spectrum. -/
theorem triple_zero {E : I → ℝ} (hs : ∑ i, E i=0) : VanishesTo (oddTrace E) 3 0 := by
  intro j hj
  rw [← as_expSum,iteratedDeriv_expSum]
  simp only [expSum,mul_zero,exp_zero,mul_one]
  have moments := expand E (fun r => r^j)
  rw [moments]
  rcases (show j=0 ∨ j=1 ∨ j=2 by omega) with rfl | rfl | rfl
  · simp only [pow_zero,sub_self,sum_const_zero]
  · simp only [pow_one,sub_neg_eq_add,sum_add_distrib,hs,add_zero]
  · simp only [neg_sq,sub_self,sum_const_zero]

#print axioms expand
#print axioms triple_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Zeros
