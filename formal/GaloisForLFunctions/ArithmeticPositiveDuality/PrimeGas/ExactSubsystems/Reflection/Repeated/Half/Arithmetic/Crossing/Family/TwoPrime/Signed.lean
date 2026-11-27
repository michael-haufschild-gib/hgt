import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Gibbs

/-! # A simple centered spectrum from disjoint moment-matched blocks -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime

open Finset Real

variable {X : Type*} (A B : Finset X) (E : X → ℝ)

abbrev States := (↥A ⊕ ↥B)

/-- Keep the positive energies of one block and reverse those of the other. -/
def signedEnergy : States A B → ℝ := Sum.elim (fun i => E i.val) (fun j => -E j.val)

private def origin : States A B → X := Sum.elim Subtype.val Subtype.val

private theorem origin_injective (disj : Disjoint A B) : Function.Injective (origin A B) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Subtype.ext h)
    | inr y =>
      have xy : x.val=y.val := h
      exact (Finset.disjoint_left.mp disj x.property (xy.symm ▸ y.property)).elim
  | inr x =>
    cases y with
    | inl y =>
      have xy : x.val=y.val := h
      exact (Finset.disjoint_left.mp disj y.property (xy ▸ x.property)).elim
    | inr y => exact congrArg Sum.inr (Subtype.ext h)

private theorem absolute (pos : ∀ x, 0<E x) (i : States A B) :
    |signedEnergy A B E i|=E (origin A B i) := by
  cases i with
  | inl x => exact abs_of_pos (pos x.val)
  | inr y => exact (abs_neg _).trans (abs_of_pos (pos y.val))

/-- Distinct positive source energies and disjoint blocks give distinct absolute
energies, even across the two signs. -/
theorem absolute_injective (disj : Disjoint A B) (pos : ∀ x, 0<E x) (inj : Function.Injective E) :
    Function.Injective (fun i => |signedEnergy A B E i|) := by
  intro i j eq
  change |signedEnergy A B E i|=|signedEnergy A B E j| at eq
  rw [absolute A B E pos,absolute A B E pos] at eq
  exact origin_injective A B disj (inj eq)

theorem signed_zero (mean : (∑ x ∈ A, E x) = ∑ x ∈ B, E x) :
    (∑ i, signedEnergy A B E i)=0 := by
  simp only [signedEnergy,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_neg_distrib,
    Finset.sum_coe_sort,mean,add_neg_cancel]

/-- A nonempty centered list with distinct nonzero absolute energies has
no energy reflection. -/
theorem signed_asymmetric (disj : Disjoint A B) (non : A.Nonempty ∨ B.Nonempty)
    (pos : ∀ x, 0<E x) (inj : Function.Injective E) (mean : (∑ x ∈ A, E x) = ∑ x ∈ B, E x) :
    ¬Reflects (signedEnergy A B E) := by
  intro symm
  rw [reflects_iff_centered_pair,centered_eq_of_sum_zero (signed_zero A B E mean)] at symm
  obtain ⟨r,pair⟩ := symm
  obtain ⟨i⟩ : Nonempty (States A B) := by
    rcases non with ⟨x,hx⟩ | ⟨y,hy⟩
    · exact ⟨Sum.inl ⟨x,hx⟩⟩
    · exact ⟨Sum.inr ⟨y,hy⟩⟩
  have h := pair i
  have eq : signedEnergy A B E i= -signedEnergy A B E (r i) := by linarith only [h]
  have fix := absolute_injective A B E disj pos inj (show |signedEnergy A B E i|=|signedEnergy A B E (r i)| by
    conv_lhs => rw [eq]; rw [abs_neg])
  rw [← fix] at h
  have nz := pos (origin A B i)
  rw [← absolute A B E pos i,abs_pos] at nz
  exact nz (by linarith only [h])

/-- Equal direct and reciprocal moments cancel the odd trace of the signed spectrum. -/
theorem signed_agrees (mean : (∑ x ∈ A, E x) = ∑ x ∈ B, E x) (t : ℝ)
    (forward : (∑ x ∈ A, exp (t*E x))=∑ x ∈ B, exp (t*E x))
    (backward : (∑ x ∈ A, exp (-t*E x))=∑ x ∈ B, exp (-t*E x)) :
    agrees (signedEnergy A B E) t := by
  rw [agrees_odd,centered_eq_of_sum_zero (signed_zero A B E mean)]
  simp only [oddTrace,signedEnergy,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,oddTerm,mul_neg,
    neg_mul,neg_neg,sum_sub_distrib]
  rw [← sum_coe_sort A (fun x => exp (t*E x)),← sum_coe_sort B (fun x => exp (t*E x))] at forward
  rw [← sum_coe_sort A (fun x => exp (-t*E x)),← sum_coe_sort B (fun x => exp (-t*E x))] at backward
  simp only [neg_mul] at backward
  linarith only [forward,backward]

#print axioms absolute_injective
#print axioms signed_asymmetric
#print axioms signed_agrees

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime
