import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Branches
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Grid

/-! # Realizing four-branch reflection by nonnegative prime occupations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder

open Finset Real Filter
open scoped Topology

variable {I : Type*} [Fintype I]

/-- Nonnegative occupations obtained by translating the two shifted and
two reflected spectra to a common energy origin. -/
def occupations (k : I → ℕ) (c : ℕ) : Four I → ℕ :=
  Sum.elim (Sum.elim (fun i => k i+2) k)
    (Sum.elim (fun i => c-k i+1) (fun i => c-k i+1))

/-- Bounding the old levels already forces doubled mean c+2 and upper
bound c+2 for the new occupations. -/
theorem lift_grid (k : I → ℕ) (c : ℕ) (bound : ∀ i, k i≤c) :
    (∀ i, occupations k c i≤c+2) ∧
    2*(∑ i, occupations k c i)=Fintype.card (Four I)*(c+2) := by
  constructor
  · rintro ((i | i) | (i | i)) <;> simp only [occupations,Sum.elim_inl,Sum.elim_inr] <;>
      have := bound i <;> omega
  · have per (i : I) : ((k i+2)+k i)+((c-k i+1)+(c-k i+1))=2*(c+2) := by
      have := bound i
      omega
    simp only [occupations,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,←sum_add_distrib,
      Fintype.card_sum]
    rw [sum_congr rfl (fun i _ => per i),sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]
    ring

theorem center_grid [Nonempty I] (k : I → ℕ) (c : ℕ)
    (align : 2*(∑ i, k i)=Fintype.card I*c) (i : I) :
    centered (levels k) i=(k i : ℝ)-(c : ℝ)/2 := by
  have h : 2*(∑ j, (k j : ℝ))=(Fintype.card I : ℝ)*(c : ℝ) := by exact_mod_cast align
  change (k i : ℝ)-(∑ j, (k j : ℝ))/(Fintype.card I : ℝ)=_
  congr 1
  apply (div_eq_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  linarith only [h]

omit [Fintype I] in
/-- Translating the four new branches by their common mean recovers the
reflection about c/2, for every bounded list of occupations. -/
theorem lift_raw (k : I → ℕ) (c : ℕ) (bound : ∀ i, k i≤c) :
    (fun x => (occupations k c x : ℝ)-((c+2 : ℕ) : ℝ)/2)=
      branches (fun i => (k i : ℝ)-(c : ℝ)/2) 1 := by
  funext x
  rcases x with (i | i) | (i | i) <;>
    simp only [occupations,branches,Sum.elim_inl,Sum.elim_inr,Nat.cast_add,Nat.cast_ofNat,
      Nat.cast_one,Nat.cast_sub (bound i)] <;> ring

/-- The centered natural occupations exactly realize the four-branch
spectrum. Selecting any elementary prime scales every level by its log. -/
theorem lift_centered (k : I → ℕ) (c : ℕ) (bound : ∀ i, k i≤c)
    (align : 2*(∑ i, k i)=Fintype.card I*c) :
    centered (levels (occupations k c))=branches (centered (levels k)) 1 := by
  funext x
  letI : Nonempty (Four I) := ⟨x⟩
  rw [center_grid _ _ (lift_grid k c bound).2]
  rcases x with (i | i) | (i | i) <;> letI : Nonempty I := ⟨i⟩ <;>
    simp only [occupations,branches,Sum.elim_inl,Sum.elim_inr,center_grid k c align,
      Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Nat.cast_sub (bound i)] <;> ring

#print axioms center_grid
#print axioms lift_raw
#print axioms lift_grid
#print axioms lift_centered

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder
