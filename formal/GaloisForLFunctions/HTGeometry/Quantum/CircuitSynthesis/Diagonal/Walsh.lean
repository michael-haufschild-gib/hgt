import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw

/-! # Real Walsh expansion of a diagonal Hamiltonian -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def sign (a b : Bool) : ℝ := if a && b then -1 else 1

/-- Eigenvalue of the Z word with support a at computational configuration x. -/
def character (a x : ι → Bool) : ℝ := ∏ i, sign (a i) (x i)

/-- Identity or Pauli Z at each site. -/
def zWord (a : ι → Bool) (i : ι) : Option (Fin 3) := if a i then some 2 else none

theorem zWord_diagonal (a : ι → Bool) :
    finitePauliMatrix (zWord a) = diagonal (fun x => (character a x:ℂ)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp only [finitePauliMatrix,diagonal_apply_eq,character,Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    cases ha : a i <;> cases hx : x i <;>
      norm_num [zWord,ha,hx,sign,boolPauliOptionEntry,boolPauliOption,finiteQubitPauli,
        show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]
  · rw [diagonal_apply_ne _ h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases ha : a i <;> cases hx : x i <;> cases hy : y i <;>
      simp_all [zWord,boolPauliOptionEntry,boolPauliOption,finiteQubitPauli]

private theorem one_site (x y : Bool) :
    (∑ a : Bool, sign a x * sign a y) = if x=y then 2 else 0 := by
  cases x <;> cases y <;> norm_num [Fintype.sum_bool,sign]

theorem character_orthogonal (x y : ι → Bool) :
    (∑ a : ι → Bool, character a x * character a y) = if x=y then (2:ℝ)^Fintype.card ι else 0 := by
  simp only [character,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => sign a (x i)*sign a (y i))]
  simp_rw [one_site]
  by_cases h : x=y
  · subst y; simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Coefficient of a diagonal logarithm in the commuting Z basis. -/
def coefficient (f : (ι → Bool) → ℝ) (a : ι → Bool) : ℝ :=
  (∑ x, f x * character a x)/(2:ℝ)^Fintype.card ι

theorem walsh_inversion (f : (ι → Bool) → ℝ) (y : ι → Bool) :
    (∑ a, coefficient f a * character a y) = f y := by
  have h (a : ι → Bool) : coefficient f a * character a y =
      (∑ x, f x*(character a x * character a y))/(2:ℝ)^Fintype.card ι := by
    simp only [coefficient,div_mul_eq_mul_div,Finset.sum_mul,mul_assoc]
  simp_rw [h]
  rw [← Finset.sum_div,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,character_orthogonal]
  simp [mul_ite]

#print axioms walsh_inversion
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis
