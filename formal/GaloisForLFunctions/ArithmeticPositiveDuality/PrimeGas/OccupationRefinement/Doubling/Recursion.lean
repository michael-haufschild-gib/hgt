import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! # The proper-factor recursion of the occupation doubling equation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Doubling

open Finset ArithmeticFunction

/-- Doubling every elementary capacity counts two choices for each prime particle. -/
def law (F : ArithmeticFunction ℝ) := ∀ n, (F*F) n=(2:ℝ)^(cardFactors n)*F n

def interior (F : ArithmeticFunction ℝ) (n : ℕ) :=
  ∑ d ∈ n.properDivisors.erase 1, F (n/d)*F d

theorem vacuum {F : ArithmeticFunction ℝ} (h : law F) : F 1=0 ∨ F 1=1 := by
  have eqn := h 1
  have factors : cardFactors 1=0 := cardFactors_eq_zero_iff_eq_zero_or_one.mpr (Or.inr rfl)
  rw [ArithmeticFunction.mul_apply_one,factors,pow_zero,one_mul] at eqn
  have z : F 1*(F 1-1)=0 := by linear_combination eqn
  exact (mul_eq_zero.mp z).imp_right sub_eq_zero.mp

/-- Removing both endpoints leaves factors strictly smaller than the original shell. -/
theorem recursion {F : ArithmeticFunction ℝ} (h : law F) {n : ℕ} (hn : 1<n) :
    ((2:ℝ)^(cardFactors n)-2*F 1)*F n=interior F n := by
  have eqn := h n
  have hn0 : n≠0 := by omega
  have hone : 1∈n.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd _,hn⟩
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal' (fun x y => F x*F y),
    ←Nat.cons_self_properDivisors hn0,Finset.sum_cons,
    ←Finset.sum_erase_add n.properDivisors (fun d => F (n/d)*F d) hone,
    Nat.div_self (Nat.pos_of_ne_zero hn0),Nat.div_one] at eqn
  unfold interior
  linear_combination -eqn

theorem interior_congr {F G : ArithmeticFunction ℝ} {n : ℕ} (hn : 1<n)
    (ih : ∀ k<n, F k=G k) : interior F n=interior G n := by
  apply sum_congr rfl
  intro d hd
  obtain ⟨dvd,lt⟩ := Nat.mem_properDivisors.mp (mem_of_mem_erase hd)
  have hd0 := Nat.pos_of_dvd_of_pos dvd (by omega : 0<n)
  have hd1 := ne_of_mem_erase hd
  rw [ih d lt,ih (n/d) (Nat.div_lt_self (by omega) (by omega))]

theorem composite_coefficient {n : ℕ} (hn : 1<n) (hc : ¬ n.Prime) :
    0<(2:ℝ)^(cardFactors n)-2 := by
  have h0 : cardFactors n≠0 := fun h => (cardFactors_eq_zero_iff_eq_zero_or_one.mp h).elim
    (by omega) (by omega)
  have h1 : cardFactors n≠1 := fun h => hc (cardFactors_eq_one_iff_prime.mp h)
  have large : 1<cardFactors n := by omega
  simpa only [pow_one,sub_pos] using pow_lt_pow_right₀ (by norm_num : 1<(2:ℝ)) large

#print axioms vacuum
#print axioms recursion
#print axioms composite_coefficient

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Doubling
