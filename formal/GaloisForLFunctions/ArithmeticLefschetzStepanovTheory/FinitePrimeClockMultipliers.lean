import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.IntegralityActsOnlyOnTheTorsion
import GaloisForLFunctions.RHTower.BakerProof.BakerIteration
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Scalar endomorphisms of a finite prime-frequency monoid

A real scalar preserving a nonempty finite prime-frequency monoid is a
natural number. The finite integer span first makes it integral by the
determinant trick. Baker independence then makes its exponent matrix scalar.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {P : Finset Nat.Primes}

/-- Baker independence for an arbitrary finite set of prime logarithms. -/
theorem primeLog_algebraic_relation (c : P → ℝ)
    (hc : ∀ p, IsAlgebraic ℤ (c p))
    (h : ∑ p, c p * Real.log ((p : Nat.Primes) : ℕ) = 0) :
    ∀ p, c p = 0 := by
  classical
  let e := (Fintype.equivFin P).symm
  have hinj : Function.Injective (fun i => ((e i : Nat.Primes) : ℕ)) := by
    intro i j hij
    exact e.injective (Subtype.ext (Subtype.ext hij))
  have hrel : ∑ i, c (e i) * Real.log ((e i : Nat.Primes) : ℕ) = 0 := by
    rw [e.sum_comp (fun r : P => c r * Real.log ((r : Nat.Primes) : ℕ))]
    exact h
  have hz := RHTower.primeLog_algIndep (fun i => ((e i : Nat.Primes) : ℕ)) hinj
    (fun i => (e i).val.property) (fun i => c (e i)) (fun i => hc (e i)) hrel
  intro p
  simpa only [Equiv.apply_symm_apply] using hz (e.symm p)

/-- Stabilizing the finite prime-logarithm lattice forces an integral multiplier. -/
theorem isIntegral_of_prime_frequency_dilation (p : P) (a : ℝ)
    (A : P → P →₀ ℕ)
    (hA : ∀ r, frequency (A r) = a * Real.log ((r : Nat.Primes) : ℕ)) :
    IsIntegral ℤ a := by
  classical
  let lp : P → ℝ := fun r => Real.log ((r : Nat.Primes) : ℕ)
  let N := Submodule.span ℤ (Set.range lp)
  have hmem (r : P) : lp r ∈ N := Submodule.subset_span ⟨r, rfl⟩
  have hne : N ≠ ⊥ := by
    intro he
    have hp := hmem p
    rw [he, Submodule.mem_bot] at hp
    exact (ne_of_gt (Real.log_pos (by exact_mod_cast p.val.property.one_lt))) hp
  have hgen (r : P) : a * lp r ∈ N := by
    rw [← hA r]
    unfold frequency
    apply N.sum_mem
    intro q hq
    simpa only [zsmul_eq_mul, Int.cast_natCast] using
      N.smul_mem ((A r q : ℕ) : ℤ) (hmem q)
  apply isIntegral_of_smul_mem_submodule N hne
    (Submodule.fg_span (Set.finite_range lp)) a
  intro x hx
  change a * x ∈ N
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨r, rfl⟩ := hx; exact hgen r
  | zero => simpa only [mul_zero] using N.zero_mem
  | add x y hx hy hx' hy' => rw [mul_add]; exact N.add_mem hx' hy'
  | smul z x hx hx' =>
      rw [mul_smul_comm]
      exact N.smul_mem z hx'

/-- Every scalar endomorphism of the finite prime-frequency monoid is an Adams exponent. -/
theorem prime_frequency_dilation_is_nat (p : P) (a : ℝ) (A : P → P →₀ ℕ)
    (hA : ∀ r, frequency (A r) = a * Real.log ((r : Nat.Primes) : ℕ)) :
    ∃ n : ℕ, a = n ∧ ∀ r, A r = Finsupp.single r n := by
  classical
  have ha := (isIntegral_of_prime_frequency_dilation p a A hA).isAlgebraic
  let c : P → ℝ := fun r => (A p r : ℝ) - if r = p then a else 0
  have hc : ∀ r, IsAlgebraic ℤ (c r) := by
    intro r
    apply (isAlgebraic_nat (A p r)).sub
    split_ifs
    · exact ha
    · exact isAlgebraic_zero
  have hrel : ∑ r, c r * Real.log ((r : Nat.Primes) : ℕ) = 0 := by
    simp only [c, sub_mul, sum_sub_distrib, ite_mul, zero_mul]
    simp only [sum_ite_eq', mem_univ, if_true]
    exact sub_eq_zero.mpr (hA p)
  have hp := primeLog_algebraic_relation c hc hrel p
  have he : a = (A p p : ℝ) := by
    dsimp [c] at hp
    simp only [if_pos rfl] at hp
    exact (sub_eq_zero.mp hp).symm
  refine ⟨A p p, he, fun r => frequency_injective ?_⟩
  rw [hA r, he]
  simp only [frequency, Finsupp.single_apply, ite_mul, Nat.cast_ite,
    Nat.cast_zero, zero_mul, sum_ite_eq, mem_univ, if_true]

#print axioms prime_frequency_dilation_is_nat

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
