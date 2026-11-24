import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Filter.AtTopBot.Finite

/-! # Integer energy gradings that separate prescribed arithmetic labels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Polynomial Filter

/-- Prime occupations as coefficients, with the prime itself indexing its monomial. -/
def occupationPolynomial (n : ℕ) : ℕ[X] := ⟨⟨n.factorization⟩⟩

/-- The prime p has integer energy t^p. -/
def grade (t n : ℕ) : ℕ := (occupationPolynomial n).eval t

theorem grade_mul (t : ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    grade t (m*n) = grade t m+grade t n := by
  have h : occupationPolynomial (m*n) = occupationPolynomial m+occupationPolynomial n := by
    ext i
    exact DFunLike.congr_fun (Nat.factorization_mul hm hn) i
  rw [grade,h,eval_add]
  rfl

theorem grade_one (t : ℕ) : grade t 1 = 0 := by
  have h : occupationPolynomial 1 = 0 := by ext i; exact DFunLike.congr_fun Nat.factorization_one i
  rw [grade,h,eval_zero]

theorem grade_prime_power (t : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    grade t (p^k) = k*t^p := by
  have h : occupationPolynomial (p^k) = monomial p k :=
    congrArg (fun v : ℕ →₀ ℕ => Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff v)) hp.factorization_pow
  rw [grade,h,eval_monomial]

private theorem eventual_separation (m n : ℕ+) :
    ∀ᶠ t : ℕ in atTop, grade t m.val = grade t n.val → m = n := by
  classical
  by_cases he : m = n
  · exact Eventually.of_forall (fun _ _ => he)
  let f := Nat.castRingHom ℤ
  let Q := fun k : ℕ+ => (occupationPolynomial k.val).map f
  have hd : Q m ≠ Q n := by
    intro h
    have hp := Polynomial.map_injective f Nat.cast_injective h
    exact he (PNat.coe_injective (Nat.factorization_inj m.ne_zero n.ne_zero
      (congrArg (fun p : ℕ[X] => p.toFinsupp.coeff) hp)))
  let bad := {x : ℤ | (Q m).eval x = (Q n).eval x}
  have hbad : bad.Finite := by
    by_contra h
    exact hd (eq_of_infinite_eval_eq _ _ h)
  have hpre := hbad.preimage (f := fun t : ℕ => (t:ℤ)) Nat.cast_injective.injOn
  filter_upwards [hpre.eventually_cofinite_notMem.filter_mono atTop_le_cofinite] with t ht
  intro h
  exfalso
  apply ht
  change (Q m).eval (f t) = (Q n).eval (f t)
  rw [show (Q m).eval (f t) = f (grade t m.val) from eval_map_apply f t,
    show (Q n).eval (f t) = f (grade t n.val) from eval_map_apply f t]
  exact congrArg f h

/-- One positive integer grading distinguishes every element of any prescribed finite spectrum. -/
theorem exists_separating_grade (S : Finset ℕ+) :
    ∃ t : ℕ+, Set.InjOn (fun n : ℕ+ => grade t.val n.val) (S : Set ℕ+) := by
  have hs : ∀ᶠ t : ℕ in atTop, ∀ m ∈ S, ∀ n ∈ S, grade t m.val = grade t n.val → m = n :=
    S.eventually_all.mpr (fun m _ => S.eventually_all.mpr (fun n _ => eventual_separation m n))
  obtain ⟨t,ht,hS⟩ := ((eventually_ge_atTop (1:ℕ)).and hs).exists
  exact ⟨⟨t,ht⟩,fun m hm n hn => hS m hm n hn⟩

#print axioms grade_mul
#print axioms grade_one
#print axioms grade_prime_power
#print axioms exists_separating_grade

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
