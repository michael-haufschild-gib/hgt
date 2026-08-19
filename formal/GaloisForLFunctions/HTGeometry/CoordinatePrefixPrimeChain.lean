import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coordinate-prefix primes of a polynomial ring

Substituting the first `j` coordinates of a point `c` into a polynomial gives a `k`-algebra
endomorphism of `MvPolynomial (Fin N) k` whose kernel is the ideal of the coordinate subspace
through `c` in the first `j` directions.  These kernels form a strictly increasing chain of
`N + 1` primes, and none of them contains a polynomial that is nonzero at `c`.

This is the elementary source of maximal-length prime chains avoiding a hypersurface, used to
bound Krull dimensions from below.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {k : Type*} [Field k] {N : ℕ}

/-- Substitute the first `j` coordinates of a point `c` into a polynomial. -/
noncomputable def coordinatePrefixSubst (c : Fin N → k) (j : ℕ) :
    MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin N) k :=
  aeval fun i => if (i : ℕ) < j then C (c i) else X i

theorem coordinatePrefixSubst_X (c : Fin N → k) (j : ℕ) (i : Fin N) :
    coordinatePrefixSubst c j (X i) = if (i : ℕ) < j then C (c i) else X i := by
  simp [coordinatePrefixSubst]

theorem coordinatePrefixSubst_C (c : Fin N → k) (j : ℕ) (r : k) :
    coordinatePrefixSubst c j (C r) = C r := by
  simp [coordinatePrefixSubst]

theorem coordinatePrefixSubst_comp (c : Fin N → k) {j l : ℕ} (hjl : j ≤ l) :
    (coordinatePrefixSubst c l).comp (coordinatePrefixSubst c j) = coordinatePrefixSubst c l := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, coordinatePrefixSubst_X, coordinatePrefixSubst_X]
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (lt_of_lt_of_le h hjl), coordinatePrefixSubst_C]
  · rw [if_neg h, coordinatePrefixSubst_X]

/-- The ideal of the coordinate subspace cut out by the first `j` coordinates of `c`. -/
noncomputable def coordinatePrefixIdeal (c : Fin N → k) (j : ℕ) : Ideal (MvPolynomial (Fin N) k) :=
  RingHom.ker (coordinatePrefixSubst c j).toRingHom

instance coordinatePrefixIdeal_isPrime (c : Fin N → k) (j : ℕ) : (coordinatePrefixIdeal c j).IsPrime :=
  RingHom.ker_isPrime _

theorem mem_coordinatePrefixIdeal_iff (c : Fin N → k) (j : ℕ) (f : MvPolynomial (Fin N) k) :
    f ∈ coordinatePrefixIdeal c j ↔ coordinatePrefixSubst c j f = 0 := Iff.rfl

theorem coordinatePrefixIdeal_mono (c : Fin N → k) {j l : ℕ} (hjl : j ≤ l) :
    coordinatePrefixIdeal c j ≤ coordinatePrefixIdeal c l := by
  intro f hf
  rw [mem_coordinatePrefixIdeal_iff] at hf ⊢
  have := congrArg (fun g : MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin N) k => g f)
    (coordinatePrefixSubst_comp c hjl)
  simpa [hf] using this.symm

theorem coordinatePrefixIdeal_lt (c : Fin N → k) {j : ℕ} (hj : j < N) :
    coordinatePrefixIdeal c j < coordinatePrefixIdeal c (j + 1) := by
  refine lt_of_le_of_ne (coordinatePrefixIdeal_mono c (Nat.le_succ j)) fun hcon => ?_
  set i : Fin N := ⟨j, hj⟩ with hi
  have hmem : (X i - C (c i) : MvPolynomial (Fin N) k) ∈ coordinatePrefixIdeal c (j + 1) := by
    rw [mem_coordinatePrefixIdeal_iff, map_sub, coordinatePrefixSubst_X, coordinatePrefixSubst_C,
      if_pos (by simp [hi])]
    simp
  rw [← hcon, mem_coordinatePrefixIdeal_iff, map_sub, coordinatePrefixSubst_X, coordinatePrefixSubst_C,
    if_neg (by simp [hi])] at hmem
  have : (X i : MvPolynomial (Fin N) k) = C (c i) := by
    have := sub_eq_zero.mp hmem
    exact this
  have hco := congrArg (fun p : MvPolynomial (Fin N) k => MvPolynomial.coeff (Finsupp.single i 1) p) this
  simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, eq_comm, Finsupp.single_eq_zero] at hco

theorem coordinatePrefixSubst_eq_C_eval (c : Fin N → k) (f : MvPolynomial (Fin N) k) :
    coordinatePrefixSubst c N f = C (MvPolynomial.eval c f) := by
  rw [coordinatePrefixSubst]
  rw [show (fun i : Fin N => if (i : ℕ) < N then C (c i) else X i) = fun i => C (c i) from
    funext fun i => if_pos i.isLt]
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem notMem_coordinatePrefixIdeal_of_eval_ne_zero (c : Fin N → k) {f : MvPolynomial (Fin N) k}
    (hf : MvPolynomial.eval c f ≠ 0) {j : ℕ} (hj : j ≤ N) : f ∉ coordinatePrefixIdeal c j := by
  intro hmem
  have h := coordinatePrefixIdeal_mono c hj hmem
  rw [mem_coordinatePrefixIdeal_iff, coordinatePrefixSubst_eq_C_eval] at h
  exact hf (by simpa using congrArg (MvPolynomial.coeff 0) h)

end GaloisForLFunctions.HTGeometry
