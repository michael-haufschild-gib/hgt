import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Algebra.Hom

/-!
# The projective charge is a well-defined invariant

The charge `k` of the diagonalized clock action `ρ_λ(q) = λ^k·q` is uniquely determined: over an
infinite field, `λ^k = λ^m` for every nonzero `λ` forces `k = m` (the monomials `X^k`, `X^m` agree on
an infinite set, hence are equal).  So a given diagonalizing generator carries a single, canonical
projective charge — the absolute cocharacter.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Over an infinite field, `λ^k = λ^m` for all nonzero `λ` forces `k = m`. -/
theorem charge_unique {C : Type*} [Field C] [Infinite C] {k m : ℕ}
    (h : ∀ lam : C, lam ≠ 0 → lam ^ k = lam ^ m) : k = m := by
  have hinf : {x : C | x ≠ 0}.Infinite := by
    have h0 := (Set.finite_singleton (0 : C)).infinite_compl
    rwa [Set.compl_singleton_eq] at h0
  have hdiff : (Polynomial.X ^ k - Polynomial.X ^ m : Polynomial C) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact hinf.mono fun x hx => by
      have hx0 : x ≠ 0 := hx
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [h x hx0, sub_self]
  have heq : (Polynomial.X ^ k : Polynomial C) = Polynomial.X ^ m := sub_eq_zero.mp hdiff
  have hnd := congrArg Polynomial.natDegree heq
  rwa [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at hnd

/-- **Charge invariance.**  A diagonalizing generator `q` of a clock action determines a unique
charge: if `ρ_λ(q) = λ^k·q` and `ρ_λ(q) = λ^m·q` (both for nonzero `λ`), then `k = m`. -/
theorem charge_unique_of_scaling {C E : Type*} [Field C] [Infinite C] [Field E] [Algebra C E]
    (ρ : C → (E →ₐ[C] E)) {q : E} (hq : q ≠ 0) {k m : ℕ}
    (hk : ∀ lam : C, lam ≠ 0 → ρ lam q = algebraMap C E (lam ^ k) * q)
    (hm : ∀ lam : C, lam ≠ 0 → ρ lam q = algebraMap C E (lam ^ m) * q) :
    k = m := by
  apply charge_unique (C := C)
  intro lam hlam
  have hqeq : algebraMap C E (lam ^ k) * q = algebraMap C E (lam ^ m) * q :=
    (hk lam hlam).symm.trans (hm lam hlam)
  have h2 : algebraMap C E (lam ^ k) = algebraMap C E (lam ^ m) := mul_right_cancel₀ hq hqeq
  have h3 : algebraMap C E (lam ^ k - lam ^ m) = 0 := by rw [map_sub, h2, sub_self]
  exact sub_eq_zero.mp (by rwa [map_eq_zero] at h3)

end GaloisForLFunctions.HTGeometry
