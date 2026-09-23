import Mathlib.Data.Finset.Prod

/-!
# Additive energy behind Maynard's `R*`

Maynard's fourth-moment large-values count `R*` is exactly the additive energy of the integer cells
where a Dirichlet polynomial is large.  For a finite set `S`, this is the number of quadruples
`m₁ + m₂ = m₃ + m₄` in `S⁴`.

The universal range is sharp:

`|S|² ≤ E⁺(S) ≤ |S|³`.

The lower bound is the diagonal family, while the upper bound records that the fourth entry is
uniquely determined by the first three.  Consequently any useful `R*` saving over `R³` must use
arithmetic structure of the large-value set; it cannot follow from its cardinality alone.
-/

namespace RHTower.Sieve

open Finset

/-- Ordered additive quadruples in a finite set of integer frequency cells. -/
def maynardAdditiveQuadruples (S : Finset ℤ) : Finset (ℤ × (ℤ × (ℤ × ℤ))) :=
  (S.product (S.product (S.product S))).filter fun p =>
    p.1 + p.2.1 = p.2.2.1 + p.2.2.2

/-- Maynard's `R*`: additive energy of the large-value cells. -/
def maynardRStar (S : Finset ℤ) : ℕ :=
  (maynardAdditiveQuadruples S).card

/-- Every ordered pair supplies one diagonal additive quadruple. -/
theorem card_sq_le_maynardRStar (S : Finset ℤ) :
    S.card ^ (2 : ℕ) ≤ maynardRStar S := by
  classical
  let diagonal : ℤ × ℤ → ℤ × (ℤ × (ℤ × ℤ)) := fun p =>
    (p.1, (p.2, (p.1, p.2)))
  have hcard := Finset.card_le_card_of_injOn diagonal (s := S.product S)
    (t := maynardAdditiveQuadruples S) (by
      intro p hp
      have hp' : p.1 ∈ S ∧ p.2 ∈ S := by simpa using hp
      simp [maynardAdditiveQuadruples, diagonal, hp'.1, hp'.2]) (by
      intro p hp q hq heq
      apply Prod.ext
      · exact congrArg (fun x : ℤ × (ℤ × (ℤ × ℤ)) => x.1) heq
      · exact congrArg (fun x : ℤ × (ℤ × (ℤ × ℤ)) => x.2.1) heq)
  simpa [maynardRStar, pow_two] using hcard

/-- The fourth entry of an additive quadruple is uniquely determined by the first three. -/
theorem maynardRStar_le_card_cube (S : Finset ℤ) :
    maynardRStar S ≤ S.card ^ (3 : ℕ) := by
  classical
  let forgetLast : ℤ × (ℤ × (ℤ × ℤ)) → ℤ × (ℤ × ℤ) := fun p =>
    (p.1, (p.2.1, p.2.2.1))
  have hcard := Finset.card_le_card_of_injOn forgetLast
    (s := maynardAdditiveQuadruples S) (t := S.product (S.product S)) (by
      intro p hp
      have hp' : p ∈ maynardAdditiveQuadruples S := by exact hp
      have hprod := (Finset.mem_filter.mp hp').1
      have hprod' : p.1 ∈ S ∧ p.2.1 ∈ S ∧ p.2.2.1 ∈ S ∧ p.2.2.2 ∈ S := by
        simpa using hprod
      simp [forgetLast, hprod'.1, hprod'.2.1, hprod'.2.2.1]) (by
      intro p hp q hq heq
      have hpadd : p.1 + p.2.1 = p.2.2.1 + p.2.2.2 := by
        simpa [maynardAdditiveQuadruples] using
          (Finset.mem_filter.mp (show p ∈ maynardAdditiveQuadruples S from hp)).2
      have hqadd : q.1 + q.2.1 = q.2.2.1 + q.2.2.2 := by
        simpa [maynardAdditiveQuadruples] using
          (Finset.mem_filter.mp (show q ∈ maynardAdditiveQuadruples S from hq)).2
      have h1 : p.1 = q.1 :=
        congrArg (fun x : ℤ × (ℤ × ℤ) => x.1) heq
      have h23 : (p.2.1, p.2.2.1) = (q.2.1, q.2.2.1) :=
        congrArg (fun x : ℤ × (ℤ × ℤ) => x.2) heq
      have h2 : p.2.1 = q.2.1 :=
        congrArg (fun x : ℤ × ℤ => x.1) h23
      have h3 : p.2.2.1 = q.2.2.1 :=
        congrArg (fun x : ℤ × ℤ => x.2) h23
      have h4 : p.2.2.2 = q.2.2.2 := by omega
      exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)))
  simpa [maynardRStar, pow_succ, Nat.mul_assoc] using hcard

/-- Exact universal range for the fourth-moment cell count. -/
theorem maynardRStar_sandwich (S : Finset ℤ) :
    S.card ^ (2 : ℕ) ≤ maynardRStar S ∧ maynardRStar S ≤ S.card ^ (3 : ℕ) :=
  ⟨card_sq_le_maynardRStar S, maynardRStar_le_card_cube S⟩

end RHTower.Sieve
