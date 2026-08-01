import GaloisForLFunctions.HTGeometry.GammaFieldSumBoundary
import Mathlib.Order.Lex

/-!
# The dominant index always exists

The boundary datum of a Gamma-field monomial is the triple `(Γ-exponent, degree of the rational
factor, digamma exponent)`, and domination is the lexicographic order on it with the first component
reversed.  Packaging the datum as a key in `ℕᵒᵈ ×ₗ ℤ ×ₗ ℕ` — a linear order — turns domination into a
comparison of keys, so a finite family always has a dominant member.

This is the existential of eq. (5): the normalizing member of a finite tuple can always be chosen, so
the dominance hypothesis of the collapse costs no generality.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- The lexicographic key of a Gamma-field monomial: the `Γ`-exponent reversed, the degree of the
rational factor, and the digamma exponent. -/
noncomputable def gammaKey (j : ℕ) (p q : Polynomial ℂ) (D : ℕ) :
    Lex (ℕᵒᵈ × Lex (ℤ × ℕ)) :=
  toLex (OrderDual.toDual j, toLex (((p.natDegree : ℤ) - (q.natDegree : ℤ)), D))

theorem dominates_iff_key_le {ja jb : ℕ} {pa qa pb qb : Polynomial ℂ} {Da Db : ℕ}
    (hpa : pa ≠ 0) (hqa : qa ≠ 0) (hpb : pb ≠ 0) (hqb : qb ≠ 0) :
    GammaMonomialDominates ja pa qa Da jb pb qb Db
      ↔ gammaKey ja pa qa Da ≤ gammaKey jb pb qb Db := by
  have hd1 : (pa * qb).natDegree = pa.natDegree + qb.natDegree :=
    Polynomial.natDegree_mul hpa hqb
  have hd2 : (qa * pb).natDegree = qa.natDegree + pb.natDegree :=
    Polynomial.natDegree_mul hqa hpb
  rw [GammaMonomialDominates, gammaKey, gammaKey]
  simp only [Prod.Lex.le_iff, ofLex_toLex, OrderDual.toDual_lt_toDual, OrderDual.toDual_inj,
    hd1, hd2]
  constructor
  · rintro (hj | ⟨hjeq, hlt | ⟨heq, hD⟩⟩)
    · exact Or.inl hj
    · exact Or.inr ⟨hjeq, Or.inl (by omega)⟩
    · exact Or.inr ⟨hjeq, Or.inr ⟨by omega, hD⟩⟩
  · rintro (hj | ⟨hjeq, hlt | ⟨heq, hD⟩⟩)
    · exact Or.inl hj
    · exact Or.inr ⟨hjeq, Or.inl (by omega)⟩
    · exact Or.inr ⟨hjeq, Or.inr ⟨by omega, hD⟩⟩

/-- **Every finite family of Gamma-field monomials has a dominant index.**  This is the existential
in eq. (5): the normalizing member can always be chosen. -/
theorem exists_dominant_index {ι : Type*} [Fintype ι] [Nonempty ι] (j : ι → ℕ)
    (p q : ι → Polynomial ℂ) (D : ι → ℕ) (hp : ∀ i, p i ≠ 0) (hq : ∀ i, q i ≠ 0) :
    ∃ β : ι, ∀ α : ι,
      GammaMonomialDominates (j α) (p α) (q α) (D α) (j β) (p β) (q β) (D β) := by
  classical
  obtain ⟨β, -, hβ⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun i => gammaKey (j i) (p i) (q i) (D i)) ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  refine ⟨β, fun α => ?_⟩
  exact (dominates_iff_key_le (hp α) (hq α) (hp β) (hq β)).mpr (hβ α (Finset.mem_univ α))

/-- **The dominance hypothesis of the collapse is always satisfiable.**  Any doubly indexed family of
Gamma-field monomials — the monomials of all the coefficients of a finite relation — has one member
dominating them all. -/
theorem exists_dominant_monomial_family {N k : ℕ} [NeZero N] [NeZero k] (j : Fin N → Fin k → ℕ)
    (p q : Fin N → Fin k → Polynomial ℂ) (D : Fin N → Fin k → ℕ)
    (hp : ∀ a i, p a i ≠ 0) (hq : ∀ a i, q a i ≠ 0) :
    ∃ (b : Fin N × Fin k), ∀ (a : Fin N) (i : Fin k),
      GammaMonomialDominates (j a i) (p a i) (q a i) (D a i)
        (j b.1 b.2) (p b.1 b.2) (q b.1 b.2) (D b.1 b.2) := by
  classical
  haveI : Nonempty (Fin N × Fin k) := ⟨⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩,
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩⟩⟩
  obtain ⟨b, hb⟩ := exists_dominant_index (ι := Fin N × Fin k)
    (fun c => j c.1 c.2) (fun c => p c.1 c.2) (fun c => q c.1 c.2) (fun c => D c.1 c.2)
    (fun c => hp c.1 c.2) (fun c => hq c.1 c.2)
  exact ⟨b, fun a i => hb (a, i)⟩

end GaloisForLFunctions
