import GaloisForLFunctions.HTGeometry.GradedMultiplication
import GaloisForLFunctions.HTGeometry.FamilyIdealXGraded

/-!
# Two elementary facts about graded pieces of ideals

```text
finrank_quotDegreePart_le_of_le   ** a larger subspace has a smaller quotient in each degree **
degreePart_sup_span_of_lt         ** adjoining a form of degree `d` changes nothing below `d` **
```

Both are needed to run a degeneration step by step.  The first turns a containment of ideals — the
chain ideal inside the initial ideal of the concave weight, say — into the inequality of Hilbert
functions the fibre bookkeeping consumes.  The second says the invariant carried by the iteration,
equality of Hilbert functions in *every* degree, survives adjoining a regular form on each side: the
degrees at and above `d` are handled by the Hilbert-function identity of a regular element, and the
degrees below `d` are untouched, because a homogeneous component of `l · g` below the degree of `l`
vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- **A larger subspace has a smaller quotient in each degree.** -/
theorem finrank_quotDegreePart_le_of_le {A B : Submodule K (MvPolynomial σ K)} (hAB : A ≤ B)
    (e : ℕ) [FiniteDimensional K (homogeneousSubmodule σ K e)] :
    finrank K (quotDegreePart B e) ≤ finrank K (quotDegreePart A e) := by
  have hle : degreePart A e ≤ degreePart B e := fun x hx => hAB hx
  exact LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hle)

/-- **Adjoining a form of degree `d` changes nothing below `d`.** -/
theorem degreePart_sup_span_of_lt {I : Ideal (MvPolynomial σ K)} (hI : IsHomogIdeal I)
    {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) {e : ℕ} (he : e < d) :
    degreePart ((I ⊔ Ideal.span {l}).restrictScalars K) e = degreePart (I.restrictScalars K) e := by
  refine le_antisymm ?_ (fun x hx => Ideal.mem_sup_left hx)
  intro x hx
  obtain ⟨a, ha, y, hy, hsum⟩ := Submodule.mem_sup.mp (hx : (x : MvPolynomial σ K) ∈ I ⊔ _)
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hxh : (x : MvPolynomial σ K).IsHomogeneous e := x.2
  have hcomp : MvPolynomial.homogeneousComponent e (a + g * l) = (x : MvPolynomial σ K) := by
    rw [hsum]
    exact MvPolynomial.homogeneousComponent_eq_self hxh
  rw [map_add, mul_comm g l, homogeneousComponent_mul_left_of_lt hl g he, add_zero] at hcomp
  show (x : MvPolynomial σ K) ∈ I
  rw [← hcomp]
  exact hI e a ha

end GaloisForLFunctions.HTGeometry
