import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Group-like elements of a monoid algebra over a domain

A group-like element of `R[G]` is exactly one basis monoid element.  The proof pairs the
comultiplication against two coefficient functionals: the group-like equation forces the
coefficients to be orthogonal idempotents of `R`, and over a domain only one of them survives.
-/

open Coalgebra TensorProduct

namespace GaloisForLFunctions.HTGeometry

section Coefficients

variable {R : Type*} [CommRing R] {G : Type*}

/-- The coefficient of a monoid-algebra element at a monoid element, as a linear functional. -/
noncomputable def maCoeff (g : G) : MonoidAlgebra R G →ₗ[R] R :=
  Finsupp.lapply g ∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem maCoeff_apply (g : G) (x : MonoidAlgebra R G) :
    maCoeff (R := R) g x = x.coeff g := rfl

/-- The pairing of two coefficient functionals on the tensor square. -/
noncomputable def coeffPair (g h : G) :
    (MonoidAlgebra R G ⊗[R] MonoidAlgebra R G) →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap ∘ₗ
    TensorProduct.map (maCoeff (R := R) g) (maCoeff (R := R) h)

@[simp] theorem coeffPair_tmul (g h : G) (x y : MonoidAlgebra R G) :
    coeffPair (R := R) g h (x ⊗ₜ[R] y) = x.coeff g * y.coeff h := by
  simp [coeffPair, smul_eq_mul]

theorem comul_single_eq (k : G) (a : R) :
    comul (R := R) (MonoidAlgebra.single k a)
      = (MonoidAlgebra.single k (1 : R)) ⊗ₜ[R] (MonoidAlgebra.single k a) := by
  rw [MonoidAlgebra.comul_single]
  simp

/-- Pairing the comultiplication against two coefficients isolates the diagonal. -/
theorem coeffPair_comul [DecidableEq G] (x : MonoidAlgebra R G) (g h : G) :
    coeffPair (R := R) g h (comul (R := R) x) = if g = h then x.coeff g else 0 := by
  classical
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
  rw [Finsupp.sum, map_sum, map_sum]
  have hterm : ∀ k ∈ x.coeff.support,
      coeffPair (R := R) g h (comul (R := R) (MonoidAlgebra.single k (x.coeff k)))
        = if k = g then (if g = h then x.coeff g else 0) else 0 := by
    intro k _
    rw [comul_single_eq, coeffPair_tmul, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finsupp.single_apply]
    by_cases hkg : k = g
    · subst hkg
      by_cases hkh : k = h
      · subst hkh
        simp
      · simp [hkh]
    · simp [hkg]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  by_cases hmem : g ∈ x.coeff.support
  · rw [if_pos hmem]
  · rw [if_neg hmem]
    have hzero : x.coeff g = 0 := Finsupp.notMem_support_iff.1 hmem
    by_cases hgh : g = h
    · rw [if_pos hgh, hzero]
    · rw [if_neg hgh]

end Coefficients

section GroupLike

variable {R : Type*} [CommRing R] [IsDomain R] {G : Type*}

/-- **Group-like classification.**  Over a domain the group-like elements of a monoid algebra are
exactly the basis monoid elements: no proper linear combination is group-like. -/
theorem isGroupLikeElem_iff_exists_single {x : MonoidAlgebra R G} :
    IsGroupLikeElem R x ↔ ∃ g : G, x = MonoidAlgebra.single g 1 := by
  classical
  constructor
  · intro hx
    have hpair : ∀ g h : G, (if g = h then x.coeff g else 0) = x.coeff g * x.coeff h := by
      intro g h
      rw [← coeffPair_comul x g h, hx.comul_eq_tmul_self, coeffPair_tmul]
    have hne : x ≠ 0 := hx.ne_zero
    have hcoeffne : x.coeff ≠ 0 := by
      intro hc
      exact hne (MonoidAlgebra.coeff_injective (by rw [hc]; simp))
    obtain ⟨g, hg⟩ : ∃ g : G, x.coeff g ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hcoeffne (Finsupp.ext fun g => by simpa using hcon g)
    have hgg : x.coeff g = x.coeff g * x.coeff g := by simpa using hpair g g
    have hg1 : x.coeff g = 1 := by
      have h0 : x.coeff g * (x.coeff g - 1) = 0 := by
        rw [mul_sub, mul_one, ← hgg, sub_self]
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hg
      · exact sub_eq_zero.1 h
    refine ⟨g, MonoidAlgebra.coeff_injective ?_⟩
    rw [MonoidAlgebra.coeff_single]
    refine Finsupp.ext fun h => ?_
    rw [Finsupp.single_apply]
    by_cases hgh : g = h
    · subst hgh
      simpa using hg1
    · have hph := hpair g h
      rw [if_neg hgh, hg1, one_mul] at hph
      rw [if_neg hgh]
      exact hph.symm
  · rintro ⟨g, rfl⟩
    refine ⟨?_, comul_single_eq g 1⟩
    rw [MonoidAlgebra.counit_single]
    simp

end GroupLike

end GaloisForLFunctions.HTGeometry
