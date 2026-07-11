import Mathlib.Data.Finsupp.Basic

/-!
# Discrete residues and the shift-coboundary obstruction

The signed archimedean Gamma orbit-charge card (§3, eq. 13) and the double-sine defect cards obtain
their hypertranscendence obstruction from a purely algebraic fact about rational shift summability:
*for every rational function `u`, each fixed-order principal-part coefficient of `u(s+H) − u(s)` has
zero sum over every `HZ`-orbit — the sum is finite and telescopes.*

Modeling the order-`j` principal-part coefficients of a meromorphic function along one orbit as a
finitely supported function `P : α →₀ M` (pole location `↦` coefficient), the **discrete residue**
over the orbit is `∑ P`, and the shift by the period is a bijection `e : α ≃ α` of pole locations.
A shift-coboundary — the principal-part datum of `g(s+H) − g(s)` — is `equivMapDomain e Q − Q`, and
its discrete residue vanishes because the finite sum is shift-invariant.  This generalizes the
integer-orbit degree computation of `GaloisForLFunctions.OrbitBalance` to arbitrary orbits and
coefficient groups.
-/

namespace GaloisForLFunctions

variable {α β M : Type*}

/-- The discrete residue over an orbit: the sum of the (finitely many nonzero) principal-part
coefficients. -/
def discreteResidue [AddCommMonoid M] (P : α →₀ M) : M := P.sum fun _ m => m

@[simp]
theorem discreteResidue_zero [AddCommMonoid M] : discreteResidue (0 : α →₀ M) = 0 := by
  simp [discreteResidue]

/-- The discrete residue is invariant under any bijective reindexing of pole locations — in
particular under the period shift. -/
theorem discreteResidue_equivMapDomain [AddCommMonoid M] (e : α ≃ β) (P : α →₀ M) :
    discreteResidue (Finsupp.equivMapDomain e P) = discreteResidue P := by
  rw [discreteResidue, discreteResidue, Finsupp.sum_equivMapDomain]

/-- The discrete residue is additive on differences. -/
theorem discreteResidue_sub [AddCommGroup M] (P Q : α →₀ M) :
    discreteResidue (P - Q) = discreteResidue P - discreteResidue Q :=
  Finsupp.sum_sub_index fun _ _ _ => rfl

/-- **Shift-coboundary obstruction.**  The discrete residue of a shift-coboundary
`equivMapDomain e Q − Q` vanishes over every orbit: the finite principal-part sum telescopes.  This
is the exact rational-summability obstruction driving the DA/HT dichotomy (§3, eq. 13). -/
theorem discreteResidue_shiftCoboundary_eq_zero [AddCommGroup M] (e : α ≃ α) (Q : α →₀ M) :
    discreteResidue (Finsupp.equivMapDomain e Q - Q) = 0 := by
  rw [discreteResidue_sub, discreteResidue_equivMapDomain, sub_self]

/-- Contrapositive form: a principal-part datum with nonzero discrete residue over some orbit is not
a shift-coboundary — hence not rationally shift-summable.  This is the step that forces
hypertranscendence when some orbit charge `M_c ≠ 0`. -/
theorem not_shiftCoboundary_of_discreteResidue_ne_zero [AddCommGroup M] (e : α ≃ α) (P : α →₀ M)
    (hP : discreteResidue P ≠ 0) : ∀ Q : α →₀ M, P ≠ Finsupp.equivMapDomain e Q - Q := by
  intro Q hQ
  exact hP (hQ ▸ discreteResidue_shiftCoboundary_eq_zero e Q)

end GaloisForLFunctions
