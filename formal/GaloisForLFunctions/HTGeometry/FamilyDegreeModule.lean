import GaloisForLFunctions.HTGeometry.FamilyXGrading

/-!
# The graded pieces of the family are modules over the base line

```text
polyMvAlgebra       the base line acts on the family by mapping coefficients
isXHomog_smul       that action preserves the x-degree
xDegreeSubmodule    ** so each x-degree is a module over the base line **
```

Scaling by a polynomial in the extra variable multiplies coefficientwise by constants, which does
not change the `x`-degree; this is what makes the degeneration a family of graded pieces over the
base line rather than merely a family of rings.

Mathlib has no `Algebra (Polynomial K) (Polynomial A)` instance for a `K`-algebra `A`; the one
declared here is the canonical coefficient map, and is stated only for the polynomial-ring case, so
it cannot collide with the identity algebra on `Polynomial K`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- The base line acts on the family by mapping coefficients. -/
noncomputable instance polyMvAlgebra :
    Algebra (Polynomial K) (Polynomial (MvPolynomial σ K)) :=
  (Polynomial.mapRingHom (MvPolynomial.C : K →+* MvPolynomial σ K)).toAlgebra

theorem polyMvAlgebra_smul (c : Polynomial K) (F : Polynomial (MvPolynomial σ K)) :
    c • F = (c.map (MvPolynomial.C : K →+* MvPolynomial σ K)) * F := rfl

theorem isXHomog_smul {e : ℕ} (c : Polynomial K) {F : Polynomial (MvPolynomial σ K)}
    (hF : IsXHomog e F) : IsXHomog e (c • F) := by
  classical
  intro j
  rw [polyMvAlgebra_smul, Polynomial.coeff_mul]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
  rintro ⟨a, b⟩ _
  have hc : (c.map (MvPolynomial.C : K →+* MvPolynomial σ K)).coeff a
      = MvPolynomial.C (c.coeff a) := by
    rw [Polynomial.coeff_map]
  rw [hc]
  have h0 : (MvPolynomial.C (c.coeff a) : MvPolynomial σ K).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C _ _
  have := h0.mul (hF b)
  rwa [zero_add] at this

/-- The polynomials in the extra variable whose coefficients are all `x`-homogeneous of one degree,
as a module over the base line. -/
noncomputable def xDegreeSubmodule (K : Type u) [Field K] (σ : Type*) (e : ℕ) :
    Submodule (Polynomial K) (Polynomial (MvPolynomial σ K)) where
  carrier := {F | IsXHomog e F}
  add_mem' := by
    intro F G hF hG j
    rw [Polynomial.coeff_add]
    exact (hF j).add (hG j)
  zero_mem' := by
    intro j
    rw [Polynomial.coeff_zero]
    exact MvPolynomial.isHomogeneous_zero _ _ _
  smul_mem' := fun c _ hF => isXHomog_smul c hF

theorem mem_xDegreeSubmodule {e : ℕ} {F : Polynomial (MvPolynomial σ K)} :
    F ∈ xDegreeSubmodule K σ e ↔ IsXHomog e F := Iff.rfl

end GaloisForLFunctions.HTGeometry
