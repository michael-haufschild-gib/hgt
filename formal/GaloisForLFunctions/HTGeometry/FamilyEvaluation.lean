import GaloisForLFunctions.HTGeometry.FamilyDegreeFinite

/-!
# Evaluating the family at a point of the base line

```text
isHomogeneous_eval_of_isXHomog   evaluating keeps the x-degree
polyMvScalarTower                the two scalar actions of the base field agree
evalDegreeHom                    ** evaluation, as a map of graded pieces **
```

Setting the extra variable to a constant sends a polynomial whose coefficients are all homogeneous of
one degree to a polynomial homogeneous of that degree, and does so linearly over the base field.  This
is the map whose kernel is the ideal of the point, and therefore the map that realises a fibre of the
family in a fixed degree.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {K : Type u} [Field K]

theorem isHomogeneous_eval_of_isXHomog {N e : ℕ} {F : Polynomial (MvPolynomial (Fin N) K)}
    (hF : IsXHomog e F) (lam : K) :
    (Polynomial.eval (MvPolynomial.C lam) F).IsHomogeneous e := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
  intro j _
  have h1 : ((MvPolynomial.C lam : MvPolynomial (Fin N) K) ^ j).IsHomogeneous 0 := by
    have : (MvPolynomial.C lam : MvPolynomial (Fin N) K).IsHomogeneous 0 :=
      MvPolynomial.isHomogeneous_C _ _
    simpa using this.pow j
  have := (hF j).mul h1
  rwa [add_zero] at this

instance polyMvScalarTower {σ : Type*} :
    IsScalarTower K (Polynomial K) (Polynomial (MvPolynomial σ K)) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  show (Polynomial.C (MvPolynomial.C c) : Polynomial (MvPolynomial σ K))
    = (Polynomial.C c : Polynomial K).map (MvPolynomial.C : K →+* MvPolynomial σ K)
  rw [Polynomial.map_C]

/-- Evaluating the extra variable at a point, on a graded piece of the family. -/
noncomputable def evalDegreeHom (K : Type u) [Field K] (N e : ℕ) (lam : K) :
    (Submodule.restrictScalars K (xDegreeSubmodule K (Fin N) e))
      →ₗ[K] (homogeneousSubmodule (Fin N) K e) where
  toFun F := ⟨Polynomial.eval (MvPolynomial.C lam) (F : Polynomial (MvPolynomial (Fin N) K)),
    isHomogeneous_eval_of_isXHomog F.2 lam⟩
  map_add' F G := by
    refine Subtype.ext ?_
    show Polynomial.eval (MvPolynomial.C lam)
      ((F : Polynomial (MvPolynomial (Fin N) K)) + (G : Polynomial (MvPolynomial (Fin N) K)))
      = _
    rw [Polynomial.eval_add]
    rfl
  map_smul' c F := by
    refine Subtype.ext ?_
    have hsm : ((c • F : Submodule.restrictScalars K (xDegreeSubmodule K (Fin N) e)) :
        Polynomial (MvPolynomial (Fin N) K))
        = (Polynomial.C (MvPolynomial.C c)) * (F : Polynomial (MvPolynomial (Fin N) K)) := by
      show c • (F : Polynomial (MvPolynomial (Fin N) K)) = _
      rw [Algebra.smul_def]
      rfl
    show Polynomial.eval (MvPolynomial.C lam)
      ((c • F : Submodule.restrictScalars K (xDegreeSubmodule K (Fin N) e)) :
        Polynomial (MvPolynomial (Fin N) K)) = _
    rw [hsm, Polynomial.eval_mul, Polynomial.eval_C, Submodule.coe_smul,
      MvPolynomial.smul_eq_C_mul]
    rfl

end GaloisForLFunctions.HTGeometry
