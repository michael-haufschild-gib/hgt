import GaloisForLFunctions.HTGeometry.PaperGenericSL2Factoriality
import GaloisForLFunctions.HTGeometry.PaperDeterminantUnitRigidity
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.PicardUFD

/-!
# Line bundles and scalar units on the native generic SL₂ torsor

The source's Picard theorem applies to the existing generic torsor algebra,
whose unique factorization was transported from the determinant presentation.
Its invertible modules admit actual linear trivializations. The same
presentation identifies all invertible regular functions as scalar units.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

/-- Every invertible module on the native generic SL₂ torsor has a linear trivialization. -/
theorem paperGenericSL2_invertibleModule_trivial
    (M : Type*) [AddCommGroup M] [Module (genericSL ℂ 2) M]
    [Module.Invertible (genericSL ℂ 2) M] : Nonempty (M ≃ₗ[genericSL ℂ 2] genericSL ℂ 2) :=
  PicardSupport.invertibleModule_trivial_of_gcd (genericSL ℂ 2) M

/-- The Picard group of the actual native generic SL₂ algebra is trivial. -/
theorem paperGenericSL2_picard_eq_one (L : CommRing.Pic (genericSL ℂ 2)) : L = 1 :=
  Subsingleton.elim _ _

/-- Every invertible regular function on the native torsor is a scalar unit. -/
theorem paperGenericSL2_unit_eq_scalar (u : (genericSL ℂ 2)ˣ) :
    ∃ c : ℂˣ, (u : genericSL ℂ 2) = algebraMap ℂ (genericSL ℂ 2) (c : ℂ) := by
  let v : (Obstruction.C ℂ)ˣ :=
    Units.map paperGenericSL2PolynomialEquiv.symm.toMonoidHom
      (Units.map Polynomial.C.toMonoidHom u)
  obtain ⟨c, hc⟩ := paperDeterminantUnit_eq_scalar ℂ v
  refine ⟨c, ?_⟩
  have he := congrArg paperGenericSL2PolynomialEquiv hc
  change paperGenericSL2PolynomialEquiv
      (paperGenericSL2PolynomialEquiv.symm (Polynomial.C (u : genericSL ℂ 2))) =
    paperGenericSL2PolynomialEquiv (algebraMap ℂ (Obstruction.C ℂ) (c : ℂ)) at he
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes] at he
  apply Polynomial.C_injective
  exact he

/-- Scalar evaluation obtained from the determinant basepoint. -/
def paperGenericSL2ScalarEvaluation : genericSL ℂ 2 →ₐ[ℂ] ℂ :=
  (Obstruction.determinantBasepoint ℂ).comp paperSL2ToDeterminant

/-- The full native unit group is precisely the coefficient-field unit group. -/
def paperGenericSL2UnitsEquiv : (genericSL ℂ 2)ˣ ≃* ℂˣ where
  toFun := Units.map paperGenericSL2ScalarEvaluation.toMonoidHom
  invFun := Units.map (algebraMap ℂ (genericSL ℂ 2)).toMonoidHom
  left_inv u := by
    apply Units.ext
    change algebraMap ℂ (genericSL ℂ 2) (paperGenericSL2ScalarEvaluation (u : genericSL ℂ 2)) = u
    obtain ⟨c, hc⟩ := paperGenericSL2_unit_eq_scalar u
    rw [hc, AlgHom.commutes]
    rfl
  right_inv u := by
    apply Units.ext
    exact paperGenericSL2ScalarEvaluation.commutes (u : ℂ)
  map_mul' u v := map_mul _ _ _

/-- Arbitrary polynomial parameters introduce no new invertible functions on the native torsor. -/
def paperGenericSL2PolynomialUnitsEquiv (σ : Type*) :
    (MvPolynomial σ (genericSL ℂ 2))ˣ ≃* ℂˣ :=
  (polynomialUnitsEquiv (fun _ : σ => (0 : genericSL ℂ 2))).trans paperGenericSL2UnitsEquiv

end

end GaloisForLFunctions.HTGeometry
