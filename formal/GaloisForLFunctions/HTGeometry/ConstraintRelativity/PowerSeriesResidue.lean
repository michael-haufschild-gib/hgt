import Mathlib
import GaloisForLFunctions.HTGeometry.PowerSeriesCriticalDeformation

/-!
# Formal power-series residue field

Minimal shared infrastructure identifying the residue ring of `k[[X]]` at `(X)` with `k`.
-/

namespace HTGeometry.ConstraintRelativity

noncomputable section

variable {k : Type*} [Field k]

/-- The constant coefficient as a map of `k`-algebras. -/
noncomputable def constantCoeffAlgHom : PowerSeries k →ₐ[k] k :=
  { PowerSeries.constantCoeff with commutes' := fun r => by simp }

@[simp] theorem constantCoeffAlgHom_apply (f : PowerSeries k) :
    constantCoeffAlgHom f = PowerSeries.constantCoeff f := rfl

theorem constantCoeffAlgHom_surjective :
    Function.Surjective (constantCoeffAlgHom (k := k)) :=
  fun r => ⟨PowerSeries.C r, by simp⟩

theorem ker_constantCoeffAlgHom :
    RingHom.ker (constantCoeffAlgHom (k := k)) =
      Ideal.span ({PowerSeries.X} : Set (PowerSeries k)) :=
  (GaloisForLFunctions.HTGeometry.powerSeriesDeformIdeal_eq_ker_constantCoeff k).symm

/-- The residue ring of the formal power series ring is the coefficient field. -/
noncomputable def powerSeriesResidueEquiv :
    (PowerSeries k ⧸ Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k (ker_constantCoeffAlgHom (k := k)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective constantCoeffAlgHom_surjective)

@[simp] theorem powerSeriesResidueEquiv_mk (f : PowerSeries k) :
    powerSeriesResidueEquiv (Ideal.Quotient.mk _ f) = PowerSeries.constantCoeff f := rfl

end

end HTGeometry.ConstraintRelativity
