import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleSelfDuality
import GaloisForLFunctions.RHTower.FieldOneSemilocalArchimedeanFaithfulness
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Full faithfulness of the semilocal Weyl tensor

Finite-zero contraction recovers the real Weyl factor.  Dually,
archimedean-zero contraction against the standard Gaussian recovers the
finite-adele Weyl factor, because every real phase and the Gaussian both take
value one at zero.

Combining archimedean faithfulness with finite-adele character self-duality
shows that the full semilocal Weyl multiplier representation on the algebraic
Schwartz--Bruhat tensor is faithful.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open scoped TensorProduct

/-- Evaluation at zero on the real Schwartz factor. -/
def fieldOneArchimedeanSchwartzEvalZero :
    FieldOneArchimedeanSchwartz →ₗ[ℂ] ℂ where
  toFun f := f 0
  map_add' f g := by simp
  map_smul' c f := by simp

/-- Contract the real factor of a semilocal algebraic tensor by evaluation at
zero. -/
def fieldOneSemilocalContractArchimedeanZero :
    FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
      FieldOneFiniteBruhatSchwartz :=
  (TensorProduct.lid ℂ FieldOneFiniteBruhatSchwartz).toLinearMap.comp
    (TensorProduct.map fieldOneArchimedeanSchwartzEvalZero LinearMap.id)

@[simp]
theorem fieldOneSemilocalContractArchimedeanZero_tmul
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    fieldOneSemilocalContractArchimedeanZero (f ⊗ₜ[ℂ] g) =
      f 0 • g := by
  simp [fieldOneSemilocalContractArchimedeanZero,
    fieldOneArchimedeanSchwartzEvalZero]

@[simp]
theorem fieldOneSemilocalArchimedeanWeylMultiplier_gaussian_zero
    (h : ℝ) :
    fieldOneSemilocalArchimedeanWeylMultiplier h
        GaloisForLFunctions.gaussianSchwartz 0 = 1 := by
  simp [fieldOneSemilocalArchimedeanWeylMultiplier,
    HTGeometry.FieldOneCore.fieldOneArchimedeanWeylMultiplier_apply,
    HTGeometry.FieldOneCore.fieldOneArchimedeanPhase,
    HTGeometry.scalarWeylCharacter,
    GaloisForLFunctions.gaussReal]

/-- Equality of semilocal Weyl operators forces equality of finite-adele
coordinates. -/
theorem fieldOneSemilocalBruhatWeylMultiplier_eq_imp_snd_eq
    {a b : ℝ × FieldOneFiniteAdele}
    (heq :
      fieldOneSemilocalBruhatWeylMultiplier a =
        fieldOneSemilocalBruhatWeylMultiplier b) :
    a.2 = b.2 := by
  apply fieldOneFiniteAdeleStandardWeylMultiplier_injective
  apply LinearMap.ext
  intro g
  have htensor :=
    congrArg
      (fun T :
          FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
            FieldOneSemilocalBruhatSchwartz =>
        T (GaloisForLFunctions.gaussianSchwartz ⊗ₜ[ℂ] g))
      heq
  have hcontract :=
    congrArg fieldOneSemilocalContractArchimedeanZero htensor
  simpa only [
    fieldOneSemilocalBruhatWeylMultiplier_tmul,
    fieldOneSemilocalContractArchimedeanZero_tmul,
    fieldOneSemilocalArchimedeanWeylMultiplier_gaussian_zero,
    one_smul] using hcontract

/-- The full semilocal Weyl action on the algebraic real--finite
Schwartz--Bruhat tensor is faithful. -/
theorem fieldOneSemilocalBruhatWeylMultiplier_injective :
    Function.Injective fieldOneSemilocalBruhatWeylMultiplier := by
  intro a b heq
  apply Prod.ext
  · exact
      fieldOneSemilocalBruhatWeylMultiplier_eq_imp_fst_eq heq
  · exact
      fieldOneSemilocalBruhatWeylMultiplier_eq_imp_snd_eq heq

end

end GaloisForLFunctions.RHTower
