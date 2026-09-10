import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionFreeModule
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Connection symmetries as polynomial-module endomorphisms

A real-linear endomorphism commutes with the connection precisely when it is linear
over its polynomial operator ring. The correspondence preserves addition, composition,
and real scalars, giving an actual algebra equivalence with no assumed commutation law.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The full algebra of real-linear endomorphisms commuting with a polynomial connection. -/
def gomesPolynomialConnectionCommutantAlgebra (A : ℝ[X]) :
    Subalgebra ℝ (Module.End ℝ ℝ[X]) :=
  Subalgebra.centralizer ℝ {gomesPolynomialFirstOrderLinearMap A}

/-- Elements of the full connection symmetry algebra. -/
abbrev GomesPolynomialConnectionCommutant (A : ℝ[X]) :=
  ↥(gomesPolynomialConnectionCommutantAlgebra A)

/-- Membership is exactly the concrete connection intertwining equation. -/
theorem gomesPolynomialConnectionCommutant_mem_iff (A : ℝ[X]) (E : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    E ∈ gomesPolynomialConnectionCommutantAlgebra A ↔
      E.comp (gomesPolynomialFirstOrderLinearMap A) =
        (gomesPolynomialFirstOrderLinearMap A).comp E := by
  rw [gomesPolynomialConnectionCommutantAlgebra, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h
    exact (h _ (Set.mem_singleton _)).symm
  · intro h F hf
    have hf' : F = gomesPolynomialFirstOrderLinearMap A := Set.mem_singleton_iff.mp hf
    rw [hf']
    exact h.symm

/-- A commuting real map extends to a polynomial-linear endomorphism of the operator module. -/
def gomesPolynomialCommutantToModuleEnd (A : ℝ[X]) (E : GomesPolynomialConnectionCommutant A) :
    Module.End ℝ[X] (Module.AEval' (gomesPolynomialFirstOrderLinearMap A)) :=
  LinearMap.ofAEval (gomesPolynomialFirstOrderLinearMap A)
    ((Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)).toLinearMap.comp E.val) fun P => by
      change (Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A))
          (E.val (gomesPolynomialFirstOrderLinearMap A P)) =
        X • (Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)) (E.val P)
      rw [Module.AEval'.X_smul_of]
      apply (Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)).injective
      exact congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f P)
        ((gomesPolynomialConnectionCommutant_mem_iff A E.val).mp E.property)

/-- The promoted endomorphism acts by the original commuting real map. -/
theorem gomesPolynomialCommutantToModuleEnd_apply (A : ℝ[X])
    (E : GomesPolynomialConnectionCommutant A) (P : ℝ[X]) :
    gomesPolynomialCommutantToModuleEnd A E
      ((Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)) P) =
        (Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)) (E.val P) := rfl

/-- Forgetting polynomial scalars recovers a real map that commutes with the connection. -/
def gomesPolynomialModuleEndToCommutant (A : ℝ[X])
    (F : Module.End ℝ[X] (Module.AEval' (gomesPolynomialFirstOrderLinearMap A))) :
    GomesPolynomialConnectionCommutant A := by
  refine ⟨(Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)).symm.toLinearMap.comp
    ((F.restrictScalars ℝ).comp
      (Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)).toLinearMap), ?_⟩
  apply (gomesPolynomialConnectionCommutant_mem_iff A _).mpr
  apply LinearMap.ext
  intro P
  change (Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)).symm
      (F ((Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A))
        (gomesPolynomialFirstOrderLinearMap A P))) =
    gomesPolynomialFirstOrderLinearMap A
      ((Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)).symm
        (F ((Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A)) P)))
  rw [← Module.AEval'.X_smul_of, map_smul, Module.AEval'.of_symm_X_smul]

/-- Commuting real endomorphisms and polynomial-module endomorphisms are the same real algebra. -/
def gomesPolynomialConnectionCommutantModuleEquiv (A : ℝ[X]) :
    GomesPolynomialConnectionCommutant A ≃ₐ[ℝ]
      Module.End ℝ[X] (Module.AEval' (gomesPolynomialFirstOrderLinearMap A)) where
  toFun := gomesPolynomialCommutantToModuleEnd A
  invFun := gomesPolynomialModuleEndToCommutant A
  left_inv E := by
    apply Subtype.ext
    apply LinearMap.ext
    intro P
    rfl
  right_inv F := by
    apply LinearMap.ext
    intro P
    rfl
  map_mul' E F := by
    apply LinearMap.ext
    intro P
    rfl
  map_add' E F := by
    apply LinearMap.ext
    intro P
    rfl
  commutes' c := by
    apply LinearMap.ext
    intro P
    rfl

/-- Every polynomial in the connection is a genuine commuting endomorphism. -/
theorem gomesPolynomialConnection_aeval_mem_commutant (A F : ℝ[X]) :
    (Polynomial.aeval (gomesPolynomialFirstOrderLinearMap A)) F ∈
      gomesPolynomialConnectionCommutantAlgebra A := by
  apply (gomesPolynomialConnectionCommutant_mem_iff A _).mpr
  have h := congrArg (Polynomial.aeval (gomesPolynomialFirstOrderLinearMap A))
    (mul_comm F X)
  simpa only [map_mul, Polynomial.aeval_X, Module.End.mul_eq_comp] using h

/-- Polynomial operator evolution as an element of the full connection symmetry algebra. -/
def gomesPolynomialConnectionPolynomialSymmetry (A F : ℝ[X]) :
    GomesPolynomialConnectionCommutant A :=
  ⟨(Polynomial.aeval (gomesPolynomialFirstOrderLinearMap A)) F,
    gomesPolynomialConnection_aeval_mem_commutant A F⟩

end GaloisForLFunctions.HTGeometry
