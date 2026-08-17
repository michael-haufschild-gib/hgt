import GaloisForLFunctions.HTGeometry.BlockExtensionSecondOrderResponse
import GaloisForLFunctions.HTGeometry.PhysicalObserverSpectralRealization
import GaloisForLFunctions.HTGeometry.ArbitraryGraphLocalHamiltonianGenericityLaw

/-!
# The layer split is a physical one-site field plus one edge term

Attaching a qubit to an old architecture splits every old level by the new local field and couples
the two layers by an edge operator.  In the split eigenbasis those two data are exactly the abstract
`layerSplitEnergy` and `layerCrossPerturbation`: the first is the diagonal of
`H_old ⊗ 1 + 1 ⊗ diag(field)`, the second is `M ⊗ X` for the exchange matrix `X` of the attached
qubit.

So the abstract split system is realized inside the onsite-plus-edge class of the leaf-extended
architecture: it is a local Hamiltonian, it is Hermitian whenever the old spectrum, the field and
the attachment operator are, and its trace is twice the old trace -- hence it is traceless exactly
when the old spectrum is.
-/

open scoped Kronecker

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Realization

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The local field of the attached qubit: the level splitting `±z/2`. -/
def layerFieldShift (z : ℂ) : Bool → ℂ := fun s => if s then -(z / 2) else z / 2

/-- The exchange matrix of the attached qubit. -/
def layerExchange : Matrix Bool Bool ℂ := selectedLayerExchangeMatrix false true

theorem layerExchange_apply (u v : Bool) :
    layerExchange u v = if u = v then 0 else 1 := by
  cases u <;> cases v <;> simp [layerExchange, selectedLayerExchangeMatrix]

/-- **The cross perturbation is the edge term `M ⊗ X`.** -/
theorem layerCrossPerturbation_eq_coupling (M : Matrix A A ℂ) :
    layerCrossPerturbation M = layerMatrixCoupling M layerExchange := by
  ext x y
  show layerCrossPerturbation M x y = M x.1 y.1 * layerExchange x.2 y.2
  rw [layerExchange_apply]
  by_cases h : x.2 = y.2
  · rw [layerCrossPerturbation_apply_same h, if_pos h, mul_zero]
  · rw [layerCrossPerturbation_apply_cross h, if_neg h, mul_one]

/-- **The split spectrum is the old Hamiltonian plus the new one-site field.** -/
theorem diagonal_layerSplitEnergy_eq (E : A → ℂ) (z : ℂ) :
    Matrix.diagonal (layerSplitEnergy E z)
      = layerMatrixCoupling (Matrix.diagonal E) (1 : Matrix Bool Bool ℂ)
        + layerMatrixCoupling (1 : Matrix A A ℂ) (Matrix.diagonal (layerFieldShift z)) := by
  ext x y
  show Matrix.diagonal (layerSplitEnergy E z) x y
      = (Matrix.diagonal E) x.1 y.1 * (1 : Matrix Bool Bool ℂ) x.2 y.2
        + (1 : Matrix A A ℂ) x.1 y.1 * (Matrix.diagonal (layerFieldShift z)) x.2 y.2
  rw [Matrix.diagonal_apply, Matrix.diagonal_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.one_apply]
  by_cases h1 : x.1 = y.1
  · by_cases h2 : x.2 = y.2
    · have hxy : x = y := Prod.ext h1 h2
      rw [if_pos hxy, if_pos h1, if_pos h2, if_pos h1, if_pos h2, layerSplitEnergy, layerFieldShift]
      simp
    · have hxy : x ≠ y := fun h => h2 (by rw [h])
      rw [if_neg hxy, if_pos h1, if_neg h2, if_pos h1, if_neg h2]
      ring
  · have hxy : x ≠ y := fun h => h1 (by rw [h])
    rw [if_neg hxy, if_neg h1, if_neg h1]
    ring

/-- **The physical realisation.**  The split system is the leaf Hamiltonian of the attached qubit:
old Hamiltonian, new one-site field, one parent--leaf edge term. -/
theorem layerSplit_eq_physicalLeafHamiltonian (E : A → ℂ) (z : ℂ) (M : Matrix A A ℂ) :
    Matrix.diagonal (layerSplitEnergy E z) + layerCrossPerturbation M
      = physicalLeafHamiltonian (Matrix.diagonal E) M (layerFieldShift z) layerExchange := by
  rw [diagonal_layerSplitEnergy_eq, layerCrossPerturbation_eq_coupling, physicalLeafHamiltonian]

/-- The split system is Hermitian whenever the old spectrum, the field and the attachment are. -/
theorem isHermitian_layerSplit {E : A → ℂ} {z : ℂ} {M : Matrix A A ℂ}
    (hE : ∀ a, star (E a) = E a) (hz : star z = z) (hM : M.IsHermitian) :
    (Matrix.diagonal (layerSplitEnergy E z) + layerCrossPerturbation M).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.add_apply, star_add,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  have hcross : star (layerCrossPerturbation M y x) = layerCrossPerturbation M x y := by
    by_cases h : x.2 = y.2
    · rw [layerCrossPerturbation_apply_same h, layerCrossPerturbation_apply_same h.symm, star_zero]
    · have h' : ¬ y.2 = x.2 := fun hh => h hh.symm
      rw [layerCrossPerturbation_apply_cross h, layerCrossPerturbation_apply_cross h']
      have hMx := congrFun (congrFun hM x.1) y.1
      rw [Matrix.conjTranspose_apply] at hMx
      exact hMx
  rw [hcross]
  congr 1
  by_cases hxy : y = x
  · rw [if_pos hxy, if_pos hxy.symm, layerSplitEnergy, layerSplitEnergy, star_add, hE, hxy]
    congr 1
    cases x.2 <;> simp [hz]
  · have hxy' : ¬ x = y := fun h => hxy h.symm
    rw [if_neg hxy, if_neg hxy', star_zero]

/-- The trace of the split system is twice the old trace: the field cancels between the layers and
the edge term is off-diagonal. -/
theorem trace_layerSplit (E : A → ℂ) (z : ℂ) (M : Matrix A A ℂ) :
    (Matrix.diagonal (layerSplitEnergy E z) + layerCrossPerturbation M).trace
      = 2 * ∑ a, E a := by
  classical
  rw [Matrix.trace_add, Matrix.trace_diagonal]
  have hcross : (layerCrossPerturbation M).trace = 0 := by
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun x _ => ?_
    exact layerCrossPerturbation_diagonal M x
  rw [hcross, add_zero, Fintype.sum_prod_type]
  have hinner : ∀ a : A, (∑ s : Bool, layerSplitEnergy E z (a, s)) = 2 * E a := by
    intro a
    rw [Fintype.sum_bool, layerSplitEnergy, layerSplitEnergy]
    simp
    ring
  rw [Finset.sum_congr rfl fun a _ => hinner a, ← Finset.mul_sum]

/-- **The split system is a local Hamiltonian of the leaf-extended architecture.** -/
theorem isLocalHamiltonian_layerSplit {Physical Observer : Type}
    [Fintype Physical] [DecidableEq Physical] [Fintype Observer] [DecidableEq Observer]
    (old : RootedTensorTree Physical Observer) (parent : Observer)
    (E : Physical → ℂ) (z : ℂ) (M : Matrix Physical Physical ℂ)
    (hE : old.IsLocalHamiltonian (Matrix.diagonal E))
    (hM : old.IsOneSite parent M) :
    (RootedTensorTree.leaf old Bool parent).IsLocalHamiltonian
      (Matrix.diagonal (layerSplitEnergy E z) + layerCrossPerturbation M) :=
  ⟨Matrix.diagonal E, M, layerFieldShift z, layerExchange, hE, hM,
    layerSplit_eq_physicalLeafHamiltonian E z M⟩

/-- **The split system lies in the architecture's Hermitian local Hamiltonian space.** -/
theorem layerSplit_mem_hermitianLocalHamiltonianSubmodule {Physical Observer : Type}
    [Fintype Physical] [DecidableEq Physical] [Fintype Observer] [DecidableEq Observer]
    (old : RootedTensorTree Physical Observer) (parent : Observer)
    {E : Physical → ℂ} {z : ℂ} {M : Matrix Physical Physical ℂ}
    (hlocal : old.IsLocalHamiltonian (Matrix.diagonal E))
    (hone : old.IsOneSite parent M)
    (hE : ∀ a, star (E a) = E a) (hz : star z = z)
    (hM : M.IsHermitian) :
    (Matrix.diagonal (layerSplitEnergy E z) + layerCrossPerturbation M)
      ∈ (RootedTensorTree.leaf old Bool parent).hermitianLocalHamiltonianSubmodule :=
  RootedTensorTree.mem_hermitianLocalHamiltonianSubmodule _
    (isLocalHamiltonian_layerSplit old parent E z M hlocal hone)
    (isHermitian_layerSplit hE hz hM)

/-- **The traceless case.**  A traceless old spectrum makes the whole split system traceless, so it
lies in the trace-zero part of the local Hamiltonian space. -/
theorem layerSplit_mem_traceless {Physical Observer : Type}
    [Fintype Physical] [DecidableEq Physical] [Fintype Observer] [DecidableEq Observer]
    (old : RootedTensorTree Physical Observer) (parent : Observer)
    {E : Physical → ℂ} {z : ℂ} {M : Matrix Physical Physical ℂ}
    (hlocal : old.IsLocalHamiltonian (Matrix.diagonal E))
    (hone : old.IsOneSite parent M)
    (hE : ∀ a, star (E a) = E a) (hz : star z = z)
    (hM : M.IsHermitian) (htrace : ∑ a, E a = 0) :
    (Matrix.diagonal (layerSplitEnergy E z) + layerCrossPerturbation M)
      ∈ (RootedTensorTree.leaf old Bool parent).hermitianLocalHamiltonianSubmodule ⊓
        LinearMap.ker ((Matrix.traceLinearMap (Physical × Bool) ℂ ℂ).restrictScalars ℝ) := by
  refine ⟨layerSplit_mem_hermitianLocalHamiltonianSubmodule old parent hlocal hone hE hz hM, ?_⟩
  show (Matrix.traceLinearMap (Physical × Bool) ℂ ℂ)
      (Matrix.diagonal (layerSplitEnergy E z) + layerCrossPerturbation M) = 0
  rw [Matrix.traceLinearMap_apply, trace_layerSplit, htrace, mul_zero]

end Realization

end

end GaloisForLFunctions.HTGeometry
