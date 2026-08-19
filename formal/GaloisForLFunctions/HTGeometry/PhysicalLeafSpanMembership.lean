/-
# The physical leaf Hamiltonian lies in the architecture's interaction span

A leaf-extended tensor tree has as its local Hamiltonians exactly the sums of an old Hamiltonian, a
field on the new site and one parent--leaf edge term.  Any such assembly with Hermitian data is
therefore a Hermitian local Hamiltonian, hence lies in the architecture's Hermitian local
Hamiltonian submodule, hence in the real span of its canonical generators -- which is the shell's
own interaction family.

Main results:
* `mem_span_realMatrixSubmoduleGenerator` — a submodule element is in the span of its generators.
* `isLocalHamiltonian_physicalLeaf` — the physical leaf assembly is local.
* `isHermitian_physicalLeafHamiltonian` — and Hermitian at Hermitian data.
* `physicalLeaf_mem_span_generator` — **hence it lies in the interaction span**.
-/
import GaloisForLFunctions.HTGeometry.LayerSplitPhysicalRealization
import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionChart

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- A submodule element lies in the real span of its canonical generators. -/
theorem mem_span_realMatrixSubmoduleGenerator {I : Type u} [Fintype I]
    (L : Submodule ℝ (Matrix I I ℂ)) {H : Matrix I I ℂ} (hH : H ∈ L) :
    H ∈ Submodule.span ℝ (Set.range (realMatrixSubmoduleGenerator L)) := by
  classical
  obtain ⟨p, hp⟩ := exists_realAffineMatrix_eq_of_mem_submodule L H hH
  have hsum : (∑ i, p i • realMatrixSubmoduleGenerator L i) = H := by
    rw [← hp]
    ext a b
    simp [realAffineMatrix, Matrix.sum_apply]
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable {Physical Observer : Type}
  [Fintype Physical] [DecidableEq Physical] [Fintype Observer] [DecidableEq Observer]

/-- **The physical leaf assembly is a local Hamiltonian of the extended architecture.** -/
theorem isLocalHamiltonian_physicalLeaf (old : RootedTensorTree Physical Observer)
    (parent : Observer) (Hold M : Matrix Physical Physical ℂ) (shift : Bool → ℂ)
    (edge : Matrix Bool Bool ℂ)
    (hlocal : old.IsLocalHamiltonian Hold) (hone : old.IsOneSite parent M) :
    (RootedTensorTree.leaf old Bool parent).IsLocalHamiltonian
      (physicalLeafHamiltonian Hold M shift edge) :=
  ⟨Hold, M, shift, edge, hlocal, hone, rfl⟩

theorem isHermitian_diagonal_of_star {ρ : Type*} [DecidableEq ρ] {shift : ρ → ℂ}
    (hshift : ∀ s, star (shift s) = shift s) : (Matrix.diagonal shift).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : y = x
  · rw [if_pos h, if_pos h.symm, hshift, h]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), star_zero]

/-- **The physical leaf assembly is Hermitian at Hermitian data.** -/
theorem isHermitian_physicalLeafHamiltonian {P ρ : Type*} [DecidableEq P] [DecidableEq ρ]
    {Hold M : Matrix P P ℂ} {shift : ρ → ℂ} {edge : Matrix ρ ρ ℂ}
    (hHold : Hold.IsHermitian) (hM : M.IsHermitian)
    (hshift : ∀ s, star (shift s) = shift s) (hedge : edge.IsHermitian) :
    (physicalLeafHamiltonian Hold M shift edge).IsHermitian := by
  rw [physicalLeafHamiltonian]
  refine Matrix.IsHermitian.add (Matrix.IsHermitian.add ?_ ?_) ?_
  · exact layerMatrixCoupling_isHermitian hHold Matrix.isHermitian_one
  · exact layerMatrixCoupling_isHermitian Matrix.isHermitian_one
      (isHermitian_diagonal_of_star hshift)
  · exact layerMatrixCoupling_isHermitian hM hedge

/-- **The physical leaf Hamiltonian lies in the real span of the architecture's canonical
interaction generators.** -/
theorem physicalLeaf_mem_span_generator (old : RootedTensorTree Physical Observer)
    (parent : Observer) {Hold M : Matrix Physical Physical ℂ} {shift : Bool → ℂ}
    {edge : Matrix Bool Bool ℂ}
    (hlocal : old.IsLocalHamiltonian Hold) (hone : old.IsOneSite parent M)
    (hHold : Hold.IsHermitian) (hM : M.IsHermitian)
    (hshift : ∀ s, star (shift s) = shift s) (hedge : edge.IsHermitian) :
    physicalLeafHamiltonian Hold M shift edge ∈
      Submodule.span ℝ (Set.range (realMatrixSubmoduleGenerator
        (RootedTensorTree.leaf old Bool parent).hermitianLocalHamiltonianSubmodule)) :=
  mem_span_realMatrixSubmoduleGenerator _
    (RootedTensorTree.mem_hermitianLocalHamiltonianSubmodule _
      (isLocalHamiltonian_physicalLeaf old parent Hold M shift edge hlocal hone)
      (isHermitian_physicalLeafHamiltonian hHold hM hshift hedge))

end

end GaloisForLFunctions.HTGeometry
