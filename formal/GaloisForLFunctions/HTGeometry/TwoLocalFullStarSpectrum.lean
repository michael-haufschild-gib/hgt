import GaloisForLFunctions.HTGeometry.TwoLocalEdgeMonodromy
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-!
# One full two-local Hamiltonian carrying the exact edge transposition

The isolated two-level blocks from `TwoLocalEdgeMonodromy` are assembled
here into one matrix on the complete Boolean Hilbert basis.  Its
characteristic polynomial factors exactly over the environment blocks, so
the previously constructed signed branches are roots of one full
characteristic polynomial rather than of unrelated `2 × 2` surrogates.

The same matrix is exhibited coefficient-by-coefficient as a complexified
distinguished-star two-local Hamiltonian: onsite terms, distinguished-star
two-body terms, and one transverse flip.  On the real parameter slice it is
Hermitian.  Along the explicit complex loop its full simple spectrum
undergoes exactly the selected Boolean-edge transposition.
-/

open scoped BigOperators

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

/-- The Hamiltonian block whose `λI-H` matrix is
`twoLocalEdgeCharacteristicMatrix`. -/
def twoLocalEdgeHamiltonianBlock {m : ℕ}
    (z₀ z : Fin m → Bool) (w : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![((starIsingBinaryCode z₀ z : ℂ) + w), 1;
      1, -((starIsingBinaryCode z₀ z : ℂ) + w)]

theorem twoLocalEdgeCharacteristicMatrix_eq_scalar_sub {m : ℕ}
    (z₀ z : Fin m → Bool) (w lam : ℂ) :
    Matrix.scalar (Fin 2) lam -
        twoLocalEdgeHamiltonianBlock z₀ z w =
      twoLocalEdgeCharacteristicMatrix z₀ z w lam := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoLocalEdgeHamiltonianBlock,
      twoLocalEdgeCharacteristicMatrix] <;> ring

/-- Block-diagonal realization before replacing `Fin 2` by `Bool`. -/
def twoLocalBlockHamiltonianMatrix {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ) :
    Matrix (Fin 2 × (Fin m → Bool))
      (Fin 2 × (Fin m → Bool)) ℂ :=
  Matrix.blockDiagonal fun z =>
    twoLocalEdgeHamiltonianBlock z₀ z w

theorem twoLocalBlockCharacteristicMatrix_eq {m : ℕ}
    (z₀ : Fin m → Bool) (w lam : ℂ) :
    Matrix.scalar (Fin 2 × (Fin m → Bool)) lam -
        twoLocalBlockHamiltonianMatrix z₀ w =
      Matrix.blockDiagonal fun z =>
        twoLocalEdgeCharacteristicMatrix z₀ z w lam := by
  have hblocks :
      (fun z =>
        twoLocalEdgeCharacteristicMatrix z₀ z w lam) =
      (fun z =>
        Matrix.scalar (Fin 2) lam -
          twoLocalEdgeHamiltonianBlock z₀ z w) := by
    funext z
    exact
      (twoLocalEdgeCharacteristicMatrix_eq_scalar_sub
        z₀ z w lam).symm
  rw [hblocks]
  ext ⟨i, z⟩ ⟨j, y⟩
  by_cases hzy : z = y
  · subst y
    simp [twoLocalBlockHamiltonianMatrix,
      Matrix.blockDiagonal_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
  · have hp : (i, z) ≠ (j, y) := by
      intro h
      exact hzy (congrArg Prod.snd h)
    simp [twoLocalBlockHamiltonianMatrix,
      Matrix.blockDiagonal_apply, Matrix.scalar_apply,
      hzy, hp]

/-- Exact characteristic-polynomial product over all Boolean
environments. -/
theorem twoLocalBlockHamiltonian_charpoly_eval_eq_prod {m : ℕ}
    (z₀ : Fin m → Bool) (w lam : ℂ) :
    (twoLocalBlockHamiltonianMatrix z₀ w).charpoly.eval lam =
      ∏ z : Fin m → Bool,
        (twoLocalEdgeCharacteristicMatrix z₀ z w lam).det := by
  rw [Matrix.eval_charpoly,
    twoLocalBlockCharacteristicMatrix_eq,
    Matrix.det_blockDiagonal]

/-- Full Hamiltonian in the natural Boolean computational basis. -/
def twoLocalStarHamiltonianMatrix {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ) :
    Matrix (Bool × (Fin m → Bool))
      (Bool × (Fin m → Bool)) ℂ :=
  fun x y =>
    if x.2 = y.2 then
      if x.1 = y.1 then
        if x.1 then
          -((starIsingBinaryCode z₀ x.2 : ℂ) + w)
        else
          (starIsingBinaryCode z₀ x.2 : ℂ) + w
      else 1
    else 0

/-- Change of index from the `2 × 2` block convention to the Boolean
computational basis. -/
def twoLocalFullIndexEquiv (m : ℕ) :
    (Fin 2 × (Fin m → Bool)) ≃
      (Bool × (Fin m → Bool)) :=
  Equiv.prodCongr finTwoEquiv (Equiv.refl _)

theorem twoLocalBlockHamiltonian_reindex_eq_starHamiltonian {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ) :
    Matrix.reindex (twoLocalFullIndexEquiv m)
        (twoLocalFullIndexEquiv m)
        (twoLocalBlockHamiltonianMatrix z₀ w) =
      twoLocalStarHamiltonianMatrix z₀ w := by
  ext ⟨b, z⟩ ⟨d, y⟩
  cases b <;> cases d <;> by_cases hzy : z = y <;>
    simp [Matrix.reindex_apply, twoLocalFullIndexEquiv,
      finTwoEquiv, twoLocalBlockHamiltonianMatrix,
      twoLocalEdgeHamiltonianBlock,
      twoLocalStarHamiltonianMatrix,
      Matrix.blockDiagonal_apply, hzy]

theorem twoLocalStarHamiltonian_charpoly_eval_eq_prod {m : ℕ}
    (z₀ : Fin m → Bool) (w lam : ℂ) :
    (twoLocalStarHamiltonianMatrix z₀ w).charpoly.eval lam =
      ∏ z : Fin m → Bool,
        (twoLocalEdgeCharacteristicMatrix z₀ z w lam).det := by
  rw [← twoLocalBlockHamiltonian_reindex_eq_starHamiltonian,
    Matrix.charpoly_reindex,
    twoLocalBlockHamiltonian_charpoly_eval_eq_prod]

/-- Every continued signed sheet is a root of the characteristic
polynomial of the same full matrix. -/
theorem twoLocalGlobalEigenvalueLift_fullMatrix_root {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) :
    (twoLocalStarHamiltonianMatrix z₀
      (twoLocalSelectedEdgeParameter s)).charpoly.eval
        (twoLocalGlobalEigenvalueLift z₀ x s) = 0 := by
  rw [twoLocalStarHamiltonian_charpoly_eval_eq_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ x.2)
  exact det_twoLocalGlobalEigenvalueLift_eq_zero z₀ x s

/-! ## Exact two-local realization -/

/-- Standard coefficient model for one transverse distinguished spin with
onsite and distinguished-star diagonal interactions. -/
def distinguishedStarTwoLocalHamiltonian {m : ℕ}
    (constant longitudinal transverse : ℂ)
    (onsite interaction : Fin m → ℂ) :
    Matrix (Bool × (Fin m → Bool))
      (Bool × (Fin m → Bool)) ℂ :=
  fun x y =>
    if x = y then
      constant +
        longitudinal * (boolOccupation x.1 : ℂ) +
        ∑ i, onsite i * (boolOccupation (x.2 i) : ℂ) +
        ∑ i, interaction i *
          (boolOccupation x.1 : ℂ) *
          (boolOccupation (x.2 i) : ℂ)
    else if x.2 = y.2 then transverse else 0

/-- Membership in the explicit complexified distinguished-star two-local
Hamiltonian family. -/
def IsComplexDistinguishedStarTwoLocalHamiltonian {m : ℕ}
    (H : Matrix (Bool × (Fin m → Bool))
      (Bool × (Fin m → Bool)) ℂ) : Prop :=
  ∃ (constant longitudinal transverse : ℂ)
      (onsite interaction : Fin m → ℂ),
    H = distinguishedStarTwoLocalHamiltonian
      constant longitudinal transverse onsite interaction

theorem twoLocalStarHamiltonian_diagonal {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ)
    (x : Bool × (Fin m → Bool)) :
    twoLocalStarHamiltonianMatrix z₀ w x x =
      (twoLocalSymmetricIsolatedEdgeEnergy z₀ x : ℂ) +
        w - 2 * w * (boolOccupation x.1 : ℂ) := by
  rcases x with ⟨b, z⟩
  cases b <;>
    simp [twoLocalStarHamiltonianMatrix,
      twoLocalSymmetricIsolatedEdgeEnergy, boolOccupation] <;>
    ring

/-- The full matrix is genuinely two-local for every complex continuation
parameter, not merely block diagonal by declaration. -/
theorem twoLocalStarHamiltonian_is_complex_twoLocal {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ) :
    IsComplexDistinguishedStarTwoLocalHamiltonian
      (twoLocalStarHamiltonianMatrix z₀ w) := by
  rcases
      twoLocalSymmetricIsolatedEdgeEnergy_isDistinguishedStarTwoLocal
        z₀ with
    ⟨constant, longitudinal, onsite, interaction, henergy⟩
  refine ⟨(constant : ℂ) + w,
    (longitudinal : ℂ) - 2 * w, 1,
    fun i => (onsite i : ℂ),
    fun i => (interaction i : ℂ), ?_⟩
  ext x y
  by_cases hxy : x = y
  · subst y
    rw [twoLocalStarHamiltonian_diagonal]
    simp only [distinguishedStarTwoLocalHamiltonian, if_pos]
    have h := congrArg (fun q : ℤ => (q : ℂ)) (henergy x)
    push_cast at h
    rw [h]
    ring
  · by_cases henv : x.2 = y.2
    · have hbit : x.1 ≠ y.1 := by
        intro hb
        exact hxy (Prod.ext hb henv)
      simp [twoLocalStarHamiltonianMatrix,
        distinguishedStarTwoLocalHamiltonian, hxy, henv,
        hbit]
    · simp [twoLocalStarHamiltonianMatrix,
        distinguishedStarTwoLocalHamiltonian, hxy, henv]

/-- The real slice of the family consists of Hermitian Hamiltonians. -/
theorem twoLocalStarHamiltonian_isHermitian_of_star_eq {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ) (hw : star w = w) :
    (twoLocalStarHamiltonianMatrix z₀ w).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨b, z⟩ ⟨d, y⟩
  cases b <;> cases d <;>
    (by_cases hzy : z = y
     · subst y
       simp [twoLocalStarHamiltonianMatrix, hw]
     · have hyz : y ≠ z := Ne.symm hzy
       simp [twoLocalStarHamiltonianMatrix, hzy, hyz])

/-! ## Full-matrix monodromy capstone -/

theorem continuous_twoLocalStarHamiltonian_selectedLoop {m : ℕ}
    (z₀ : Fin m → Bool) :
    Continuous fun s : I =>
      twoLocalStarHamiltonianMatrix z₀
        (twoLocalSelectedEdgeParameter s) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  unfold twoLocalStarHamiltonianMatrix
  split_ifs
  · exact
      (continuous_const.add
        continuous_twoLocalSelectedEdgeParameter).neg
  · exact
      continuous_const.add
        continuous_twoLocalSelectedEdgeParameter
  · exact continuous_const
  · exact continuous_const

theorem twoLocalStarHamiltonian_selectedLoop_closed {m : ℕ}
    (z₀ : Fin m → Bool) :
    twoLocalStarHamiltonianMatrix z₀
        (twoLocalSelectedEdgeParameter 1) =
      twoLocalStarHamiltonianMatrix z₀
        (twoLocalSelectedEdgeParameter 0) := by
  rw [twoLocalSelectedEdgeParameter_closed]

/-- One closed loop of one full complexified two-local Hamiltonian has a
simple spectrum throughout and acts on that complete spectrum by exactly
one selected Boolean-edge transposition. -/
theorem twoLocal_fullMatrix_exact_singleEdge_transposition {m : ℕ}
    (z₀ : Fin m → Bool) :
    Continuous (fun s : I =>
        twoLocalStarHamiltonianMatrix z₀
          (twoLocalSelectedEdgeParameter s)) ∧
      twoLocalStarHamiltonianMatrix z₀
          (twoLocalSelectedEdgeParameter 1) =
        twoLocalStarHamiltonianMatrix z₀
          (twoLocalSelectedEdgeParameter 0) ∧
      (∀ s,
        IsComplexDistinguishedStarTwoLocalHamiltonian
          (twoLocalStarHamiltonianMatrix z₀
            (twoLocalSelectedEdgeParameter s))) ∧
      (∀ x s,
        (twoLocalStarHamiltonianMatrix z₀
          (twoLocalSelectedEdgeParameter s)).charpoly.eval
            (twoLocalGlobalEigenvalueLift z₀ x s) = 0) ∧
      (∀ s,
        Function.Injective fun x =>
          twoLocalGlobalEigenvalueLift z₀ x s) ∧
      ∀ x,
        twoLocalGlobalEigenvalueLift z₀ x 1 =
          twoLocalGlobalEigenvalueLift z₀
            (twoLocalSelectedEdgeSwap z₀ x) 0 := by
  exact
    ⟨continuous_twoLocalStarHamiltonian_selectedLoop z₀,
      twoLocalStarHamiltonian_selectedLoop_closed z₀,
      fun s => twoLocalStarHamiltonian_is_complex_twoLocal z₀
        (twoLocalSelectedEdgeParameter s),
      twoLocalGlobalEigenvalueLift_fullMatrix_root z₀,
      twoLocalGlobalEigenvalueLift_injective z₀,
      twoLocalGlobalEigenvalueLift_endpoint_permutation z₀⟩

end GaloisForLFunctions.HTGeometry
