/-
# Physical endpoint-complete path witnesses

The explicit two-qubit graph-state edge supplies a maximally projective seed with one Hermitian
endpoint observable whose spectral matrix has no zero off-diagonal entry.  Iterating the physical
leaf theorem produces static nearest-neighbour qubit Hamiltonians of arbitrary finite length with
the same endpoint-completeness property.
-/
import GaloisForLFunctions.HTGeometry.PhysicalEndpointCompletePathExtension

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix BigOperators

/-- The graph-state two-qubit edge, compressed to one endpoint observable, is the physical seed for
endpoint-complete path growth. -/
theorem exists_physicallyRealizedEndpointComplete_twoQubitSeed :
    ∃ Z : PhysicallyRealizedEndpointCompleteSystem,
      Z.State = (Bool × Bool) ∧
      Z.PhysicalState = (Bool × Bool) ∧
      Z.Observer = Bool := by
  classical
  obtain ⟨energy, henergyMaximal, _⟩ :=
    exists_maximallyProjectiveEnergy_close_fintype
      (fun _ : Bool × Bool => 0) 1 (by norm_num)
  have hcover : ∀ a b : Bool × Bool, a ≠ b →
      ∃ q : Fin 3, twoQubitEndpointTransition true q a b ≠ 0 := by
    intro a b hab
    have hadj :
        (transitionFamilySupportGraph (twoQubitEndpointTransition true)).Adj a b := by
      rw [transitionFamilySupportGraph_twoQubitEndpointTransition]
      simpa using hab
    obtain ⟨q, hq⟩ := hadj
    refine ⟨q, ?_⟩
    intro hz
    exact hq.2 (by simp [hz])
  obtain ⟨coefficient, hcoefficient⟩ :=
    exists_realProbeCombination_ne_zero
      (twoQubitEndpointTransition true) hcover
  let endpointProbe : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    realMatrixFamilyCombination (twoQubitEndpointProbe true) coefficient
  let endpointTransition : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    realMatrixFamilyCombination (twoQubitEndpointTransition true) coefficient
  let hamiltonian : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    twoQubitGraphBasis *
      Matrix.diagonal (fun i => (energy i : ℂ)) *
      twoQubitGraphBasisᴴ
  let tree : RootedTensorTree (Bool × Bool) Bool :=
    RootedTensorTree.edge Bool Bool Bool (Equiv.refl Bool)
  have hprobeLocal : ∀ q, tree.IsOneSite true (twoQubitEndpointProbe true q) := by
    intro q
    change ∃ R, twoQubitEndpointProbe true q =
      layerMatrixCoupling (1 : Matrix Bool Bool ℂ) R
    exact ⟨boolPauli q, by simp [twoQubitEndpointProbe]⟩
  have hcoordinate : endpointTransition =
      twoQubitGraphBasisᴴ * endpointProbe * twoQubitGraphBasis := by
    exact realMatrixFamilyCombination_coordinate
      twoQubitGraphBasis (twoQubitEndpointProbe true)
        (twoQubitEndpointTransition true) coefficient (fun _ => rfl)
  let Z : PhysicallyRealizedEndpointCompleteSystem :=
    { State := Bool × Bool
      PhysicalState := Bool × Bool
      Observer := Bool
      stateFintype := inferInstance
      stateDecidableEq := inferInstance
      stateNonempty := inferInstance
      physicalFintype := inferInstance
      physicalDecidableEq := inferInstance
      observerFintype := inferInstance
      observerDecidableEq := inferInstance
      energy := energy
      energy_maximallyProjective := henergyMaximal
      three_le_stateCard := by norm_num
      basis := twoQubitGraphBasis
      star_basis_mul_basis := twoQubitGraphBasis_conjTranspose_mul_self
      basis_mul_star_basis := twoQubitGraphBasis_mul_conjTranspose_self
      hamiltonian := hamiltonian
      hamiltonian_eq_diagonal := rfl
      tree := tree
      endpoint := true
      hamiltonian_local := by
        change True
        trivial
      endpointProbe := endpointProbe
      endpointProbe_isHermitian :=
        realMatrixFamilyCombination_isHermitian
          (twoQubitEndpointProbe true)
          (twoQubitEndpointProbe_isHermitian true) coefficient
      endpointProbe_local :=
        tree.isOneSite_realMatrixFamilyCombination true
          (twoQubitEndpointProbe true) coefficient hprobeLocal
      endpointTransition_ne_zero := by
        intro a b hab
        rw [← hcoordinate]
        exact hcoefficient a b hab }
  exact ⟨Z, rfl, rfl, rfl⟩

/-- A selected physical endpoint-complete qubit path, starting at two sites and attaching one qubit
at its current endpoint at every successor step. -/
noncomputable def physicalEndpointCompleteQubitPath :
    ℕ → PhysicallyRealizedEndpointCompleteSystem
  | 0 => Classical.choose exists_physicallyRealizedEndpointComplete_twoQubitSeed
  | n + 1 => Classical.choose (physicalEndpointCompleteQubitPath n).exists_leafExtension

@[simp] theorem physicalEndpointCompleteQubitPath_stateCard (n : ℕ) :
    Fintype.card (physicalEndpointCompleteQubitPath n).State = 2 ^ (n + 2) := by
  induction n with
  | zero =>
      have h := (Classical.choose_spec
        exists_physicallyRealizedEndpointComplete_twoQubitSeed).1
      calc
        Fintype.card (physicalEndpointCompleteQubitPath 0).State =
            Fintype.card (Bool × Bool) := Fintype.card_congr (Equiv.cast h)
        _ = 2 ^ (0 + 2) := by norm_num
  | succ n ih =>
      have h := (Classical.choose_spec
        (physicalEndpointCompleteQubitPath n).exists_leafExtension).1
      calc
        Fintype.card (physicalEndpointCompleteQubitPath (n + 1)).State =
            Fintype.card ((physicalEndpointCompleteQubitPath n).State × Bool) :=
          Fintype.card_congr (Equiv.cast h)
        _ = 2 ^ (n + 1 + 2) := by
          rw [Fintype.card_prod, Fintype.card_bool, ih]
          ring

@[simp] theorem physicalEndpointCompleteQubitPath_physicalCard (n : ℕ) :
    Fintype.card (physicalEndpointCompleteQubitPath n).PhysicalState = 2 ^ (n + 2) := by
  induction n with
  | zero =>
      have h := (Classical.choose_spec
        exists_physicallyRealizedEndpointComplete_twoQubitSeed).2.1
      calc
        Fintype.card (physicalEndpointCompleteQubitPath 0).PhysicalState =
            Fintype.card (Bool × Bool) := Fintype.card_congr (Equiv.cast h)
        _ = 2 ^ (0 + 2) := by norm_num
  | succ n ih =>
      have h := (Classical.choose_spec
        (physicalEndpointCompleteQubitPath n).exists_leafExtension).2.1
      calc
        Fintype.card (physicalEndpointCompleteQubitPath (n + 1)).PhysicalState =
            Fintype.card ((physicalEndpointCompleteQubitPath n).PhysicalState × Bool) :=
          Fintype.card_congr (Equiv.cast h)
        _ = 2 ^ (n + 1 + 2) := by
          rw [Fintype.card_prod, Fintype.card_bool, ih]
          ring

@[simp] theorem physicalEndpointCompleteQubitPath_observerCard (n : ℕ) :
    Fintype.card (physicalEndpointCompleteQubitPath n).Observer = n + 2 := by
  induction n with
  | zero =>
      have h := (Classical.choose_spec
        exists_physicallyRealizedEndpointComplete_twoQubitSeed).2.2
      calc
        Fintype.card (physicalEndpointCompleteQubitPath 0).Observer =
            Fintype.card Bool := Fintype.card_congr (Equiv.cast h)
        _ = 0 + 2 := by norm_num
  | succ n ih =>
      have h := (Classical.choose_spec
        (physicalEndpointCompleteQubitPath n).exists_leafExtension).2.2
      calc
        Fintype.card (physicalEndpointCompleteQubitPath (n + 1)).Observer =
            Fintype.card (Sum (physicalEndpointCompleteQubitPath n).Observer Unit) :=
          Fintype.card_congr (Equiv.cast h)
        _ = n + 1 + 2 := by
          rw [Fintype.card_sum, Fintype.card_unit, ih]

end

end GaloisForLFunctions.HTGeometry
