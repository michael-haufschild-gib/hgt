import GaloisForLFunctions.HTGeometry.PhysicalObserverSpectralLeafExtension

/-!
# Explicit physical two-qubit seed

The graph-state basis of one qubit edge turns each endpoint's three Pauli
probes into the three nonzero translations of the four spectral labels.
Thus every endpoint transition graph is complete.  This supplies the
all-local-dimensions-two base missing from one-site nonbipartite growth.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix BigOperators

universe u

/-- Two-qubit edge graph-state basis `CZ (H ⊗ H)`, written entrywise. -/
def twoQubitGraphBasis :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x a =>
    if Bool.xor
        (Bool.xor (a.1 && x.1) (a.2 && x.2))
        (x.1 && x.2)
    then -(1 / 2 : ℂ)
    else (1 / 2 : ℂ)

theorem twoQubitGraphBasis_conjTranspose_mul_self :
    twoQubitGraphBasisᴴ * twoQubitGraphBasis =
      (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  have hstarTwo :
      (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    norm_num
  ext a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;>
    fin_cases b₁ <;> fin_cases b₂ <;>
    norm_num [twoQubitGraphBasis, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, Matrix.one_apply, hstarTwo]

theorem twoQubitGraphBasis_mul_conjTranspose_self :
    twoQubitGraphBasis * twoQubitGraphBasisᴴ =
      (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  have hstarTwo :
      (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    norm_num
  ext a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;>
    fin_cases b₁ <;> fin_cases b₂ <;>
    norm_num [twoQubitGraphBasis, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, Matrix.one_apply, hstarTwo]

/-- Pauli `X`, `Y`, and `Z`, indexed in that order. -/
def boolPauli (q : Fin 3) : Matrix Bool Bool ℂ :=
  if q = 0 then
    fun x y => if x = y then 0 else 1
  else if q = 1 then
    fun x y =>
      if x = y then 0
      else if x = false then -Complex.I else Complex.I
  else
    fun x y =>
      if x = y then
        if x = false then 1 else -1
      else 0

theorem boolPauli_isHermitian
    (q : Fin 3) :
    (boolPauli q).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  fin_cases q <;> fin_cases x <;> fin_cases y <;>
    simp [boolPauli, Matrix.conjTranspose_apply]

/-- The three physical probes at either endpoint of one qubit edge. -/
def twoQubitEndpointProbe
    (s : Bool) (q : Fin 3) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  if s = false then
    layerMatrixCoupling (boolPauli q)
      (1 : Matrix Bool Bool ℂ)
  else
    layerMatrixCoupling (1 : Matrix Bool Bool ℂ)
      (boolPauli q)

theorem twoQubitEndpointProbe_isHermitian
    (s : Bool) (q : Fin 3) :
    (twoQubitEndpointProbe s q).IsHermitian := by
  by_cases hs : s = false
  · simp only [twoQubitEndpointProbe, if_pos hs]
    exact layerMatrixCoupling_isHermitian
      (boolPauli_isHermitian q) Matrix.isHermitian_one
  · simp only [twoQubitEndpointProbe, if_neg hs]
    exact layerMatrixCoupling_isHermitian
      Matrix.isHermitian_one (boolPauli_isHermitian q)

/-- Exact graph-basis spectral coordinates of an endpoint Pauli. -/
def twoQubitEndpointTransition
    (s : Bool) (q : Fin 3) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  twoQubitGraphBasisᴴ *
    twoQubitEndpointProbe s q *
    twoQubitGraphBasis

/-- Spectral-label translation induced by an endpoint Pauli. -/
def twoQubitEndpointFlip
    (s : Bool) (q : Fin 3)
    (a : Bool × Bool) : Bool × Bool :=
  if q = 0 then
    if s = false then (a.1, !a.2) else (!a.1, a.2)
  else if q = 1 then
    (!a.1, !a.2)
  else if s = false then
    (!a.1, a.2)
  else
    (a.1, !a.2)

set_option maxHeartbeats 1000000 in
/-- Each endpoint Pauli has exactly one nonzero translated entry in every
spectral row. -/
theorem twoQubitEndpointTransition_ne_zero_iff
    (s : Bool) (q : Fin 3)
    (a b : Bool × Bool) :
    twoQubitEndpointTransition s q a b ≠ 0 ↔
      b = twoQubitEndpointFlip s q a := by
  have hstarTwo :
      (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    norm_num
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases s <;> fin_cases q <;>
    fin_cases a₁ <;> fin_cases a₂ <;>
    fin_cases b₁ <;> fin_cases b₂ <;>
    norm_num [twoQubitEndpointTransition,
      twoQubitEndpointProbe, twoQubitEndpointFlip,
      twoQubitGraphBasis, boolPauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fintype.sum_bool,
      hstarTwo]

theorem twoQubitEndpointTransition_isHermitian
    (s : Bool) (q : Fin 3) :
    (twoQubitEndpointTransition s q).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul
    twoQubitGraphBasis (twoQubitEndpointProbe_isHermitian s q)

/-- At either endpoint, the three local Pauli probes connect every pair of
graph-basis labels. -/
theorem transitionFamilySupportGraph_twoQubitEndpointTransition
    (s : Bool) :
    transitionFamilySupportGraph
        (twoQubitEndpointTransition s) =
      (⊤ : SimpleGraph (Bool × Bool)) := by
  ext a b
  constructor
  · rintro ⟨q, hq⟩
    simpa using hq.1
  · intro hab
    have hne : a ≠ b := by
      simpa using hab
    rcases a with ⟨a₁, a₂⟩
    rcases b with ⟨b₁, b₂⟩
    fin_cases s <;> fin_cases a₁ <;> fin_cases a₂ <;>
      fin_cases b₁ <;> fin_cases b₂
    all_goals
      try simp_all only [Bool.false_eq_true, Bool.true_eq_false,
        Prod.mk.injEq, not_false_eq_true, and_self,
        not_true_eq_false, or_false, false_or]
    all_goals
      try exact (hne rfl).elim
    all_goals
      first
      | refine ⟨(0 : Fin 3), ?_⟩
        simpa [transitionSupportGraph,
          twoQubitEndpointTransition_ne_zero_iff,
          twoQubitEndpointFlip]
      | refine ⟨(1 : Fin 3), ?_⟩
        simpa [transitionSupportGraph,
          twoQubitEndpointTransition_ne_zero_iff,
          twoQubitEndpointFlip]
      | refine ⟨(2 : Fin 3), ?_⟩
        simpa [transitionSupportGraph,
          twoQubitEndpointTransition_ne_zero_iff,
          twoQubitEndpointFlip]

/-- Explicit physically realized two-qubit edge seed. -/
theorem exists_physicallyRealized_twoQubitGraphSeed :
    ∃ Z : PhysicallyRealizedGoodObserverSpectralSystem.{0},
      Z.spectral.stateCard = 4 ∧
      Z.spectral.observerCard = 2 := by
  obtain ⟨energy, henergyMaximal, _⟩ :=
    exists_maximallyProjectiveEnergy_close_fintype
      (fun _ : Bool × Bool => 0) 1 (by norm_num)
  have hgood :
      HermitianObserverFamilyGood
        twoQubitEndpointTransition := by
    intro s
    refine ⟨?_, ?_, ?_⟩
    · intro q
      exact twoQubitEndpointTransition_isHermitian s q
    · rw [transitionFamilySupportGraph_twoQubitEndpointTransition]
      exact SimpleGraph.preconnected_top
    · rw [transitionFamilySupportGraph_twoQubitEndpointTransition]
      exact completeGraph_not_isBipartite_of_three_le_card
        (I := Bool × Bool) (by norm_num)
  let X : GoodObserverSpectralSystem.{0} :=
    { State := Bool × Bool
      Observer := Bool
      Probe := fun _ => Fin 3
      stateFintype := inferInstance
      stateDecidableEq := inferInstance
      stateNonempty := inferInstance
      stateNontrivial := inferInstance
      observerFintype := inferInstance
      observerDecidableEq := inferInstance
      observerNonempty := inferInstance
      probeFintype := fun _ => inferInstance
      probeDecidableEq := fun _ => inferInstance
      energy := energy
      energy_maximallyProjective := henergyMaximal
      transition := twoQubitEndpointTransition
      observerFamily_good := hgood }
  let hamiltonian :
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    twoQubitGraphBasis *
      Matrix.diagonal (fun i => (energy i : ℂ)) *
      twoQubitGraphBasisᴴ
  let R :
      @GoodObserverSpectralSystem.PhysicalRealization
        X X.stateFintype X.stateDecidableEq :=
    { PhysicalState := Bool × Bool
      physicalFintype := inferInstance
      physicalDecidableEq := inferInstance
      basis := twoQubitGraphBasis
      star_basis_mul_basis :=
        twoQubitGraphBasis_conjTranspose_mul_self
      basis_mul_star_basis :=
        twoQubitGraphBasis_mul_conjTranspose_self
      hamiltonian := hamiltonian
      hamiltonian_eq_diagonal := rfl
      physicalProbe := twoQubitEndpointProbe
      transition_eq_coordinate := by
        intro s q
        rfl }
  exact ⟨⟨X, R⟩, by simp [X,
    GoodObserverSpectralSystem.stateCard],
    by simp [X, GoodObserverSpectralSystem.observerCard]⟩

end

end GaloisForLFunctions.HTGeometry
