import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-!
# Component-histogram law for completed quantum recurrence

For any finite joint spectral label set whose total energy is a sum of
component energies, mutual projective independence of the component energy
families makes an equal-total-energy replica collision equivalent to equality
of every component histogram. Combined with the finite-spectrum time-average
identity, this classifies all completed survival-fidelity moments.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Energy obtained by summing component energies along supplied coordinates. -/
def factorizedEnergyOn
    {C X : Type*} [Fintype C]
    {I : C → Type*}
    (coordinate : ∀ c, X → I c)
    (energy : ∀ c, I c → ℝ)
    (x : X) : ℝ :=
  ∑ c, energy c (coordinate c x)

/-- Component histogram induced by a replica multiplicity vector. -/
def componentReplicaMultiplicityOn
    {C X : Type*} [Fintype X]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (coordinate : ∀ c, X → I c)
    (p : X → ℕ) (c : C) (i : I c) : ℕ :=
  ∑ x, if coordinate c x = i then p x else 0

/-- Every balanced rational relation among all component energies is
componentwise trivial. This combines maximal projective rank inside each
component with rational transversality between component gap modules. -/
def ComponentProjectivelyIndependent
    {C : Type*} [Fintype C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ) : Prop :=
  ∀ k : ∀ c, I c → ℤ,
    (∀ c, ∑ i, k c i = 0) →
    (∑ c, ∑ i, (k c i : ℝ) * energy c i) = 0 →
    ∀ c, k c = 0

/-- Regrouping a replica energy sum by one component coordinate. -/
theorem sum_replica_factorized_componentOn
    {C X : Type*} [Fintype X]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (coordinate : ∀ c, X → I c)
    (energy : ∀ c, I c → ℝ)
    (p : X → ℕ) (c : C) :
    (∑ x, (p x : ℝ) * energy c (coordinate c x)) =
      ∑ i, (componentReplicaMultiplicityOn coordinate p c i : ℝ) *
        energy c i := by
  classical
  unfold componentReplicaMultiplicityOn
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

/-- A factorized total replica energy is the component-histogram pairing
with the component energy families. -/
theorem replicaMultiplicityEnergy_factorizedOn
    {C X : Type*} [Fintype C] [Fintype X]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (coordinate : ∀ c, X → I c)
    (energy : ∀ c, I c → ℝ)
    (p : X → ℕ) :
    replicaMultiplicityEnergy (factorizedEnergyOn coordinate energy) p =
      ∑ c, ∑ i,
        (componentReplicaMultiplicityOn coordinate p c i : ℝ) *
          energy c i := by
  classical
  unfold replicaMultiplicityEnergy factorizedEnergyOn
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  exact sum_replica_factorized_componentOn coordinate energy p c

/-- Every component histogram has the total replica mass. -/
theorem sum_componentReplicaMultiplicityOn_eq
    {C X : Type*} [Fintype X] [DecidableEq X]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (coordinate : ∀ c, X → I c)
    {p : X → ℕ} {n : ℕ}
    (hp : p ∈ Finset.univ.piAntidiag n) (c : C) :
    ∑ i, componentReplicaMultiplicityOn coordinate p c i = n := by
  classical
  unfold componentReplicaMultiplicityOn
  rw [Finset.sum_comm]
  simpa using (Finset.mem_piAntidiag.mp hp).1

/-- **Component collision equivalence.** Under mutual projective
independence, two equal-mass replica packets have equal total energy exactly
when every component sees the same histogram. -/
theorem factorizedOn_replica_energy_eq_iff_componentMultiplicity_eq
    {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (coordinate : ∀ c, X → I c)
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    {p q : X → ℕ} {n : ℕ}
    (hp : p ∈ Finset.univ.piAntidiag n)
    (hq : q ∈ Finset.univ.piAntidiag n) :
    replicaMultiplicityEnergy
          (factorizedEnergyOn coordinate energy) p =
        replicaMultiplicityEnergy
          (factorizedEnergyOn coordinate energy) q ↔
      ∀ c i,
        componentReplicaMultiplicityOn coordinate p c i =
          componentReplicaMultiplicityOn coordinate q c i := by
  classical
  constructor
  · intro heq
    let k : ∀ c, I c → ℤ :=
      fun c i =>
        (componentReplicaMultiplicityOn coordinate p c i : ℤ) -
          (componentReplicaMultiplicityOn coordinate q c i : ℤ)
    have hbalanced : ∀ c, ∑ i, k c i = 0 := by
      intro c
      unfold k
      rw [Finset.sum_sub_distrib]
      have hpSum :=
        sum_componentReplicaMultiplicityOn_eq coordinate hp c
      have hqSum :=
        sum_componentReplicaMultiplicityOn_eq coordinate hq c
      have hpSumZ :
          ∑ i,
              (componentReplicaMultiplicityOn coordinate p c i : ℤ) =
            (n : ℤ) := by
        exact_mod_cast hpSum
      have hqSumZ :
          ∑ i,
              (componentReplicaMultiplicityOn coordinate q c i : ℤ) =
            (n : ℤ) := by
        exact_mod_cast hqSum
      rw [hpSumZ, hqSumZ, sub_self]
    have henergy :
        (∑ c, ∑ i, (k c i : ℝ) * energy c i) = 0 := by
      rw [replicaMultiplicityEnergy_factorizedOn
          coordinate energy p,
        replicaMultiplicityEnergy_factorizedOn
          coordinate energy q] at heq
      calc
        (∑ c, ∑ i, (k c i : ℝ) * energy c i) =
            (∑ c, ∑ i,
              (componentReplicaMultiplicityOn coordinate p c i : ℝ) *
                energy c i) -
              (∑ c, ∑ i,
                (componentReplicaMultiplicityOn coordinate q c i : ℝ) *
                  energy c i) := by
            unfold k
            push_cast
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro c hc
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
        _ = 0 := sub_eq_zero.mpr heq
    have hk := hindependent k hbalanced henergy
    intro c i
    have hki := congrFun (hk c) i
    change
      (componentReplicaMultiplicityOn coordinate p c i : ℤ) -
          (componentReplicaMultiplicityOn coordinate q c i : ℤ) = 0 at hki
    omega
  · intro hhist
    rw [replicaMultiplicityEnergy_factorizedOn coordinate energy p,
      replicaMultiplicityEnergy_factorizedOn coordinate energy q]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro i hi
    rw [hhist c i]

/-- Weighted mass of all and only joint component-histogram collisions. -/
def fidelityReplicaComponentCollisionMassOn
    {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (coordinate : ∀ c, X → I c)
    (weight : X → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      if ∀ c i,
          componentReplicaMultiplicityOn coordinate p c i =
            componentReplicaMultiplicityOn coordinate q c i
      then fidelityReplicaMultiplicityWeight weight p q
      else 0

/-- The ordinary replica collision mass of a factorized energy is exactly
the component-histogram collision mass. -/
theorem fidelityReplicaCollisionMass_factorizedOn_eq_componentCollisionMass
    {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (coordinate : ∀ c, X → I c)
    (weight : X → ℝ)
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (n : ℕ) :
    fidelityReplicaCollisionMass
        weight (factorizedEnergyOn coordinate energy) n =
      fidelityReplicaComponentCollisionMassOn coordinate weight n := by
  classical
  rw [← fidelityReplicaResonantMass_eq_collisionMass]
  unfold fidelityReplicaResonantMass
    fidelityReplicaComponentCollisionMassOn
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply if_congr
  · exact
      factorizedOn_replica_energy_eq_iff_componentMultiplicity_eq
        coordinate energy hindependent hp hq
  · rfl
  · rfl

/-- **Completed component-histogram law.** Every long-time
survival-fidelity moment of a component-factorized finite spectrum converges
to the mass of equal component histograms. -/
theorem
    finiteSpectralSurvivalFidelityMean_factorizedOn_tendsto_componentCollisionMass
    {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (coordinate : ∀ c, X → I c)
    (weight : X → ℝ)
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (n : ℕ) :
    Filter.Tendsto
      (finiteSpectralSurvivalFidelityMean
        weight (factorizedEnergyOn coordinate energy) n)
      Filter.atTop
      (nhds
        (fidelityReplicaComponentCollisionMassOn
          coordinate weight n : ℂ)) := by
  rw [←
    fidelityReplicaCollisionMass_factorizedOn_eq_componentCollisionMass
      coordinate weight energy hindependent n]
  exact finiteSpectralSurvivalFidelityMean_tendsto_collisionMass
    weight (factorizedEnergyOn coordinate energy) n

end

end GaloisForLFunctions.HTGeometry
