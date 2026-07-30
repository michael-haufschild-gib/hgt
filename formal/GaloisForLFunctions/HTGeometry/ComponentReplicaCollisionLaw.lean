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

/-! ## Order-two recurrence tomography of component product geometry -/

/-- Components on which two joint spectral labels differ. -/
abbrev DifferingComponent
    {C : Type*} {I : C → Type*}
    (x y : ∀ c, I c) :=
  {c : C // x c ≠ y c}

/-- First label obtained by independently choosing an orientation on every
component where `x` and `y` differ. -/
def componentRecombineFirst
    {C : Type*} {I : C → Type*}
    [∀ c, DecidableEq (I c)]
    (x y : ∀ c, I c)
    (switch : DifferingComponent x y → Bool) :
    ∀ c, I c :=
  fun c =>
    if h : x c = y c then x c
    else if switch ⟨c, h⟩ = true then x c else y c

/-- Complementary label obtained from the opposite orientation. -/
def componentRecombineSecond
    {C : Type*} {I : C → Type*}
    [∀ c, DecidableEq (I c)]
    (x y : ∀ c, I c)
    (switch : DifferingComponent x y → Bool) :
    ∀ c, I c :=
  fun c =>
    if h : x c = y c then y c
    else if switch ⟨c, h⟩ = true then y c else x c

/-- An ordered pair is a componentwise recombination of `(x,y)` when every
coordinate is either unchanged or swapped. -/
def IsComponentwiseRecombination
    {C : Type*} {I : C → Type*}
    (x y : ∀ c, I c)
    (zw : (∀ c, I c) × (∀ c, I c)) : Prop :=
  ∀ c,
    (zw.1 c = x c ∧ zw.2 c = y c) ∨
      (zw.1 c = y c ∧ zw.2 c = x c)

instance isComponentwiseRecombinationDecidable
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, DecidableEq (I c)]
    (x y : ∀ c, I c)
    (zw : (∀ c, I c) × (∀ c, I c)) :
    Decidable (IsComponentwiseRecombination x y zw) := by
  unfold IsComponentwiseRecombination
  infer_instance

/-- Independent component switches always produce a componentwise
recombination. -/
def componentRecombinationForward
    {C : Type*} {I : C → Type*}
    [∀ c, DecidableEq (I c)]
    (x y : ∀ c, I c)
    (switch : DifferingComponent x y → Bool) :
    {zw : (∀ c, I c) × (∀ c, I c) //
      IsComponentwiseRecombination x y zw} :=
  ⟨(componentRecombineFirst x y switch,
      componentRecombineSecond x y switch), by
    intro c
    by_cases hxy : x c = y c
    · left
      simp [componentRecombineFirst, componentRecombineSecond, hxy]
    · by_cases hs : switch ⟨c, hxy⟩ = true
      · left
        simp [componentRecombineFirst, componentRecombineSecond, hxy, hs]
      · right
        simp [componentRecombineFirst, componentRecombineSecond, hxy, hs]⟩

/-- Recover the switch orientation from a componentwise recombination. -/
def componentRecombinationSwitch
    {C : Type*} {I : C → Type*}
    [∀ c, DecidableEq (I c)]
    (x y : ∀ c, I c)
    (zw : {zw : (∀ c, I c) × (∀ c, I c) //
      IsComponentwiseRecombination x y zw}) :
    DifferingComponent x y → Bool :=
  fun c => decide (zw.1.1 c.1 = x c.1)

theorem componentRecombinationSwitch_forward
    {C : Type*} {I : C → Type*}
    [∀ c, DecidableEq (I c)]
    (x y : ∀ c, I c)
    (switch : DifferingComponent x y → Bool) :
    componentRecombinationSwitch x y
        (componentRecombinationForward x y switch) =
      switch := by
  funext c
  cases hs : switch c
  · have hyx : y c.1 ≠ x c.1 := fun h => c.2 h.symm
    simp [componentRecombinationSwitch, componentRecombinationForward,
      componentRecombineFirst, c.2, hyx, hs]
  · simp [componentRecombinationSwitch, componentRecombinationForward,
      componentRecombineFirst, c.2, hs]

theorem componentRecombinationForward_switch
    {C : Type*} {I : C → Type*}
    [∀ c, DecidableEq (I c)]
    (x y : ∀ c, I c)
    (zw : {zw : (∀ c, I c) × (∀ c, I c) //
      IsComponentwiseRecombination x y zw}) :
    componentRecombinationForward x y
        (componentRecombinationSwitch x y zw) =
      zw := by
  apply Subtype.ext
  apply Prod.ext
  · funext c
    have hc := zw.2 c
    by_cases hxy : x c = y c
    · rcases hc with hc | hc
      · simp [componentRecombinationForward, componentRecombineFirst,
          hxy, hc.1]
      · simp [componentRecombinationForward, componentRecombineFirst,
          hxy, hc.1]
    · rcases hc with hc | hc
      · simp [componentRecombinationForward, componentRecombineFirst,
          componentRecombinationSwitch, hxy, hc.1]
      · have hyx : y c ≠ x c := fun h => hxy h.symm
        simp [componentRecombinationForward, componentRecombineFirst,
          componentRecombinationSwitch, hxy, hc.1, hyx]
  · funext c
    have hc := zw.2 c
    by_cases hxy : x c = y c
    · rcases hc with hc | hc
      · simp [componentRecombinationForward, componentRecombineSecond,
          hxy, hc.2]
      · simp [componentRecombinationForward, componentRecombineSecond,
          hxy, hc.2]
    · rcases hc with hc | hc
      · simp [componentRecombinationForward, componentRecombineSecond,
          componentRecombinationSwitch, hxy, hc.1, hc.2]
      · have hyx : y c ≠ x c := fun h => hxy h.symm
        simp [componentRecombinationForward, componentRecombineSecond,
          componentRecombinationSwitch, hxy, hc.1, hc.2, hyx]

/-- **Boolean-cube recombination law.** Order-two component-histogram
collision partners are exactly independent switches on the components where
the original pair differs. -/
def componentRecombinationEquiv
    {C : Type*} {I : C → Type*}
    [∀ c, DecidableEq (I c)]
    (x y : ∀ c, I c) :
    (DifferingComponent x y → Bool) ≃
      {zw : (∀ c, I c) × (∀ c, I c) //
        IsComponentwiseRecombination x y zw} where
  toFun := componentRecombinationForward x y
  invFun := componentRecombinationSwitch x y
  left_inv := componentRecombinationSwitch_forward x y
  right_inv := componentRecombinationForward_switch x y

/-- Hamming distance in the component-product spectral label space. -/
def componentHammingDistance
    {C : Type*} [Fintype C] {I : C → Type*}
    (x y : ∀ c, I c) : ℕ :=
  by
    classical
    exact Fintype.card (DifferingComponent x y)

noncomputable instance componentwiseRecombinationFintype
    {C : Type*} [Fintype C] {I : C → Type*}
    [∀ c, Fintype (I c)]
    (x y : ∀ c, I c) :
    Fintype
      {zw : (∀ c, I c) × (∀ c, I c) //
        IsComponentwiseRecombination x y zw} :=
  Fintype.ofFinite _

/-- **Exponential Hamming tomography law.** The exact number of ordered
order-two recombinations is `2` raised to the component Hamming distance. -/
theorem card_componentwiseRecombination
    {C : Type*} [Fintype C] {I : C → Type*}
    [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
    (x y : ∀ c, I c) :
    Fintype.card
        {zw : (∀ c, I c) × (∀ c, I c) //
          IsComponentwiseRecombination x y zw} =
      2 ^ componentHammingDistance x y := by
  classical
  letI : Fintype (DifferingComponent x y) := Fintype.ofFinite _
  letI : Fintype
      {zw : (∀ c, I c) × (∀ c, I c) //
        IsComponentwiseRecombination x y zw} :=
    Fintype.ofFinite _
  calc
    Fintype.card
        {zw : (∀ c, I c) × (∀ c, I c) //
          IsComponentwiseRecombination x y zw} =
        Fintype.card (DifferingComponent x y → Bool) :=
      (Fintype.card_congr (componentRecombinationEquiv x y)).symm
    _ = 2 ^ componentHammingDistance x y := by
      simp [componentHammingDistance]

/-- Multiplicity of a label in an ordered two-point packet. -/
def twoPointMultiplicity
    {A : Type*} [DecidableEq A]
    (x y i : A) : ℕ :=
  (if x = i then 1 else 0) + (if y = i then 1 else 0)

/-- Equality of all two-point multiplicities means that the ordered pair is
either unchanged or swapped. -/
theorem twoPointMultiplicity_eq_iff_swap
    {A : Type*} [DecidableEq A]
    (x y z w : A) :
    (∀ i, twoPointMultiplicity z w i =
        twoPointMultiplicity x y i) ↔
      (z = x ∧ w = y) ∨ (z = y ∧ w = x) := by
  constructor
  · intro h
    by_cases hzx : z = x
    · left
      refine ⟨hzx, ?_⟩
      subst z
      by_cases hwx : w = x
      · subst w
        by_cases hyx : y = x
        · exact hyx.symm
        · have hx := h x
          simp [twoPointMultiplicity, hyx] at hx
      · by_cases hyw : y = w
        · exact hyw.symm
        · have hw := h w
          have hxw : x ≠ w := fun h => hwx h.symm
          simp [twoPointMultiplicity, hxw, hyw] at hw
    · right
      have hz := h z
      have hzy : z = y := by
        by_cases hyz : y = z
        · exact hyz.symm
        · have hxz : x ≠ z := fun h => hzx h.symm
          simp [twoPointMultiplicity, hxz, hyz] at hz
      refine ⟨hzy, ?_⟩
      subst y
      by_cases hwx : w = x
      · exact hwx
      · have hx := h x
        simp [twoPointMultiplicity, hzx, hwx] at hx
  · rintro (h | h)
    · rcases h with ⟨rfl, rfl⟩
      intro i
      rfl
    · rcases h with ⟨rfl, rfl⟩
      intro i
      simp [twoPointMultiplicity, add_comm]

private theorem sum_twoPointMultiplicity_mul
    {A : Type*} [Fintype A] [DecidableEq A]
    (energy : A → ℝ) (x y : A) :
    (∑ i, (twoPointMultiplicity x y i : ℝ) * energy i) =
      energy x + energy y := by
  unfold twoPointMultiplicity
  push_cast
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp

/-- Every componentwise recombination preserves the two-copy total energy
for every additive component spectrum, without any independence premise. -/
theorem componentwiseRecombination_factorizedPairEnergy_eq
    {C : Type*} [Fintype C]
    {I : C → Type*}
    (energy : ∀ c, I c → ℝ)
    (x y z w : ∀ c, I c)
    (hrec : IsComponentwiseRecombination x y (z, w)) :
    factorizedEnergyOn (fun c u => u c) energy z +
          factorizedEnergyOn (fun c u => u c) energy w =
        factorizedEnergyOn (fun c u => u c) energy x +
          factorizedEnergyOn (fun c u => u c) energy y := by
  unfold factorizedEnergyOn
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rcases hrec c with h | h
  · change z c = x c ∧ w c = y c at h
    change
      energy c (z c) + energy c (w c) =
        energy c (x c) + energy c (y c)
    rw [h.1, h.2]
  · change z c = y c ∧ w c = x c at h
    change
      energy c (z c) + energy c (w c) =
        energy c (x c) + energy c (y c)
    rw [h.1, h.2, add_comm]

/-- **Spectral collision/recombination equivalence.** Under mutual
projective independence of the component spectra, an order-two equality of
total energies occurs exactly by independently swapping component labels. -/
theorem factorizedPairEnergy_eq_iff_componentwiseRecombination
    {C : Type*} [Fintype C]
    {I : C → Type*}
    [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (x y z w : ∀ c, I c) :
    factorizedEnergyOn (fun c u => u c) energy z +
          factorizedEnergyOn (fun c u => u c) energy w =
        factorizedEnergyOn (fun c u => u c) energy x +
          factorizedEnergyOn (fun c u => u c) energy y ↔
      IsComponentwiseRecombination x y (z, w) := by
  classical
  constructor
  · intro heq
    let k : ∀ c, I c → ℤ :=
      fun c i =>
        (twoPointMultiplicity (z c) (w c) i : ℤ) -
          (twoPointMultiplicity (x c) (y c) i : ℤ)
    have hbalanced : ∀ c, ∑ i, k c i = 0 := by
      intro c
      unfold k twoPointMultiplicity
      push_cast
      rw [Finset.sum_sub_distrib]
      simp_rw [Finset.sum_add_distrib]
      simp
    have henergy :
        (∑ c, ∑ i, (k c i : ℝ) * energy c i) = 0 := by
      unfold k
      push_cast
      calc
        (∑ c, ∑ i,
          ((twoPointMultiplicity (z c) (w c) i : ℝ) -
            (twoPointMultiplicity (x c) (y c) i : ℝ)) * energy c i) =
            (∑ c, ∑ i,
              (twoPointMultiplicity (z c) (w c) i : ℝ) * energy c i) -
            (∑ c, ∑ i,
              (twoPointMultiplicity (x c) (y c) i : ℝ) * energy c i) := by
                simp_rw [sub_mul, Finset.sum_sub_distrib]
        _ = (∑ c, (energy c (z c) + energy c (w c))) -
            (∑ c, (energy c (x c) + energy c (y c))) := by
              simp_rw [sum_twoPointMultiplicity_mul]
        _ = 0 := by
          unfold factorizedEnergyOn at heq
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          exact sub_eq_zero.mpr heq
    have hk := hindependent k hbalanced henergy
    intro c
    apply
      (twoPointMultiplicity_eq_iff_swap
        (x c) (y c) (z c) (w c)).mp
    intro i
    have hki := congrFun (hk c) i
    change
      (twoPointMultiplicity (z c) (w c) i : ℤ) -
          (twoPointMultiplicity (x c) (y c) i : ℤ) = 0 at hki
    omega
  · intro hrec
    exact
      componentwiseRecombination_factorizedPairEnergy_eq
        energy x y z w hrec

/-- **Pair-resolved recurrence kernel.** The centered time average of every
two-copy spectral matrix element converges to the indicator of independent
component recombination. -/
theorem factorizedPairPhaseAverage_tendsto_recombinationIndicator
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*}
    [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (x y z w : ∀ c, I c) :
    Filter.Tendsto
      (fun T =>
        symmetricPhaseAverage T
          ((factorizedEnergyOn (fun c u => u c) energy z +
              factorizedEnergyOn (fun c u => u c) energy w) -
            (factorizedEnergyOn (fun c u => u c) energy x +
              factorizedEnergyOn (fun c u => u c) energy y)))
      Filter.atTop
      (nhds
        (if IsComponentwiseRecombination x y (z, w)
          then (1 : ℂ) else 0)) := by
  classical
  have hzero :
      (factorizedEnergyOn (fun c u => u c) energy z +
            factorizedEnergyOn (fun c u => u c) energy w) -
          (factorizedEnergyOn (fun c u => u c) energy x +
            factorizedEnergyOn (fun c u => u c) energy y) = 0 ↔
        IsComponentwiseRecombination x y (z, w) := by
    rw [sub_eq_zero]
    exact
      factorizedPairEnergy_eq_iff_componentwiseRecombination
        energy hindependent x y z w
  simpa only [hzero] using
    symmetricPhaseAverage_tendsto_resonanceIndicator
      ((factorizedEnergyOn (fun c u => u c) energy z +
          factorizedEnergyOn (fun c u => u c) energy w) -
        (factorizedEnergyOn (fun c u => u c) energy x +
          factorizedEnergyOn (fun c u => u c) energy y))

/-- The order-two equal-energy collision class is equivalent to the Boolean
cube of independent component switches. -/
def factorizedPairEnergyCollisionEquiv
    {C : Type*} [Fintype C]
    {I : C → Type*}
    [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (x y : ∀ c, I c) :
    {zw : (∀ c, I c) × (∀ c, I c) //
      factorizedEnergyOn (fun c u => u c) energy zw.1 +
            factorizedEnergyOn (fun c u => u c) energy zw.2 =
          factorizedEnergyOn (fun c u => u c) energy x +
            factorizedEnergyOn (fun c u => u c) energy y} ≃
      {zw : (∀ c, I c) × (∀ c, I c) //
        IsComponentwiseRecombination x y zw} :=
  Equiv.subtypeEquiv (Equiv.refl _) fun zw =>
    factorizedPairEnergy_eq_iff_componentwiseRecombination
      energy hindependent x y zw.1 zw.2

noncomputable instance factorizedPairEnergyCollisionFintype
    {C : Type*} [Fintype C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (x y : ∀ c, I c) :
    Fintype
      {zw : (∀ c, I c) × (∀ c, I c) //
        factorizedEnergyOn (fun c u => u c) energy zw.1 +
              factorizedEnergyOn (fun c u => u c) energy zw.2 =
            factorizedEnergyOn (fun c u => u c) energy x +
              factorizedEnergyOn (fun c u => u c) energy y} :=
  Fintype.ofFinite _

/-- The Boolean component-switch cube embeds into the exact two-copy energy
collision class for every additive component spectrum. -/
def componentSwitchEmbedding_pairEnergyCollision
    {C : Type*} [Fintype C]
    {I : C → Type*} [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (x y : ∀ c, I c) :
    (DifferingComponent x y → Bool) ↪
      {zw : (∀ c, I c) × (∀ c, I c) //
        factorizedEnergyOn (fun c u => u c) energy zw.1 +
              factorizedEnergyOn (fun c u => u c) energy zw.2 =
            factorizedEnergyOn (fun c u => u c) energy x +
              factorizedEnergyOn (fun c u => u c) energy y} where
  toFun switch :=
    ⟨(componentRecombineFirst x y switch,
        componentRecombineSecond x y switch),
      componentwiseRecombination_factorizedPairEnergy_eq
        energy x y
        (componentRecombineFirst x y switch)
        (componentRecombineSecond x y switch)
        (componentRecombinationForward x y switch).2⟩
  inj' := by
    intro a b hab
    have hpairs :
        (componentRecombineFirst x y a,
            componentRecombineSecond x y a) =
          (componentRecombineFirst x y b,
            componentRecombineSecond x y b) :=
      congrArg Subtype.val hab
    have hsub :
        componentRecombinationForward x y a =
          componentRecombinationForward x y b :=
      Subtype.ext hpairs
    calc
      a = componentRecombinationSwitch x y
          (componentRecombinationForward x y a) :=
        (componentRecombinationSwitch_forward x y a).symm
      _ = componentRecombinationSwitch x y
          (componentRecombinationForward x y b) :=
        congrArg (componentRecombinationSwitch x y) hsub
      _ = b :=
        componentRecombinationSwitch_forward x y b

/-- **Universal collision-cube lower bound.** Every additive component
factorization forces at least `2 ^ d_H(x,y)` ordered equal-energy two-copy
pairs. Additional resonances may enlarge this class but cannot remove the
factorization cube. -/
theorem two_pow_componentHammingDistance_le_card_pairEnergyCollision
    {C : Type*} [Fintype C]
    {I : C → Type*}
    [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (x y : ∀ c, I c) :
    2 ^ componentHammingDistance x y ≤
      Fintype.card
        {zw : (∀ c, I c) × (∀ c, I c) //
          factorizedEnergyOn (fun c u => u c) energy zw.1 +
                factorizedEnergyOn (fun c u => u c) energy zw.2 =
              factorizedEnergyOn (fun c u => u c) energy x +
                factorizedEnergyOn (fun c u => u c) energy y} := by
  classical
  calc
    2 ^ componentHammingDistance x y =
        Fintype.card (DifferingComponent x y → Bool) := by
      simp [componentHammingDistance]
    _ ≤ Fintype.card
        {zw : (∀ c, I c) × (∀ c, I c) //
          factorizedEnergyOn (fun c u => u c) energy zw.1 +
                factorizedEnergyOn (fun c u => u c) energy zw.2 =
              factorizedEnergyOn (fun c u => u c) energy x +
                factorizedEnergyOn (fun c u => u c) energy y} :=
      Fintype.card_le_of_injective
        (componentSwitchEmbedding_pairEnergyCollision energy x y)
        (componentSwitchEmbedding_pairEnergyCollision energy x y).injective

/-- **Order-two spectral Hamming law.** Under component projective
independence, the number of ordered joint spectral pairs with the same
two-copy total energy as `(x,y)` is exactly `2` to their component Hamming
distance. -/
theorem card_factorizedPairEnergyCollision
    {C : Type*} [Fintype C]
    {I : C → Type*}
    [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (x y : ∀ c, I c) :
    Fintype.card
        {zw : (∀ c, I c) × (∀ c, I c) //
          factorizedEnergyOn (fun c u => u c) energy zw.1 +
                factorizedEnergyOn (fun c u => u c) energy zw.2 =
              factorizedEnergyOn (fun c u => u c) energy x +
                factorizedEnergyOn (fun c u => u c) energy y} =
      2 ^ componentHammingDistance x y := by
  calc
    Fintype.card
        {zw : (∀ c, I c) × (∀ c, I c) //
          factorizedEnergyOn (fun c u => u c) energy zw.1 +
                factorizedEnergyOn (fun c u => u c) energy zw.2 =
              factorizedEnergyOn (fun c u => u c) energy x +
                factorizedEnergyOn (fun c u => u c) energy y} =
        Fintype.card
          {zw : (∀ c, I c) × (∀ c, I c) //
            IsComponentwiseRecombination x y zw} :=
      Fintype.card_congr
        (factorizedPairEnergyCollisionEquiv
          energy hindependent x y)
    _ = 2 ^ componentHammingDistance x y :=
      card_componentwiseRecombination x y

end

end GaloisForLFunctions.HTGeometry
