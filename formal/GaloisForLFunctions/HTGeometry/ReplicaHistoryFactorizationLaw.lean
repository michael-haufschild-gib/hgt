import GaloisForLFunctions.HTGeometry.ComponentReplicaCollisionLaw

/-!
# Replica-history factorization law

For an additive finite spectrum, every independent rearrangement of each
component history preserves total replica energy. Under mutual projective
independence, these are all equal-energy histories. Consequently the exact
collision class is a Cartesian product of the component arrangement classes
at every finite replica order.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Number of occurrences of one symbol in a finite indexed history. -/
def historyMultiplicity
    {R A : Type*} [Fintype R] [DecidableEq A]
    (x : R → A) (a : A) : ℕ :=
  ∑ r, if x r = a then 1 else 0

/-- Two finite histories are rearrangements when they have the same
histogram. -/
def IsHistoryRearrangement
    {R A : Type*} [Fintype R] [DecidableEq A]
    (x y : R → A) : Prop :=
  ∀ a, historyMultiplicity x a = historyMultiplicity y a

/-- A joint history is a componentwise rearrangement of another when every
component retains its own histogram. -/
def IsComponentHistoryRearrangement
    {C R : Type*} [Fintype R]
    {I : C → Type*} [∀ c, DecidableEq (I c)]
    (x y : R → ∀ c, I c) : Prop :=
  ∀ c, IsHistoryRearrangement (fun r => x r c) (fun r => y r c)

/-- Arrangement class of one finite history. -/
def HistoryArrangement
    {R A : Type*} [Fintype R] [DecidableEq A]
    (x : R → A) : Type _ :=
  {y : R → A // IsHistoryRearrangement x y}

/-- Joint histories obtained by independently rearranging every component. -/
def ComponentHistoryArrangement
    {C R : Type*} [Fintype R]
    {I : C → Type*} [∀ c, DecidableEq (I c)]
    (x : R → ∀ c, I c) : Type _ :=
  {y : R → ∀ c, I c // IsComponentHistoryRearrangement x y}

/-- Finite arrangement space of one finite history. -/
noncomputable instance historyArrangementFintype
    {R A : Type*} [Fintype R] [Fintype A] [DecidableEq A]
    (x : R → A) :
    Fintype (HistoryArrangement x) := by
  classical
  exact
    Fintype.subtype
      (Finset.univ.filter (fun y => IsHistoryRearrangement x y))
      (fun y => by simp)

/-- Every history belongs to its own arrangement class. -/
instance historyArrangementNonempty
    {R A : Type*} [Fintype R] [DecidableEq A]
    (x : R → A) :
    Nonempty (HistoryArrangement x) :=
  ⟨⟨x, fun _ => rfl⟩⟩

/-- Finite joint component-arrangement space. -/
noncomputable instance componentHistoryArrangementFintype
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (x : R → ∀ c, I c) :
    Fintype (ComponentHistoryArrangement x) := by
  classical
  exact
    Fintype.subtype
      (Finset.univ.filter (fun y =>
        IsComponentHistoryRearrangement x y))
      (fun y => by simp)

/-- Every joint history belongs to its own component-arrangement class. -/
instance componentHistoryArrangementNonempty
    {C R : Type*} [Fintype R]
    {I : C → Type*} [∀ c, DecidableEq (I c)]
    (x : R → ∀ c, I c) :
    Nonempty (ComponentHistoryArrangement x) :=
  ⟨⟨x, fun _ _ => rfl⟩⟩

/-- Currying identifies the joint component-rearrangement class with the
Cartesian product of the individual component arrangement classes. -/
def componentHistoryArrangementEquiv
    {C R : Type*} [Fintype R]
    {I : C → Type*} [∀ c, DecidableEq (I c)]
    (x : R → ∀ c, I c) :
    ComponentHistoryArrangement x ≃
      (∀ c, HistoryArrangement (fun r => x r c)) where
  toFun y := fun c => ⟨fun r => y.1 r c, y.2 c⟩
  invFun family :=
    ⟨fun r c => (family c).1 r, fun c => (family c).2⟩
  left_inv y := by
    apply Subtype.ext
    funext r c
    rfl
  right_inv family := by
    funext c
    apply Subtype.ext
    funext r
    rfl

/-- Exact product law for the number of independent component-history
arrangements. -/
theorem card_componentHistoryArrangement
    {C R : Type*} [Fintype C] [DecidableEq C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (x : R → ∀ c, I c) :
    Fintype.card (ComponentHistoryArrangement x) =
      ∏ c, Fintype.card (HistoryArrangement (fun r => x r c)) := by
  classical
  rw [Fintype.card_congr (componentHistoryArrangementEquiv x),
    Fintype.card_pi]

/-- The entries of a history histogram sum to the history length. -/
theorem sum_historyMultiplicity_eq_card
    {R A : Type*} [Fintype R] [Fintype A] [DecidableEq A]
    (x : R → A) :
    ∑ a, historyMultiplicity x a = Fintype.card R := by
  classical
  unfold historyMultiplicity
  rw [Finset.sum_comm]
  simp

/-- A finite energy sum is its histogram paired with the energy family. -/
theorem sum_history_energy_eq_histogram
    {R A : Type*} [Fintype R] [Fintype A] [DecidableEq A]
    (energy : A → ℝ) (x : R → A) :
    (∑ r, energy (x r)) =
      ∑ a, (historyMultiplicity x a : ℝ) * energy a := by
  classical
  unfold historyMultiplicity
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp

/-- Total energy of a finite history in an additive component spectrum. -/
def factorizedHistoryEnergy
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*}
    (energy : ∀ c, I c → ℝ)
    (x : R → ∀ c, I c) : ℝ :=
  ∑ r, ∑ c, energy c (x r c)

/-- A factorized history energy is the pairing of every component histogram
with its component energy family. -/
theorem factorizedHistoryEnergy_eq_histograms
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (x : R → ∀ c, I c) :
    factorizedHistoryEnergy energy x =
      ∑ c, ∑ i,
        (historyMultiplicity (fun r => x r c) i : ℝ) * energy c i := by
  classical
  unfold factorizedHistoryEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  exact sum_history_energy_eq_histogram (energy c) (fun r => x r c)

/-- **Universal inclusion.** Independent component rearrangements preserve
total history energy for every additive component spectrum, with no
independence assumption. -/
theorem componentHistoryRearrangement_factorizedHistoryEnergy_eq
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    {x y : R → ∀ c, I c}
    (hxy : IsComponentHistoryRearrangement x y) :
    factorizedHistoryEnergy energy y =
      factorizedHistoryEnergy energy x := by
  rw [factorizedHistoryEnergy_eq_histograms,
    factorizedHistoryEnergy_eq_histograms]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro i hi
  rw [hxy c i]

/-- **All-order collision classification.** Under mutual projective
independence, equal total history energy is equivalent to independent
rearrangement of each component history. -/
theorem factorizedHistoryEnergy_eq_iff_componentHistoryRearrangement
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (x y : R → ∀ c, I c) :
    factorizedHistoryEnergy energy y =
        factorizedHistoryEnergy energy x ↔
      IsComponentHistoryRearrangement x y := by
  classical
  constructor
  · intro heq
    let k : ∀ c, I c → ℤ :=
      fun c i =>
        (historyMultiplicity (fun r => y r c) i : ℤ) -
          (historyMultiplicity (fun r => x r c) i : ℤ)
    have hbalanced : ∀ c, ∑ i, k c i = 0 := by
      intro c
      unfold k
      rw [Finset.sum_sub_distrib]
      have hy :=
        sum_historyMultiplicity_eq_card (fun r => y r c)
      have hx :=
        sum_historyMultiplicity_eq_card (fun r => x r c)
      have hyZ :
          ∑ i, (historyMultiplicity (fun r => y r c) i : ℤ) =
            (Fintype.card R : ℤ) := by
        exact_mod_cast hy
      have hxZ :
          ∑ i, (historyMultiplicity (fun r => x r c) i : ℤ) =
            (Fintype.card R : ℤ) := by
        exact_mod_cast hx
      rw [hyZ, hxZ, sub_self]
    have henergy :
        (∑ c, ∑ i, (k c i : ℝ) * energy c i) = 0 := by
      rw [factorizedHistoryEnergy_eq_histograms,
        factorizedHistoryEnergy_eq_histograms] at heq
      calc
        (∑ c, ∑ i, (k c i : ℝ) * energy c i) =
            (∑ c, ∑ i,
              (historyMultiplicity (fun r => y r c) i : ℝ) *
                energy c i) -
              (∑ c, ∑ i,
                (historyMultiplicity (fun r => x r c) i : ℝ) *
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
      (historyMultiplicity (fun r => y r c) i : ℤ) -
          (historyMultiplicity (fun r => x r c) i : ℤ) = 0 at hki
    omega
  · intro hxy
    exact
      componentHistoryRearrangement_factorizedHistoryEnergy_eq
        energy hxy

/-- Equal-energy history class through one reference history. -/
def FactorizedHistoryEnergyCollision
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*}
    (energy : ∀ c, I c → ℝ)
    (x : R → ∀ c, I c) : Type _ :=
  {y : R → ∀ c, I c //
    factorizedHistoryEnergy energy y = factorizedHistoryEnergy energy x}

/-- Finite equal-energy history class. -/
noncomputable instance factorizedHistoryEnergyCollisionFintype
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (x : R → ∀ c, I c) :
    Fintype (FactorizedHistoryEnergyCollision energy x) := by
  classical
  exact
    Fintype.subtype
      (Finset.univ.filter (fun y =>
        factorizedHistoryEnergy energy y =
          factorizedHistoryEnergy energy x))
      (fun y => by simp)

/-- Every reference history belongs to its own equal-energy class. -/
instance factorizedHistoryEnergyCollisionNonempty
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*}
    (energy : ∀ c, I c → ℝ)
    (x : R → ∀ c, I c) :
    Nonempty (FactorizedHistoryEnergyCollision energy x) :=
  ⟨⟨x, rfl⟩⟩

/-- Independent component rearrangements embed into the exact energy
collision class for every additive component spectrum. -/
def componentHistoryArrangementEmbedding_energyCollision
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (x : R → ∀ c, I c) :
    ComponentHistoryArrangement x ↪
      FactorizedHistoryEnergyCollision energy x where
  toFun y :=
    ⟨y.1,
      componentHistoryRearrangement_factorizedHistoryEnergy_eq
        energy y.2⟩
  inj' a b hab := by
    apply Subtype.ext
    exact
      congrArg
        (fun z : FactorizedHistoryEnergyCollision energy x => z.1)
        hab

/-- **Universal all-order multiplicity floor.** Every additive factorization
forces at least as many equal-energy histories as there are independent
component rearrangements. Additional resonances can only enlarge the class. -/
theorem card_componentHistoryArrangement_le_card_energyCollision
    {C R : Type*} [Fintype C] [DecidableEq C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (x : R → ∀ c, I c) :
    Fintype.card (ComponentHistoryArrangement x) ≤
      Fintype.card (FactorizedHistoryEnergyCollision energy x) :=
  Fintype.card_le_of_embedding
    (componentHistoryArrangementEmbedding_energyCollision energy x)

/-- Under projective independence, the energy collision class is exactly
the component-rearrangement class. -/
def factorizedHistoryEnergyCollisionEquiv
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (x : R → ∀ c, I c) :
    FactorizedHistoryEnergyCollision energy x ≃
      ComponentHistoryArrangement x where
  toFun y :=
    ⟨y.1,
      (factorizedHistoryEnergy_eq_iff_componentHistoryRearrangement
        energy hindependent x y.1).mp y.2⟩
  invFun y :=
    ⟨y.1,
      componentHistoryRearrangement_factorizedHistoryEnergy_eq
        energy y.2⟩
  left_inv y := by
    apply Subtype.ext
    funext r c
    rfl
  right_inv y := by
    apply Subtype.ext
    funext r c
    rfl

/-- **Replica-history product law.** Under projective independence, the
number of equal-energy joint histories is exactly the product of the
component arrangement counts at every finite history order. -/
theorem card_factorizedHistoryEnergyCollision
    {C R : Type*} [Fintype C] [DecidableEq C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (x : R → ∀ c, I c) :
    Fintype.card (FactorizedHistoryEnergyCollision energy x) =
      ∏ c,
        Fintype.card (HistoryArrangement (fun r => x r c)) := by
  rw [Fintype.card_congr
      (factorizedHistoryEnergyCollisionEquiv energy hindependent x),
    card_componentHistoryArrangement]

/-- Logarithmic size of an exact equal-energy history class. -/
noncomputable def factorizedHistoryCollisionEntropy
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (x : R → ∀ c, I c) : ℝ :=
  Real.log
    (Fintype.card (FactorizedHistoryEnergyCollision energy x) : ℝ)

/-- Sum of the logarithmic arrangement counts of all component histories. -/
noncomputable def componentHistoryArrangementEntropy
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (x : R → ∀ c, I c) : ℝ :=
  ∑ c,
    Real.log
      (Fintype.card (HistoryArrangement (fun r => x r c)) : ℝ)

/-- **Additive recurrence-entropy law.** Under projective independence, the
logarithmic collision multiplicity is exactly extensive across independent
components at every finite history order. -/
theorem factorizedHistoryCollisionEntropy_eq_componentEntropy
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (x : R → ∀ c, I c) :
    factorizedHistoryCollisionEntropy energy x =
      componentHistoryArrangementEntropy x := by
  classical
  unfold factorizedHistoryCollisionEntropy
    componentHistoryArrangementEntropy
  rw [card_factorizedHistoryEnergyCollision energy hindependent x]
  push_cast
  apply Real.log_prod
  intro c hc
  exact_mod_cast
    (Nat.ne_of_gt
      (Fintype.card_pos :
        0 <
          Fintype.card
            (HistoryArrangement (fun r => x r c))))

/-- **Universal recurrence-entropy floor.** For every additive component
spectrum, independent history rearrangements give a lower bound on the
logarithmic equal-energy multiplicity. Accidental resonances can only raise
the entropy. -/
theorem componentHistoryArrangementEntropy_le_collisionEntropy
    {C R : Type*} [Fintype C] [DecidableEq C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (x : R → ∀ c, I c) :
    componentHistoryArrangementEntropy x ≤
      factorizedHistoryCollisionEntropy energy x := by
  classical
  unfold componentHistoryArrangementEntropy
    factorizedHistoryCollisionEntropy
  rw [← Real.log_prod]
  · apply Real.strictMonoOn_log.monotoneOn
    · change
        0 <
          ∏ c,
            (Fintype.card
              (HistoryArrangement (fun r => x r c)) : ℝ)
      exact Finset.prod_pos fun c hc => by
        exact_mod_cast
          (Fintype.card_pos :
            0 <
              Fintype.card
                (HistoryArrangement (fun r => x r c)))
    · change
        0 <
          (Fintype.card
            (FactorizedHistoryEnergyCollision energy x) : ℝ)
      exact_mod_cast
        (Fintype.card_pos :
          0 <
            Fintype.card
              (FactorizedHistoryEnergyCollision energy x))
    · have hcard :=
        card_componentHistoryArrangement_le_card_energyCollision
          energy x
      rw [card_componentHistoryArrangement] at hcard
      exact_mod_cast hcard
  · intro c hc
    exact_mod_cast
      (Nat.ne_of_gt
        (Fintype.card_pos :
          0 <
            Fintype.card
              (HistoryArrangement (fun r => x r c))))

/-- Indicator of independent component-history rearrangement. -/
noncomputable def componentHistoryRearrangementIndicator
    {C R : Type*} [Fintype R]
    {I : C → Type*} [∀ c, DecidableEq (I c)]
    (x y : R → ∀ c, I c) : ℂ := by
  classical
  exact if IsComponentHistoryRearrangement x y then 1 else 0

/-- **Pair-resolved all-order recurrence kernel.** Under projective
independence, the centered time average of two finite histories converges
to the indicator that every component history is a rearrangement. -/
theorem factorizedHistoryPhaseAverage_tendsto_rearrangementIndicator
    {C R : Type*} [Fintype C] [Fintype R]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy)
    (x y : R → ∀ c, I c) :
    Filter.Tendsto
      (fun T =>
        symmetricPhaseAverage T
          (factorizedHistoryEnergy energy y -
            factorizedHistoryEnergy energy x))
      Filter.atTop
      (nhds (componentHistoryRearrangementIndicator x y)) := by
  classical
  have hzero :
      factorizedHistoryEnergy energy y -
          factorizedHistoryEnergy energy x = 0 ↔
        IsComponentHistoryRearrangement x y := by
    rw [sub_eq_zero]
    exact
      factorizedHistoryEnergy_eq_iff_componentHistoryRearrangement
        energy hindependent x y
  simpa only [componentHistoryRearrangementIndicator, hzero] using
    symmetricPhaseAverage_tendsto_resonanceIndicator
      (factorizedHistoryEnergy energy y -
        factorizedHistoryEnergy energy x)

end

end GaloisForLFunctions.HTGeometry
