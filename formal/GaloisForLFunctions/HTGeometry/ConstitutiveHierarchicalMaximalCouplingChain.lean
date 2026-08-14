import GaloisForLFunctions.HTGeometry.ConstitutiveHierarchicalMaximalCoupling

open scoped BigOperators NNReal

namespace HTGeometry

noncomputable section

/-- Residual profile pair after processing the first `n` observers. -/
def nnObserverChainResidualPair {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) : ℕ → (X → ℝ≥0) × (X → ℝ≥0)
  | 0 => (u, v)
  | n + 1 =>
      let residual := nnObserverChainResidualPair u v observer n
      (nnObserverResidualLeft residual.1 residual.2 (observer n),
        nnObserverResidualRight residual.1 residual.2 (observer n))

def nnObserverChainResidualLeft {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ) : X → ℝ≥0 :=
  (nnObserverChainResidualPair u v observer n).1

def nnObserverChainResidualRight {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ) : X → ℝ≥0 :=
  (nnObserverChainResidualPair u v observer n).2

@[simp] theorem nnObserverChainResidualLeft_zero
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) :
    nnObserverChainResidualLeft u v observer 0 = u := rfl

@[simp] theorem nnObserverChainResidualRight_zero
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) :
    nnObserverChainResidualRight u v observer 0 = v := rfl

@[simp] theorem nnObserverChainResidualLeft_succ
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ) :
    nnObserverChainResidualLeft u v observer (n + 1) =
      nnObserverResidualLeft
        (nnObserverChainResidualLeft u v observer n)
        (nnObserverChainResidualRight u v observer n) (observer n) := rfl

@[simp] theorem nnObserverChainResidualRight_succ
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ) :
    nnObserverChainResidualRight u v observer (n + 1) =
      nnObserverResidualRight
        (nnObserverChainResidualLeft u v observer n)
        (nnObserverChainResidualRight u v observer n) (observer n) := rfl

/-- Coupling mass inserted at stage `n`. -/
def nnObserverChainStagePlan {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ) : X → X → ℝ≥0 :=
  nnObserverBlockPlan
    (nnObserverChainResidualLeft u v observer n)
    (nnObserverChainResidualRight u v observer n) (observer n)

/-- Coupling mass inserted through the first `n` observer levels. -/
def nnObserverChainInternalPlan {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ) (x y : X) : ℝ≥0 :=
  ∑ i ∈ Finset.range n, nnObserverChainStagePlan u v observer i x y

/-- Accumulated hierarchical plan plus the terminal product coupling. -/
def nnObserverChainMaximalPlan {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ) (x y : X) : ℝ≥0 :=
  nnObserverChainInternalPlan u v observer n x y +
    nnProductPlan
      (nnObserverChainResidualLeft u v observer n)
      (nnObserverChainResidualRight u v observer n) x y

theorem nnObserverChainInternalPlan_row_add_residual
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) :
    ∀ n x, (∑ y, nnObserverChainInternalPlan u v observer n x y) +
      nnObserverChainResidualLeft u v observer n x = u x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [nnObserverChainInternalPlan]
  | succ n ih =>
      intro x
      have hsum :
          (∑ y, nnObserverChainInternalPlan u v observer (n + 1) x y) =
            (∑ y, nnObserverChainInternalPlan u v observer n x y) +
              ∑ y, nnObserverChainStagePlan u v observer n x y := by
        simp only [nnObserverChainInternalPlan, Finset.sum_range_succ,
          Finset.sum_add_distrib]
      have hstage := nnObserverBlockPlan_row_add_residual
        (nnObserverChainResidualLeft u v observer n)
        (nnObserverChainResidualRight u v observer n) (observer n) x
      rw [hsum, nnObserverChainResidualLeft_succ,
        add_assoc, nnObserverChainStagePlan, hstage, ih]

theorem nnObserverChainInternalPlan_col_add_residual
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) :
    ∀ n y, (∑ x, nnObserverChainInternalPlan u v observer n x y) +
      nnObserverChainResidualRight u v observer n y = v y := by
  intro n
  induction n with
  | zero =>
      intro y
      simp [nnObserverChainInternalPlan]
  | succ n ih =>
      intro y
      have hsum :
          (∑ x, nnObserverChainInternalPlan u v observer (n + 1) x y) =
            (∑ x, nnObserverChainInternalPlan u v observer n x y) +
              ∑ x, nnObserverChainStagePlan u v observer n x y := by
        simp only [nnObserverChainInternalPlan, Finset.sum_range_succ,
          Finset.sum_add_distrib]
      have hstage := nnObserverBlockPlan_col_add_residual
        (nnObserverChainResidualLeft u v observer n)
        (nnObserverChainResidualRight u v observer n) (observer n) y
      rw [hsum, nnObserverChainResidualRight_succ,
        add_assoc, nnObserverChainStagePlan, hstage, ih]

theorem nnObserverChainResidual_mass_eq
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K)
    (hmass : nnProfileMass u = nnProfileMass v) : ∀ n,
    nnProfileMass (nnObserverChainResidualLeft u v observer n) =
      nnProfileMass (nnObserverChainResidualRight u v observer n) := by
  intro n
  induction n with
  | zero => simpa using hmass
  | succ n ih =>
      simpa only [Nat.succ_eq_add_one, nnObserverChainResidualLeft_succ,
        nnObserverChainResidualRight_succ] using
        nnObserverResidual_mass_eq
          (nnObserverChainResidualLeft u v observer n)
          (nnObserverChainResidualRight u v observer n) (observer n) ih

/-- The recursive chain construction always completes to the prescribed marginals. -/
def nnObserverChainMaximalCoupling
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ)
    (hmass : nnProfileMass u = nnProfileMass v) : FiniteNNCoupling u v where
  plan := nnObserverChainMaximalPlan u v observer n
  row := by
    intro x
    change ∑ y, (nnObserverChainInternalPlan u v observer n x y +
      nnProductPlan
        (nnObserverChainResidualLeft u v observer n)
        (nnObserverChainResidualRight u v observer n) x y) = u x
    rw [Finset.sum_add_distrib, nnProductPlan_row]
    · exact nnObserverChainInternalPlan_row_add_residual u v observer n x
    · exact nnObserverChainResidual_mass_eq u v observer hmass n
  col := by
    intro y
    change ∑ x, (nnObserverChainInternalPlan u v observer n x y +
      nnProductPlan
        (nnObserverChainResidualLeft u v observer n)
        (nnObserverChainResidualRight u v observer n) x y) = v y
    rw [Finset.sum_add_distrib, nnProductPlan_col]
    · exact nnObserverChainInternalPlan_col_add_residual u v observer n y
    · exact nnObserverChainResidual_mass_eq u v observer hmass n

/-- The observer equivalence relations become only coarser along a finite chain. -/
def IsNestedObserverChain {X K : Type*}
    (observer : ℕ → X → K) (n : ℕ) : Prop :=
  ∀ i j, i ≤ j → j < n → ∀ x y,
    observer i x = observer i y → observer j x = observer j y

theorem nnObserverChainResidualLeft_eq_zero_add
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (m : ℕ) {x : X}
    (hx : nnObserverChainResidualLeft u v observer m x = 0) : ∀ d,
    nnObserverChainResidualLeft u v observer (m + d) x = 0 := by
  intro d
  induction d with
  | zero => simpa using hx
  | succ d ih =>
      rw [Nat.add_succ, nnObserverChainResidualLeft_succ]
      exact nnObserverResidualLeft_eq_zero_of_eq_zero
        (nnObserverChainResidualLeft u v observer (m + d))
        (nnObserverChainResidualRight u v observer (m + d))
        (observer (m + d)) ih

theorem nnObserverChainResidualRight_eq_zero_add
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (m : ℕ) {y : X}
    (hy : nnObserverChainResidualRight u v observer m y = 0) : ∀ d,
    nnObserverChainResidualRight u v observer (m + d) y = 0 := by
  intro d
  induction d with
  | zero => simpa using hy
  | succ d ih =>
      rw [Nat.add_succ, nnObserverChainResidualRight_succ]
      exact nnObserverResidualRight_eq_zero_of_eq_zero
        (nnObserverChainResidualLeft u v observer (m + d))
        (nnObserverChainResidualRight u v observer (m + d))
        (observer (m + d)) ih

/-- Once a level has been processed, its one-sided residual invariant survives every later stage. -/
theorem nnObserverChainResidual_oneSided_of_lt
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K)
    {i j : ℕ} (hij : i < j) (k : K) :
    nnFiberMass (nnObserverChainResidualLeft u v observer j) (observer i) k = 0 ∨
      nnFiberMass (nnObserverChainResidualRight u v observer j) (observer i) k = 0 := by
  have hstep := nnObserverResidual_oneSided
    (nnObserverChainResidualLeft u v observer i)
    (nnObserverChainResidualRight u v observer i) (observer i) k
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hij)
  rcases hstep with hleft | hright
  · left
    apply (nnFiberMass_eq_zero_iff _ (observer i) k).mpr
    intro x hx
    apply nnObserverChainResidualLeft_eq_zero_add u v observer (i + 1)
    simpa only [nnObserverChainResidualLeft_succ] using
      (nnFiberMass_eq_zero_iff _ (observer i) k).mp hleft x hx
  · right
    apply (nnFiberMass_eq_zero_iff _ (observer i) k).mpr
    intro y hy
    apply nnObserverChainResidualRight_eq_zero_add u v observer (i + 1)
    simpa only [nnObserverChainResidualRight_succ] using
      (nnFiberMass_eq_zero_iff _ (observer i) k).mp hright y hy

/-- A later insertion cannot recreate agreement at a previously processed observer level. -/
theorem nnObserverChainStagePlan_avoids_earlier
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K)
    {i j : ℕ} (hij : i < j) {x y : X} (hxy : observer i x = observer i y) :
    nnObserverChainStagePlan u v observer j x y = 0 := by
  classical
  rcases nnObserverChainResidual_oneSided_of_lt u v observer hij (observer i x) with
    hleft | hright
  · have hxzero : nnObserverChainResidualLeft u v observer j x = 0 :=
      (nnFiberMass_eq_zero_iff _ (observer i) (observer i x)).mp hleft x rfl
    simp [nnObserverChainStagePlan, nnObserverBlockPlan, hxzero]
  · have hyzero : nnObserverChainResidualRight u v observer j y = 0 :=
      (nnFiberMass_eq_zero_iff _ (observer i) (observer i x)).mp hright y hxy.symm
    simp [nnObserverChainStagePlan, nnObserverBlockPlan, hyzero]

/-- Terminal residual completion cannot recreate agreement at an earlier processed level. -/
theorem nnObserverChainProductPlan_avoids_earlier
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K)
    {i n : ℕ} (hin : i < n) {x y : X} (hxy : observer i x = observer i y) :
    nnProductPlan
      (nnObserverChainResidualLeft u v observer n)
      (nnObserverChainResidualRight u v observer n) x y = 0 := by
  classical
  rcases nnObserverChainResidual_oneSided_of_lt u v observer hin (observer i x) with
    hleft | hright
  · have hxzero : nnObserverChainResidualLeft u v observer n x = 0 :=
      (nnFiberMass_eq_zero_iff _ (observer i) (observer i x)).mp hleft x rfl
    simp [nnProductPlan, hxzero]
  · have hyzero : nnObserverChainResidualRight u v observer n y = 0 :=
      (nnFiberMass_eq_zero_iff _ (observer i) (observer i x)).mp hright y hxy.symm
    simp [nnProductPlan, hyzero]

theorem nnObserverChainInternalPlan_supported_level
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) {n i : ℕ}
    (hchain : IsNestedObserverChain observer n) (hi : i < n)
    {x y : X} (hne : nnObserverChainInternalPlan u v observer (i + 1) x y ≠ 0) :
    observer i x = observer i y := by
  classical
  by_contra hxy
  apply hne
  unfold nnObserverChainInternalPlan
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hneq : observer j x ≠ observer j y := fun h =>
    hxy (hchain j i hji hi x y h)
  simp [nnObserverChainStagePlan, nnObserverBlockPlan, hneq]

/-- Internal mass through level `i` saturates every block capacity at that level. -/
theorem nnObserverChainInternalPlan_blockMass
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) {n i : ℕ}
    (hchain : IsNestedObserverChain observer n) (hi : i < n) (k : K) :
    nnCouplingBlockMass (nnObserverChainInternalPlan u v observer (i + 1))
        (observer i) k =
      min (nnFiberMass u (observer i) k) (nnFiberMass v (observer i) k) := by
  apply nnCouplingBlockMass_eq_min_of_balanced_oneSided
    u v
    (nnObserverChainResidualLeft u v observer (i + 1))
    (nnObserverChainResidualRight u v observer (i + 1))
    (nnObserverChainInternalPlan u v observer (i + 1)) (observer i)
  · exact nnObserverChainInternalPlan_row_add_residual u v observer (i + 1)
  · exact nnObserverChainInternalPlan_col_add_residual u v observer (i + 1)
  · intro x y
    exact nnObserverChainInternalPlan_supported_level u v observer hchain hi
  · intro k'
    simpa only [nnObserverChainResidualLeft_succ,
      nnObserverChainResidualRight_succ] using
      nnObserverResidual_oneSided
        (nnObserverChainResidualLeft u v observer i)
        (nnObserverChainResidualRight u v observer i) (observer i) k'

/-- On a level-agreeing pair, the completed chain plan equals the mass already inserted through
that level. -/
theorem nnObserverChainMaximalPlan_eq_internal_of_same
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) {n i : ℕ}
    (hi : i < n) {x y : X} (hxy : observer i x = observer i y) :
    nnObserverChainMaximalPlan u v observer n x y =
      nnObserverChainInternalPlan u v observer (i + 1) x y := by
  classical
  have hle : i + 1 ≤ n := Nat.succ_le_iff.mpr hi
  have htail :
      ∑ j ∈ Finset.Ico (i + 1) n, nnObserverChainStagePlan u v observer j x y = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact nnObserverChainStagePlan_avoids_earlier u v observer
      (lt_of_lt_of_le (Nat.lt_succ_self i) (Finset.mem_Ico.mp hj).1) hxy
  have hproduct := nnObserverChainProductPlan_avoids_earlier u v observer hi hxy
  unfold nnObserverChainMaximalPlan nnObserverChainInternalPlan
  rw [← Finset.sum_range_add_sum_Ico _ hle, htail, add_zero, hproduct, add_zero]

/-- The recursively constructed coupling is simultaneously maximal at every level of an arbitrary
finite nested observer chain. -/
theorem nnObserverChainMaximalCoupling_agreement
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ)
    (hmass : nnProfileMass u = nnProfileMass v)
    (hchain : IsNestedObserverChain observer n) {i : ℕ} (hi : i < n) :
    nnCouplingAgreementMass
        (nnObserverChainMaximalCoupling u v observer n hmass).plan (observer i) =
      nnObserverCapacity u v (observer i) := by
  classical
  unfold nnCouplingAgreementMass nnObserverCapacity
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (nnObserverChainMaximalCoupling u v observer n hmass).plan =
    nnObserverChainMaximalPlan u v observer n from rfl]
  rw [← nnObserverChainInternalPlan_blockMass u v observer hchain hi k]
  unfold nnCouplingBlockMass
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hkx : observer i x = k
  · simp only [hkx, if_true]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hky : observer i y = k
    · simp only [hky, if_true]
      rw [nnObserverChainMaximalPlan_eq_internal_of_same
        u v observer hi (hkx.trans hky.symm)]
    · simp [hky]
  · simp [hkx]

/-- Arbitrary finite-chain simultaneous maximality package. -/
theorem exists_coupling_simultaneously_maximal_for_nested_observer_chain
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ)
    (hmass : nnProfileMass u = nnProfileMass v)
    (hchain : IsNestedObserverChain observer n) :
    ∃ gamma : FiniteNNCoupling u v, ∀ i < n,
      nnCouplingAgreementMass gamma.plan (observer i) =
        nnObserverCapacity u v (observer i) := by
  exact ⟨nnObserverChainMaximalCoupling u v observer n hmass,
    fun i hi ↦ nnObserverChainMaximalCoupling_agreement
      u v observer n hmass hchain hi⟩

/-- Literal mass carried by the pairs which collide at `coarse` but not at `fine`. -/
def nnCouplingCollisionStratumMass {X K : Type*} [Fintype X] [DecidableEq K]
    (gamma : X → X → ℝ≥0) (fine coarse : X → K) : ℝ≥0 :=
  ∑ x, ∑ y, if coarse x = coarse y ∧ fine x ≠ fine y then gamma x y else 0

theorem nnCouplingAgreementMass_eq_pair_sum
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (gamma : X → X → ℝ≥0) (observer : X → K) :
    nnCouplingAgreementMass gamma observer =
      ∑ x, ∑ y, if observer x = observer y then gamma x y else 0 := by
  classical
  unfold nnCouplingAgreementMass nnCouplingBlockMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ k, if observer x = k then
        ∑ y, if observer y = k then gamma x y else 0 else 0) =
        ∑ y, if observer y = observer x then gamma x y else 0 := by simp
    _ = ∑ y, if observer x = observer y then gamma x y else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxy : observer x = observer y
      · rw [if_pos hxy, if_pos hxy.symm]
      · rw [if_neg hxy, if_neg (Ne.symm hxy)]

/-- Agreement at a coarse observer splits exactly into earlier agreement and the new collision
stratum. -/
theorem nnCouplingAgreementMass_coarse_eq_fine_add_stratum
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (gamma : X → X → ℝ≥0) (fine coarse : X → K)
    (hnested : ∀ x y, fine x = fine y → coarse x = coarse y) :
    nnCouplingAgreementMass gamma coarse =
      nnCouplingAgreementMass gamma fine +
        nnCouplingCollisionStratumMass gamma fine coarse := by
  classical
  rw [nnCouplingAgreementMass_eq_pair_sum, nnCouplingAgreementMass_eq_pair_sum]
  unfold nnCouplingCollisionStratumMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hf : fine x = fine y
  · have hc := hnested x y hf
    simp [hf, hc]
  · by_cases hc : coarse x = coarse y <;> simp [hf, hc]

theorem nnCouplingAgreementMass_mono_of_nested
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (gamma : X → X → ℝ≥0) (fine coarse : X → K)
    (hnested : ∀ x y, fine x = fine y → coarse x = coarse y) :
    nnCouplingAgreementMass gamma fine ≤ nnCouplingAgreementMass gamma coarse := by
  rw [nnCouplingAgreementMass_coarse_eq_fine_add_stratum gamma fine coarse hnested]
  exact le_add_right le_rfl

/-- Observer agreement capacities are monotone under coarsening. -/
theorem nnObserverCapacity_mono_of_nested
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (fine coarse : X → K)
    (hmass : nnProfileMass u = nnProfileMass v)
    (hnested : ∀ x y, fine x = fine y → coarse x = coarse y) :
    nnObserverCapacity u v fine ≤ nnObserverCapacity u v coarse := by
  let gamma := nnObserverMaximalCoupling u v fine hmass
  rw [← nnObserverMaximalCoupling_agreement u v fine hmass]
  exact (nnCouplingAgreementMass_mono_of_nested gamma.plan fine coarse hnested).trans
    (nnCouplingAgreementMass_le_capacity gamma coarse)

/-- Every simultaneous maximizer has the forced successive collision mass `A_j - A_i`. -/
theorem nnCouplingCollisionStratumMass_eq_capacity_sub
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    {u v : X → ℝ≥0} (gamma : FiniteNNCoupling u v)
    (fine coarse : X → K)
    (hnested : ∀ x y, fine x = fine y → coarse x = coarse y)
    (hfine : nnCouplingAgreementMass gamma.plan fine = nnObserverCapacity u v fine)
    (hcoarse : nnCouplingAgreementMass gamma.plan coarse = nnObserverCapacity u v coarse) :
    nnCouplingCollisionStratumMass gamma.plan fine coarse =
      nnObserverCapacity u v coarse - nnObserverCapacity u v fine := by
  have hsplit := nnCouplingAgreementMass_coarse_eq_fine_add_stratum
    gamma.plan fine coarse hnested
  rw [hfine, hcoarse] at hsplit
  exact eq_tsub_of_add_eq (by simpa [add_comm] using hsplit.symm)

/-- The constructed chain witness has every paper collision stratum mass. -/
theorem nnObserverChainMaximalCoupling_collisionStratum
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ)
    (hmass : nnProfileMass u = nnProfileMass v)
    (hchain : IsNestedObserverChain observer n) {i j : ℕ}
    (hij : i ≤ j) (hj : j < n) :
    nnCouplingCollisionStratumMass
        (nnObserverChainMaximalCoupling u v observer n hmass).plan
        (observer i) (observer j) =
      nnObserverCapacity u v (observer j) - nnObserverCapacity u v (observer i) := by
  apply nnCouplingCollisionStratumMass_eq_capacity_sub
    (nnObserverChainMaximalCoupling u v observer n hmass) (observer i) (observer j)
  · exact hchain i j hij hj
  · exact nnObserverChainMaximalCoupling_agreement
      u v observer n hmass hchain (lt_of_le_of_lt hij hj)
  · exact nnObserverChainMaximalCoupling_agreement
      u v observer n hmass hchain hj

/-- Mass outside the terminal collision relation. -/
def nnCouplingOutsideAgreementMass {X K : Type*} [Fintype X] [DecidableEq K]
    (gamma : X → X → ℝ≥0) (observer : X → K) : ℝ≥0 :=
  ∑ x, ∑ y, if observer x ≠ observer y then gamma x y else 0

theorem nnCouplingAgreementMass_add_outside
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    {u v : X → ℝ≥0} (gamma : FiniteNNCoupling u v) (observer : X → K) :
    nnCouplingAgreementMass gamma.plan observer +
      nnCouplingOutsideAgreementMass gamma.plan observer = nnProfileMass u := by
  classical
  rw [nnCouplingAgreementMass_eq_pair_sum]
  unfold nnCouplingOutsideAgreementMass nnProfileMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib]
  calc
    (∑ y : X, ((if observer x = observer y then gamma.plan x y else 0) +
        (if observer x ≠ observer y then gamma.plan x y else 0))) =
        ∑ y, gamma.plan x y := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxy : observer x = observer y <;> simp [hxy]
    _ = u x := gamma.row x

/-- Every maximal level has the forced outside mass `total mass - capacity`. -/
theorem nnCouplingOutsideAgreementMass_eq_profileMass_sub_capacity
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    {u v : X → ℝ≥0} (gamma : FiniteNNCoupling u v) (observer : X → K)
    (hmax : nnCouplingAgreementMass gamma.plan observer = nnObserverCapacity u v observer) :
    nnCouplingOutsideAgreementMass gamma.plan observer =
      nnProfileMass u - nnObserverCapacity u v observer := by
  have hsplit := nnCouplingAgreementMass_add_outside gamma observer
  rw [hmax] at hsplit
  exact eq_tsub_of_add_eq (by simpa [add_comm] using hsplit)

/-- Probability-profile form of the paper's terminal mass `1 - A_N`. -/
theorem nnObserverChainMaximalCoupling_outside_eq_one_sub_capacity
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ)
    (hu : nnProfileMass u = 1) (hv : nnProfileMass v = 1)
    (hchain : IsNestedObserverChain observer n) {i : ℕ} (hi : i < n) :
    nnCouplingOutsideAgreementMass
        (nnObserverChainMaximalCoupling u v observer n (hu.trans hv.symm)).plan
        (observer i) = 1 - nnObserverCapacity u v (observer i) := by
  simpa [hu] using nnCouplingOutsideAgreementMass_eq_profileMass_sub_capacity
    (nnObserverChainMaximalCoupling u v observer n (hu.trans hv.symm)) (observer i)
    (nnObserverChainMaximalCoupling_agreement
      u v observer n (hu.trans hv.symm) hchain hi)

/-- Sum of all agreement objectives along the observer history. -/
def nnObserverChainObjective {X K : Type*} [Fintype X] [Fintype K]
    [DecidableEq K] (gamma : X → X → ℝ≥0)
    (observer : ℕ → X → K) (n : ℕ) : ℝ≥0 :=
  ∑ i ∈ Finset.range n, nnCouplingAgreementMass gamma (observer i)

def nnObserverChainCapacityTotal {X K : Type*} [Fintype X] [Fintype K]
    [DecidableEq K] (u v : X → ℝ≥0)
    (observer : ℕ → X → K) (n : ℕ) : ℝ≥0 :=
  ∑ i ∈ Finset.range n, nnObserverCapacity u v (observer i)

/-- The consensus face consists of couplings maximizing every observer agreement. -/
def nnObserverChainConsensusFace {X K : Type*} [Fintype X] [Fintype K]
    [DecidableEq K] (u v : X → ℝ≥0)
    (observer : ℕ → X → K) (n : ℕ) : Set (FiniteNNCoupling u v) :=
  { gamma | ∀ i < n, nnCouplingAgreementMass gamma.plan (observer i) =
      nnObserverCapacity u v (observer i) }

theorem nnObserverChainObjective_le_capacityTotal
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    {u v : X → ℝ≥0} (gamma : FiniteNNCoupling u v)
    (observer : ℕ → X → K) (n : ℕ) :
    nnObserverChainObjective gamma.plan observer n ≤
      nnObserverChainCapacityTotal u v observer n := by
  apply Finset.sum_le_sum
  intro i hi
  exact nnCouplingAgreementMass_le_capacity gamma (observer i)

/-- Equality in the single summed linear objective is equivalent to simultaneous saturation of
all its individual upper bounds. -/
theorem nnObserverChainObjective_eq_capacityTotal_iff
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    {u v : X → ℝ≥0} (gamma : FiniteNNCoupling u v)
    (observer : ℕ → X → K) (n : ℕ) :
    nnObserverChainObjective gamma.plan observer n =
        nnObserverChainCapacityTotal u v observer n ↔
      gamma ∈ nnObserverChainConsensusFace u v observer n := by
  constructor
  · intro hsum i hi
    apply le_antisymm (nnCouplingAgreementMass_le_capacity gamma (observer i))
    by_contra hnot
    have hstrict : nnCouplingAgreementMass gamma.plan (observer i) <
        nnObserverCapacity u v (observer i) :=
      lt_of_not_ge hnot
    have hlt : nnObserverChainObjective gamma.plan observer n <
        nnObserverChainCapacityTotal u v observer n := by
      apply Finset.sum_lt_sum
      · intro j hj
        exact nnCouplingAgreementMass_le_capacity gamma (observer j)
      · exact ⟨i, Finset.mem_range.mpr hi, hstrict⟩
    exact hlt.ne hsum
  · intro hface
    unfold nnObserverChainObjective nnObserverChainCapacityTotal
    apply Finset.sum_congr rfl
    intro i hi
    exact hface i (Finset.mem_range.mp hi)

/-- Exact exposed-face package: the consensus face is nonempty and is precisely the maximizer set
of one linear agreement objective on the transport polytope. -/
theorem nnObserverChainConsensusFace_nonempty_exposed
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : ℕ → X → K) (n : ℕ)
    (hmass : nnProfileMass u = nnProfileMass v)
    (hchain : IsNestedObserverChain observer n) :
    Set.Nonempty (nnObserverChainConsensusFace u v observer n) ∧
      (∀ gamma : FiniteNNCoupling u v,
        nnObserverChainObjective gamma.plan observer n ≤
          nnObserverChainCapacityTotal u v observer n) ∧
      (∀ gamma : FiniteNNCoupling u v,
        nnObserverChainObjective gamma.plan observer n =
            nnObserverChainCapacityTotal u v observer n ↔
          gamma ∈ nnObserverChainConsensusFace u v observer n) := by
  refine ⟨⟨nnObserverChainMaximalCoupling u v observer n hmass, ?_⟩, ?_, ?_⟩
  · intro i hi
    exact nnObserverChainMaximalCoupling_agreement
      u v observer n hmass hchain hi
  · exact fun gamma ↦ nnObserverChainObjective_le_capacityTotal gamma observer n
  · exact fun gamma ↦ nnObserverChainObjective_eq_capacityTotal_iff gamma observer n

theorem nnFiberMass_coe {X K : Type*} [Fintype X] [DecidableEq K]
    (u : X → ℝ≥0) (observer : X → K) (k : K) :
    (nnFiberMass u observer k : ℝ) =
      finiteSignedFiberMass (fun x ↦ (u x : ℝ)) observer k := by
  simp only [nnFiberMass, finiteSignedFiberMass, NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : observer x = k <;> simp [h]

/-- Observer overlap capacity is exactly one minus total variation for probability profiles. -/
theorem nnObserverCapacity_eq_one_sub_totalVariation
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (observer : X → K)
    (hu : nnProfileMass u = 1) (hv : nnProfileMass v = 1) :
    (nnObserverCapacity u v observer : ℝ) = 1 -
      finiteProfileTotalVariation
        (fun k ↦ (nnFiberMass u observer k : ℝ))
        (fun k ↦ (nnFiberMass v observer k : ℝ)) := by
  have hsumu : ∑ k, (nnFiberMass u observer k : ℝ) = 1 := by
    rw [show (∑ k, (nnFiberMass u observer k : ℝ)) =
      ∑ k, finiteSignedFiberMass (fun x ↦ (u x : ℝ)) observer k by
        apply Finset.sum_congr rfl
        intro k hk
        exact nnFiberMass_coe u observer k]
    rw [← finiteSignedCharge_eq_sum_fiberMass]
    simpa [finiteSignedCharge, nnProfileMass] using congrArg ((↑) : ℝ≥0 → ℝ) hu
  have hsumv : ∑ k, (nnFiberMass v observer k : ℝ) = 1 := by
    rw [show (∑ k, (nnFiberMass v observer k : ℝ)) =
      ∑ k, finiteSignedFiberMass (fun x ↦ (v x : ℝ)) observer k by
        apply Finset.sum_congr rfl
        intro k hk
        exact nnFiberMass_coe v observer k]
    rw [← finiteSignedCharge_eq_sum_fiberMass]
    simpa [finiteSignedCharge, nnProfileMass] using congrArg ((↑) : ℝ≥0 → ℝ) hv
  have hcapacity : (nnObserverCapacity u v observer : ℝ) =
      ∑ k, min (nnFiberMass u observer k : ℝ)
        (nnFiberMass v observer k : ℝ) := by
    simp [nnObserverCapacity]
  rw [hcapacity, finiteProfileTotalVariation_eq, hsumu, hsumv]
  unfold finiteProfileMeet
  ring

/-- Four atoms witnessing incompatibility of incomparable observer partitions. -/
inductive IncomparableObserverAtom
  | a | b | c | d
  deriving DecidableEq, Fintype

def incomparableLeftProfile : IncomparableObserverAtom → ℝ≥0
  | .a | .d => 1 / 2
  | .b | .c => 0

def incomparableRightProfile : IncomparableObserverAtom → ℝ≥0
  | .b | .c => 1 / 2
  | .a | .d => 0

def incomparableRowObserver : IncomparableObserverAtom → Bool
  | .a | .b => false
  | .c | .d => true

def incomparableColumnObserver : IncomparableObserverAtom → Bool
  | .a | .c => false
  | .b | .d => true

theorem incomparableObserverAtom_univ :
    (Finset.univ : Finset IncomparableObserverAtom) =
      {.a, .b, .c, .d} := by
  ext x
  cases x <;> simp

theorem nnreal_invTwo_add_invTwo : (2 : ℝ≥0)⁻¹ + 2⁻¹ = 1 := by
  calc
    (2 : ℝ≥0)⁻¹ + 2⁻¹ = 2 * 2⁻¹ := (two_mul _).symm
    _ = 1 := mul_inv_cancel₀ (two_ne_zero : (2 : ℝ≥0) ≠ 0)

theorem incomparableProfiles_mass :
    nnProfileMass incomparableLeftProfile = 1 ∧
      nnProfileMass incomparableRightProfile = 1 := by
  simp [nnProfileMass, incomparableObserverAtom_univ,
    incomparableLeftProfile, incomparableRightProfile, nnreal_invTwo_add_invTwo]

theorem incomparableRowObserver_capacity :
    nnObserverCapacity incomparableLeftProfile incomparableRightProfile
      incomparableRowObserver = 1 := by
  simp [nnObserverCapacity, nnFiberMass, incomparableObserverAtom_univ,
    incomparableLeftProfile, incomparableRightProfile, incomparableRowObserver,
    nnreal_invTwo_add_invTwo]

theorem incomparableColumnObserver_capacity :
    nnObserverCapacity incomparableLeftProfile incomparableRightProfile
      incomparableColumnObserver = 1 := by
  simp [nnObserverCapacity, nnFiberMass, incomparableObserverAtom_univ,
    incomparableLeftProfile, incomparableRightProfile, incomparableColumnObserver,
    nnreal_invTwo_add_invTwo]

/-- Sharp necessity of hierarchy: the two crossing two-block observers have disjoint maximal
coupling faces. -/
theorem incomparableObserver_maximalFaces_disjoint :
    ¬ ∃ gamma : FiniteNNCoupling incomparableLeftProfile incomparableRightProfile,
      nnCouplingAgreementMass gamma.plan incomparableRowObserver =
          nnObserverCapacity incomparableLeftProfile incomparableRightProfile
            incomparableRowObserver ∧
        nnCouplingAgreementMass gamma.plan incomparableColumnObserver =
          nnObserverCapacity incomparableLeftProfile incomparableRightProfile
            incomparableColumnObserver := by
  rintro ⟨gamma, hrowMax, hcolMax⟩
  have hout : nnCouplingOutsideAgreementMass gamma.plan incomparableRowObserver = 0 := by
    have h := nnCouplingOutsideAgreementMass_eq_profileMass_sub_capacity
      gamma incomparableRowObserver hrowMax
    rw [incomparableProfiles_mass.1, incomparableRowObserver_capacity] at h
    simpa using h
  have hoff : ∀ x y, incomparableRowObserver x ≠ incomparableRowObserver y →
      gamma.plan x y = 0 := by
    intro x y hxy
    rw [nnCouplingOutsideAgreementMass] at hout
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ by positivity)).mp
      hout x (Finset.mem_univ x)
    have hy := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ by positivity)).mp
      hx y (Finset.mem_univ y)
    simpa [hxy] using hy
  have hrowZero : ∀ x, incomparableLeftProfile x = 0 → ∀ y, gamma.plan x y = 0 := by
    intro x hx y
    have hsum := gamma.row x
    rw [hx] at hsum
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ by positivity)).mp
      hsum y (Finset.mem_univ y)
  have hcolZero : ∀ y, incomparableRightProfile y = 0 → ∀ x, gamma.plan x y = 0 := by
    intro y hy x
    have hsum := gamma.col y
    rw [hy] at hsum
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ by positivity)).mp
      hsum x (Finset.mem_univ x)
  have hcolumnZero :
      nnCouplingAgreementMass gamma.plan incomparableColumnObserver = 0 := by
    rw [nnCouplingAgreementMass_eq_pair_sum]
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    by_cases hxy : incomparableColumnObserver x = incomparableColumnObserver y
    · rw [if_pos hxy]
      cases x <;> cases y
      all_goals simp [incomparableColumnObserver] at hxy
      all_goals first
        | exact hcolZero _ rfl _
        | exact hrowZero _ rfl _
        | exact hoff _ _ (by simp [incomparableRowObserver])
    · rw [if_neg hxy]
  rw [incomparableColumnObserver_capacity, hcolumnZero] at hcolMax
  exact zero_ne_one hcolMax

end


end HTGeometry
