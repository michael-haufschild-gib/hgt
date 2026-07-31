import GaloisForLFunctions.RHTower.FiniteQuantumExpectationGraphRateDistortionLaw
import GaloisForLFunctions.RHTower.FiniteQuantumExpectationEscapeReturnDichotomyLaw

/-!
# Finite localized spectral-support recurrence

Let `p` be a probability weight on finitely many energy sectors and select a
nonempty effective support `S`.  Synchronize the complete graph on `S` and
leave every sector outside `S` isolated.  The resulting recurrence exponent
is exactly `|S| - 1`, independent of ambient spectral dimension.

For the scalar coefficient history `cᵢⱼ = pᵢpⱼ`, omitted directed
coefficient mass is at most twice the probability tail outside `S`, while
selected mass is at most one.  These two facts give an explicit recurrence
budget and an unconditional never-exits-or-post-exit alternative.

This is an abstract finite spectral-weight theorem.  It does not assert that
any Hamiltonian ensemble has localized eigenfunctions or supplies a decay
estimate for the tail.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Complete graph on the selected vertices, with every outside vertex
isolated. -/
def finiteLocalizedSpectralSupportGraph
    {V : Type*} [DecidableEq V]
    (S : Finset V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ i ∈ S ∧ j ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Every vertex outside the selected support is isolated. -/
theorem finiteLocalizedSpectralSupportGraph_isIsolated_of_not_mem
    {V : Type*} [DecidableEq V]
    (S : Finset V) {i : V} (hi : i ∉ S) :
    (finiteLocalizedSpectralSupportGraph S).IsIsolated i := by
  intro j hij
  exact hi hij.2.1

private theorem finiteLocalizedSpectralSupportGraph_eq_of_reachable_of_not_mem
    {V : Type*} [DecidableEq V]
    (S : Finset V) {i j : V} (hi : i ∉ S)
    (hij : (finiteLocalizedSpectralSupportGraph S).Reachable i j) :
    i = j := by
  exact hij.elim fun p => by
    cases p with
    | nil => rfl
    | cons hadj q => exact (hi hadj.2.1).elim

private def finiteLocalizedSpectralSupportComponentLabel
    {V : Type*} [DecidableEq V]
    (S : Finset V) (i : V) :
    Option {j : V // j ∉ S} :=
  if hi : i ∈ S then none else some ⟨i, hi⟩

private theorem
    finiteLocalizedSpectralSupportComponentLabel_eq_of_reachable
    {V : Type*} [DecidableEq V]
    (S : Finset V) {i j : V}
    (hij : (finiteLocalizedSpectralSupportGraph S).Reachable i j) :
    finiteLocalizedSpectralSupportComponentLabel S i =
      finiteLocalizedSpectralSupportComponentLabel S j := by
  by_cases hi : i ∈ S
  · have hj : j ∈ S := by
      by_contra hj
      have hji : j = i :=
        finiteLocalizedSpectralSupportGraph_eq_of_reachable_of_not_mem
          S hj hij.symm
      exact hj (hji ▸ hi)
    simp [finiteLocalizedSpectralSupportComponentLabel, hi, hj]
  · have hEq : i = j :=
      finiteLocalizedSpectralSupportGraph_eq_of_reachable_of_not_mem
        S hi hij
    subst j
    rfl

/-- Connected components are one selected clique component plus one
component for every omitted vertex. -/
noncomputable def finiteLocalizedSpectralSupportComponentEquiv
    {V : Type*} [DecidableEq V]
    (S : Finset V) (hS : S.Nonempty) :
    (finiteLocalizedSpectralSupportGraph S).ConnectedComponent ≃
      Option {i : V // i ∉ S} where
  toFun :=
    SimpleGraph.ConnectedComponent.lift
      (finiteLocalizedSpectralSupportComponentLabel S)
      (fun _ _ p _hp =>
        finiteLocalizedSpectralSupportComponentLabel_eq_of_reachable
          S p.reachable)
  invFun o :=
    match o with
    | none =>
        (finiteLocalizedSpectralSupportGraph S).connectedComponentMk
          hS.choose
    | some i =>
        (finiteLocalizedSpectralSupportGraph S).connectedComponentMk i.1
  left_inv c := by
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ i =>
        by_cases hi : i ∈ S
        · simp [finiteLocalizedSpectralSupportComponentLabel, hi]
          by_cases hEq : hS.choose = i
          · subst i
            exact SimpleGraph.Reachable.refl _
          · exact
              (show
                (finiteLocalizedSpectralSupportGraph S).Adj
                  hS.choose i from
                ⟨hEq, hS.choose_spec, hi⟩).reachable
        · simp [finiteLocalizedSpectralSupportComponentLabel, hi]
  right_inv o := by
    cases o with
    | none =>
        simp [finiteLocalizedSpectralSupportComponentLabel,
          hS.choose_spec]
    | some i =>
        simp [finiteLocalizedSpectralSupportComponentLabel, i.property]

/-- Exact component count of a nonempty selected clique with isolated
outside vertices. -/
theorem finiteLocalizedSpectralSupportGraph_componentCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S.Nonempty) :
    Nat.card
        (finiteLocalizedSpectralSupportGraph S).ConnectedComponent =
      Fintype.card V - S.card + 1 := by
  rw [Nat.card_congr
    (finiteLocalizedSpectralSupportComponentEquiv S hS)]
  rw [Nat.card_eq_fintype_card]
  have hcompl :
      Fintype.card {i : V // i ∉ S} =
        Fintype.card V - S.card := by
    calc
      Fintype.card {i : V // i ∉ S} =
          Fintype.card V -
            Fintype.card {i : V // i ∈ S} :=
        Fintype.card_subtype_compl (fun i : V => i ∈ S)
      _ = Fintype.card V - S.card := by simp
  simp [hcompl]

/-- Exact graph-rank law: the effective phase dimension is `|S| - 1`. -/
theorem finiteLocalizedSpectralSupportGraph_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S.Nonempty) :
    Fintype.card V -
        Nat.card
          (finiteLocalizedSpectralSupportGraph S).ConnectedComponent =
      S.card - 1 := by
  rw [finiteLocalizedSpectralSupportGraph_componentCard S hS]
  have hcard : S.card ≤ Fintype.card V := S.card_le_univ
  have hpos : 1 ≤ S.card := hS.card_pos
  omega

/-- Scalar ordered-pair coefficient generated by probability weights. -/
def finiteLocalizedSpectralCoefficient
    {d : ℕ} (p : Fin d → ℝ)
    (_ : Unit) (i j : Fin d) : ℂ :=
  ((p i * p j : ℝ) : ℂ)

/-- Probability weight outside the selected effective support. -/
def finiteLocalizedSubsetTail
    {d : ℕ} (p : Fin d → ℝ)
    (S : Finset (Fin d)) : ℝ :=
  ∑ i, if i ∈ S then 0 else p i

/-- Absolute scalar-history deviation generated by the coefficients
`pᵢpⱼ`, with the unique history assigned weight one. -/
def finiteLocalizedSpectralDeviation
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ) : ℝ :=
  finiteQuantumExpectationTotalDeviation
    (fun _ : Unit => 1) z (finiteLocalizedSpectralCoefficient p)

/-- Localized-support recurrence budget for an externally supplied tail
bound `α`. -/
def finiteLocalizedSpectralRecurrenceBudget
    (α : ℝ) (Q : ℕ) : ℝ :=
  4 * α + 2 * (2 * Real.pi / (Q + 1 : ℝ))

theorem finiteLocalizedSubsetTail_nonneg
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (S : Finset (Fin d)) :
    0 ≤ finiteLocalizedSubsetTail p S := by
  unfold finiteLocalizedSubsetTail
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact le_rfl
  · exact hp i

/-- With nonnegative probability weights, directed coefficient mass on
`(i,j)` is exactly `pᵢpⱼ`. -/
theorem finiteLocalizedSpectral_unionCoefficientMass_eq
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i j : Fin d) :
    finiteExpectationUnionCoefficientMass
        (fun _ : Unit => 1)
        (finiteLocalizedSpectralCoefficient p) i j =
      p i * p j := by
  simp [finiteExpectationUnionCoefficientMass,
    finiteLocalizedSpectralCoefficient,
    abs_of_nonneg (hp i), abs_of_nonneg (hp j)]

/-- Selected directed coefficient mass never exceeds total probability
mass squared, hence is at most one. -/
theorem finiteLocalizedSpectral_selectedMass_le_one
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d)) :
    finiteExpectationSelectedDirectedMass
        (finiteLocalizedSpectralSupportGraph S)
        (fun _ : Unit => 1)
        (finiteLocalizedSpectralCoefficient p) ≤ 1 := by
  classical
  unfold finiteExpectationSelectedDirectedMass
  calc
    (∑ i, ∑ j,
        if (finiteLocalizedSpectralSupportGraph S).Adj i j
        then finiteExpectationUnionCoefficientMass
          (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) i j
        else 0) ≤
        ∑ i, ∑ j, p i * p j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hadj :
          (finiteLocalizedSpectralSupportGraph S).Adj i j
      · simp [hadj,
          finiteLocalizedSpectral_unionCoefficientMass_eq p hp]
      · simp [hadj, mul_nonneg (hp i) (hp j)]
    _ = ∑ i, p i * (∑ j, p j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = (∑ i, p i) * (∑ j, p j) := by
      rw [Finset.sum_mul]
    _ = 1 := by rw [hpSum]; norm_num

/-- Omitted directed coefficient mass is at most twice the probability
tail.  The estimate is orientation-honest and allows double counting of
outside--outside pairs only in the upper bound. -/
theorem finiteLocalizedSpectral_omittedMass_le_two_tail
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d)) :
    finiteExpectationOmittedDirectedMass
        (finiteLocalizedSpectralSupportGraph S)
        (fun _ : Unit => 1)
        (finiteLocalizedSpectralCoefficient p) ≤
      2 * finiteLocalizedSubsetTail p S := by
  classical
  unfold finiteExpectationOmittedDirectedMass
  let q : Fin d → ℝ :=
    fun i => if i ∈ S then 0 else p i
  calc
    (∑ i, ∑ j,
        if i ≠ j ∧
            ¬ (finiteLocalizedSpectralSupportGraph S).Adj i j
        then finiteExpectationUnionCoefficientMass
          (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) i j
        else 0) ≤
        ∑ i, ∑ j, (q i * p j + p i * q j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases homit :
          i ≠ j ∧
            ¬ (finiteLocalizedSpectralSupportGraph S).Adj i j
      · rw [if_pos homit,
          finiteLocalizedSpectral_unionCoefficientMass_eq p hp]
        by_cases hiS : i ∈ S
        · have hjS : j ∉ S := by
            intro hjS
            exact homit.2 ⟨homit.1, hiS, hjS⟩
          simp [q, hiS, hjS]
        · by_cases hjS : j ∈ S
          · simp [q, hiS, hjS]
          · simp [q, hiS, hjS,
              mul_nonneg (hp i) (hp j)]
      · rw [if_neg homit]
        have hqi : 0 ≤ q i := by
          simp only [q]
          split_ifs
          · exact le_rfl
          · exact hp i
        have hqj : 0 ≤ q j := by
          simp only [q]
          split_ifs
          · exact le_rfl
          · exact hp j
        exact add_nonneg
          (mul_nonneg hqi (hp j))
          (mul_nonneg (hp i) hqj)
    _ = (∑ i, q i) * (∑ j, p j) +
          (∑ i, p i) * (∑ j, q j) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · calc
          (∑ i, ∑ j, q i * p j) =
              ∑ i, q i * (∑ j, p j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
          _ = (∑ i, q i) * (∑ j, p j) := by
            rw [Finset.sum_mul]
      · calc
          (∑ i, ∑ j, p i * q j) =
              ∑ i, p i * (∑ j, q j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
          _ = (∑ i, p i) * (∑ j, q j) := by
            rw [Finset.sum_mul]
    _ = 2 * finiteLocalizedSubsetTail p S := by
      rw [hpSum]
      simp only [q, finiteLocalizedSubsetTail]
      ring

/-- Parametric tail interface: any external certificate
`tail(p,S) ≤ α` gives omitted directed mass at most `2α`. -/
theorem finiteLocalizedSpectral_omittedMass_le_two_alpha
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d))
    (α : ℝ) (htail : finiteLocalizedSubsetTail p S ≤ α) :
    finiteExpectationOmittedDirectedMass
        (finiteLocalizedSpectralSupportGraph S)
        (fun _ : Unit => 1)
        (finiteLocalizedSpectralCoefficient p) ≤
      2 * α :=
  (finiteLocalizedSpectral_omittedMass_le_two_tail
    p hp hpSum S).trans
      (mul_le_mul_of_nonneg_left htail (by norm_num))

/--
**Finite localized spectral-support recurrence law.**

For every nonnegative probability spectrum, every selected nonempty support
`S`, every certified tail bound `α`, every energy list and every resolution,
there is a positive integer recurrence time with exponent exactly
`|S| - 1` and scalar deviation at most

`4α + 2(2π/(Q+1))`.
-/
theorem exists_finiteLocalizedSpectralSupport_recurrence
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (α : ℝ) (htail : finiteLocalizedSubsetTail p S ≤ α)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (S.card - 1) ∧
      finiteLocalizedSpectralDeviation p
          (finiteObserverHamiltonianVertexPhase
            (n : ℝ) energy) ≤
        finiteLocalizedSpectralRecurrenceBudget α Q := by
  obtain ⟨n, hn0, hnQ, hdist⟩ :=
    exists_finiteQuantumExpectation_graph_rateDistortion
      (finiteLocalizedSpectralSupportGraph S)
      (fun _ : Unit => 1)
      (finiteLocalizedSpectralCoefficient p)
      (by intro a; norm_num) energy Q
  have hrank :
      d -
          Nat.card
            (finiteLocalizedSpectralSupportGraph S).ConnectedComponent =
        S.card - 1 := by
    simpa only [Fintype.card_fin] using
      finiteLocalizedSpectralSupportGraph_rank S hS
  rw [hrank] at hnQ
  refine ⟨n, hn0, hnQ, ?_⟩
  have homit :
      finiteExpectationOmittedDirectedMass
          (finiteLocalizedSpectralSupportGraph S)
          (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) ≤
        2 * α :=
    finiteLocalizedSpectral_omittedMass_le_two_alpha
      p hp hpSum S α htail
  have hselected :
      finiteExpectationSelectedDirectedMass
          (finiteLocalizedSpectralSupportGraph S)
          (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) ≤ 1 :=
    finiteLocalizedSpectral_selectedMass_le_one p hp hpSum S
  unfold finiteLocalizedSpectralDeviation
  calc
    finiteQuantumExpectationTotalDeviation
        (fun _ : Unit => 1)
        (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
        (finiteLocalizedSpectralCoefficient p) ≤
      2 * finiteExpectationOmittedDirectedMass
          (finiteLocalizedSpectralSupportGraph S)
          (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) +
        2 * (2 * Real.pi / (Q + 1 : ℝ)) *
          finiteExpectationSelectedDirectedMass
            (finiteLocalizedSpectralSupportGraph S)
            (fun _ : Unit => 1)
            (finiteLocalizedSpectralCoefficient p) :=
      hdist
    _ ≤ 2 * (2 * α) +
        2 * (2 * Real.pi / (Q + 1 : ℝ)) * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left homit (by norm_num))
        (mul_le_mul_of_nonneg_left hselected (by positivity))
    _ = finiteLocalizedSpectralRecurrenceBudget α Q := by
      unfold finiteLocalizedSpectralRecurrenceBudget
      ring

/-- Intrinsic form using the exact probability tail outside `S`. -/
theorem exists_finiteLocalizedSpectralSupport_recurrence_exactTail
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (S.card - 1) ∧
      finiteLocalizedSpectralDeviation p
          (finiteObserverHamiltonianVertexPhase
            (n : ℝ) energy) ≤
        4 * finiteLocalizedSubsetTail p S +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) := by
  simpa only [finiteLocalizedSpectralRecurrenceBudget] using
    exists_finiteLocalizedSpectralSupport_recurrence
      p hp hpSum S hS
      (finiteLocalizedSubsetTail p S) le_rfl energy Q

/--
**Unconditional localized-spectrum escape--return law.**

At the localized recurrence budget, either the scalar history never exits
at any nonnegative time, or some certified exit is followed strictly later
by a return within the same budget.  The post-exit return obeys the same
`|S|-1` deadline after rescaling by the positive guard tick.
-/
theorem finiteLocalizedSpectralSupport_neverExits_or_postExit_return
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (α : ℝ) (htail : finiteLocalizedSubsetTail p S ≤ α)
    (energy : Fin d → ℝ) (Q : ℕ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteLocalizedSpectralDeviation p
          (finiteObserverHamiltonianVertexPhase t energy) ≤
        finiteLocalizedSpectralRecurrenceBudget α Q) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ (Q + 1) ^ (S.card - 1) ∧
      finiteLocalizedSpectralRecurrenceBudget α Q <
        finiteLocalizedSpectralDeviation p
          (finiteObserverHamiltonianVertexPhase
            exitTime energy) ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^ (S.card - 1) : ℕ) : ℝ) *
          (exitTime + guardTime) ∧
      finiteLocalizedSpectralDeviation p
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) ≤
        finiteLocalizedSpectralRecurrenceBudget α Q := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        finiteLocalizedSpectralDeviation p
            (finiteObserverHamiltonianVertexPhase t energy) ≤
          finiteLocalizedSpectralRecurrenceBudget α Q
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    let tick : ℝ := exitTime + guardTime
    have htick0 : 0 < tick := by
      dsimp only [tick]
      linarith
    obtain ⟨n, hn0, hnQ, hreturn⟩ :=
      exists_finiteLocalizedSpectralSupport_recurrence
        p hp hpSum S hS α htail
        (fun i => tick * energy i) Q
    have hnOne : 1 ≤ n :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn0)
    have hpost : exitTime < (n : ℝ) * tick := by
      calc
        exitTime < tick := by
          dsimp only [tick]
          linarith
        _ = (1 : ℝ) * tick := by ring
        _ ≤ (n : ℝ) * tick := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hnOne) htick0.le
    have hdeadline :
        (n : ℝ) * tick ≤
          (((Q + 1) ^ (S.card - 1) : ℕ) : ℝ) * tick :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast hnQ) htick0.le
    have hreturnPhysical :
        finiteLocalizedSpectralDeviation p
            (finiteObserverHamiltonianVertexPhase
              ((n : ℝ) * tick) energy) ≤
          finiteLocalizedSpectralRecurrenceBudget α Q := by
      rw [← finiteObserverHamiltonianVertexPhase_scaledEnergy]
      exact hreturn
    exact
      ⟨exitTime, n, hexitTime, hn0, hnQ, hexit,
        by simpa only [tick] using hpost,
        by simpa only [tick] using hdeadline,
        by simpa only [tick] using hreturnPhysical⟩

end RHTower
