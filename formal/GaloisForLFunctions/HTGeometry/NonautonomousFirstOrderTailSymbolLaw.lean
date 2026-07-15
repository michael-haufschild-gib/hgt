import GaloisForLFunctions.HTGeometry.NonautonomousFirstOrderTailSymbol

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A phase-compatible observable is an explicit preimage through every finite protocol prefix. -/
theorem forwardPrefix_phaseChain
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (Q : ℕ → F)
    (hQ : ∀ i, φ i (Q (i + 1)) = Q i) (i n : ℕ) :
    forwardPrefix φ i n (Q (i + n)) = Q i := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [forwardPrefix_succ_apply]
      rw [show i + (n + 1) = (i + 1) + n by omega, ih (i + 1), hQ i]

/-- Every phase-compatible tensor observable belongs to the nonautonomous tail at its phase. -/
theorem phaseChain_mem_nonautonomousTail
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (Q : ℕ → F)
    (hQ : ∀ i, φ i (Q (i + 1)) = Q i) (i : ℕ) :
    Q i ∈ nonautonomousTail φ i := by
  rw [mem_nonautonomousTail_iff]
  intro n
  exact ⟨Q (i + n), forwardPrefix_phaseChain φ Q hQ i n⟩

/-- A transcendental compatible tensor chain makes every phase tail nontrivial. -/
theorem nonautonomousTail_ne_bot_of_phaseChain_transcendental
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (Q : ℕ → F)
    (hQ : ∀ i, φ i (Q (i + 1)) = Q i) (i : ℕ)
    (htrans : Transcendental K (Q i)) :
    nonautonomousTail φ i ≠ ⊥ := by
  intro hbot
  have hmem : Q i ∈ (⊥ : IntermediateField K F) := by
    rw [← hbot]
    exact phaseChain_mem_nonautonomousTail φ Q hQ i
  rw [IntermediateField.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  apply htrans
  rw [← hc]
  exact isAlgebraic_algebraMap (R := K) (A := F) c

/-- Pullback order of a positive tensor at a point of ramification index `e`. -/
def positiveTensorPullbackOrder (weight ramification terminalOrder : ℕ) : ℕ :=
  ramification * terminalOrder + weight * (ramification - 1)

/-- Pullback order dominates the sheet-multiplicity contribution of the terminal zero. -/
theorem ramification_mul_terminalOrder_le_positiveTensorPullbackOrder
    (weight ramification terminalOrder : ℕ) :
    ramification * terminalOrder ≤
      positiveTensorPullbackOrder weight ramification terminalOrder := by
  simp [positiveTensorPullbackOrder]

/-- The shifted tensor order is multiplied exactly by the ramification index. -/
theorem positiveTensorPullbackOrder_add_weight
    (weight ramification terminalOrder : ℕ) (hramification : 0 < ramification) :
    positiveTensorPullbackOrder weight ramification terminalOrder + weight =
      ramification * (terminalOrder + weight) := by
  have he : ramification - 1 + 1 = ramification :=
    Nat.sub_add_cancel hramification
  simp only [positiveTensorPullbackOrder]
  calc
    ramification * terminalOrder + weight * (ramification - 1) + weight =
        ramification * terminalOrder + weight * ((ramification - 1) + 1) := by
          simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    _ = ramification * terminalOrder + weight * ramification := by rw [he]
    _ = ramification * (terminalOrder + weight) := by ring

/-- Summing the local pullback inequality over all terminal zeros gives the exact global
degree-amplified defect inequality.  The outer index labels disjoint terminal fibres. -/
theorem pullbackZeroMultiplicity_global
    {α β : Type*} (zeros : Finset β) (fiber : β → Finset α)
    (ramification : β → α → ℕ) (sourceMultiplicity : β → α → ℕ)
    (terminalMultiplicity : β → ℕ) (degree : ℕ)
    (hdegree : ∀ y ∈ zeros, ∑ x ∈ fiber y, ramification y x = degree)
    (hlocal : ∀ y ∈ zeros, ∀ x ∈ fiber y,
      ramification y x * terminalMultiplicity y ≤ sourceMultiplicity y x) :
    degree * (∑ y ∈ zeros, terminalMultiplicity y) ≤
      ∑ y ∈ zeros, ∑ x ∈ fiber y, sourceMultiplicity y x := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun y hy =>
    pullbackZeroMultiplicity_fiber (fiber y) (ramification y) (sourceMultiplicity y)
      (terminalMultiplicity y) degree (hdegree y hy) (hlocal y hy)

/-- A fixed source zero-divisor budget bounds the terminal zero divisor by prefix degree. -/
theorem terminalZeroDivisor_degree_budget
    {α β : Type*} (zeros : Finset β) (fiber : β → Finset α)
    (ramification : β → α → ℕ) (sourceMultiplicity : β → α → ℕ)
    (terminalMultiplicity : β → ℕ) (degree sourceBudget : ℕ)
    (hdegree : ∀ y ∈ zeros, ∑ x ∈ fiber y, ramification y x = degree)
    (hlocal : ∀ y ∈ zeros, ∀ x ∈ fiber y,
      ramification y x * terminalMultiplicity y ≤ sourceMultiplicity y x)
    (hsource : (∑ y ∈ zeros, ∑ x ∈ fiber y, sourceMultiplicity y x) ≤ sourceBudget) :
    degree * (∑ y ∈ zeros, terminalMultiplicity y) ≤ sourceBudget :=
  (pullbackZeroMultiplicity_global zeros fiber ramification sourceMultiplicity
    terminalMultiplicity degree hdegree hlocal).trans hsource

/-- Once the prefix degree exceeds the whole source zero-divisor budget, the terminal tensor has
no zeros. -/
theorem terminalZeroDivisor_eq_zero_of_sourceBudget_lt_degree
    {α β : Type*} (zeros : Finset β) (fiber : β → Finset α)
    (ramification : β → α → ℕ) (sourceMultiplicity : β → α → ℕ)
    (terminalMultiplicity : β → ℕ) (degree sourceBudget : ℕ)
    (hdegree : ∀ y ∈ zeros, ∑ x ∈ fiber y, ramification y x = degree)
    (hlocal : ∀ y ∈ zeros, ∀ x ∈ fiber y,
      ramification y x * terminalMultiplicity y ≤ sourceMultiplicity y x)
    (hsource : (∑ y ∈ zeros, ∑ x ∈ fiber y, sourceMultiplicity y x) ≤ sourceBudget)
    (hexpanding : sourceBudget < degree) :
    ∑ y ∈ zeros, terminalMultiplicity y = 0 := by
  apply futureTensorDefect_eq_zero_of_degree_gt sourceBudget
    (∑ y ∈ zeros, terminalMultiplicity y) degree
  · exact terminalZeroDivisor_degree_budget zeros fiber ramification sourceMultiplicity
      terminalMultiplicity degree sourceBudget hdegree hlocal hsource
  · exact hexpanding

end

end GaloisForLFunctions.HTGeometry
