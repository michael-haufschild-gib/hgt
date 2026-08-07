import GaloisForLFunctions.HTGeometry.AutonomousWordComplexityConeLaw

/-!
# Circuit-word anchor rephasing law

An inverse-closed gate alphabet absorbs arbitrary anchor rephasing into one
larger bounded-word dictionary.  If an anchor and a target have bounded-word
approximations, then the anchor-inverse times the target has the sum of their
word budgets and the sum of their errors.  Thus even a continuous adaptive
anchor family creates no target witnesses outside the enlarged finite word
class.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Reverse a gate word and replace every gate by its designated inverse. -/
def circuitInverseWord {gate : Type*}
    (inverseGate : gate → gate) : List gate → List gate
  | [] => []
  | g :: w => circuitInverseWord inverseGate w ++ [inverseGate g]

@[simp] theorem length_circuitInverseWord
    {gate : Type*} (inverseGate : gate → gate) (w : List gate) :
    (circuitInverseWord inverseGate w).length = w.length := by
  induction w with
  | nil => simp [circuitInverseWord]
  | cons g w ih => simp [circuitInverseWord, ih]

/-- An inverse-closed generator evaluates the reversed inverse word to the
group inverse of the original word value. -/
theorem circuitWordValue_circuitInverseWord
    {gate G : Type*} [Group G]
    (generator : gate → G) (inverseGate : gate → gate)
    (hinverse : ∀ g, generator (inverseGate g) = (generator g)⁻¹)
    (w : List gate) :
    circuitWordValue generator (circuitInverseWord inverseGate w) =
      (circuitWordValue generator w)⁻¹ := by
  induction w with
  | nil => simp [circuitInverseWord, circuitWordValue]
  | cons g w ih =>
      rw [circuitInverseWord, circuitWordValue_append, ih]
      simp [circuitWordValue, hinverse]

/-- **Circuit-word anchor rephasing.**  Approximation tubes are closed under
inverse-left translation, with additive word budget and additive error. -/
theorem HasCircuitWordApproximation.inv_mul_of_inverseClosed
    {gate G : Type*} [Group G] [PseudoMetricSpace G]
    (generator : gate → G) (inverseGate : gate → gate)
    (hinverse : ∀ g, generator (inverseGate g) = (generator g)⁻¹)
    (hmul : ∀ a₁ a₂ b₁ b₂ : G,
      dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂)
    (hinvDist : ∀ a b : G, dist a⁻¹ b⁻¹ = dist a b)
    {epsilonX epsilonY : ℝ} {sX sY : ℕ} {x y : G}
    (hx : HasCircuitWordApproximation generator epsilonX sX x)
    (hy : HasCircuitWordApproximation generator epsilonY sY y) :
    HasCircuitWordApproximation generator (epsilonX + epsilonY) (sX + sY)
      (x⁻¹ * y) := by
  obtain ⟨wx, hwxLength, hwxDist⟩ := hx
  obtain ⟨wy, hwyLength, hwyDist⟩ := hy
  refine ⟨circuitInverseWord inverseGate wx ++ wy, ?_, ?_⟩
  · rw [List.length_append, length_circuitInverseWord]
    omega
  · rw [circuitWordValue_append,
      circuitWordValue_circuitInverseWord generator inverseGate hinverse]
    exact (hmul _ _ _ _).trans <| by
      rw [hinvDist]
      exact add_le_add hwxDist hwyDist

/-- Every member of an arbitrary anchor/target family is absorbed into the
same enlarged bounded-word approximation tube.  No finiteness assumption on
the anchor family is needed. -/
theorem hasCircuitWordApproximation_anchorRephased_family
    {gate G W : Type*} [Group G] [PseudoMetricSpace G]
    (generator : gate → G) (inverseGate : gate → gate)
    (hinverse : ∀ g, generator (inverseGate g) = (generator g)⁻¹)
    (hmul : ∀ a₁ a₂ b₁ b₂ : G,
      dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂)
    (hinvDist : ∀ a b : G, dist a⁻¹ b⁻¹ = dist a b)
    (flow : ℝ → G) (anchors : Set ℝ) (target : W → G)
    {delta epsilon : ℝ} {r s : ℕ}
    (hflow : ∀ u ∈ anchors,
      HasCircuitWordApproximation generator delta r (flow u))
    (htarget : ∀ w,
      HasCircuitWordApproximation generator epsilon s (target w)) :
    ∀ u ∈ anchors, ∀ w,
      HasCircuitWordApproximation generator (delta + epsilon) (r + s)
        ((flow u)⁻¹ * target w) := by
  intro u hu w
  exact (hflow u hu).inv_mul_of_inverseClosed generator inverseGate
    hinverse hmul hinvDist (htarget w)

end GaloisForLFunctions.HTGeometry
