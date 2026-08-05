import GaloisForLFunctions.HTGeometry.AutonomousWordComplexityConeLaw

/-!
# Circuit-word approximations exist

The word-complexity cone assumes that an endpoint is reachable by a gate word of bounded length up
to a tolerance.  Every value of a gate word of length at most `s` has the approximation exactly, at
tolerance zero, so the unit is approximable at every budget through the empty word.  The relation
is monotone in both the budget and the tolerance, which is what a cone argument consumes.
-/

namespace GaloisForLFunctions.HTGeometry

variable {gate G : Type*} [Monoid G] [PseudoMetricSpace G]

/-- **A word value is approximated by itself.** -/
theorem hasCircuitWordApproximation_circuitWordValue (generator : gate → G) {ε : ℝ}
    (hε : 0 ≤ ε) {s : ℕ} {w : List gate} (hw : w.length ≤ s) :
    HasCircuitWordApproximation generator ε s (circuitWordValue generator w) :=
  ⟨w, hw, by simpa using hε⟩

/-- The unit is approximable at every budget, through the empty word. -/
theorem hasCircuitWordApproximation_one (generator : gate → G) {ε : ℝ} (hε : 0 ≤ ε) (s : ℕ) :
    HasCircuitWordApproximation generator ε s (1 : G) := by
  have hval : circuitWordValue generator [] = (1 : G) := by
    rw [circuitWordValue]
    simp
  rw [← hval]
  exact hasCircuitWordApproximation_circuitWordValue generator hε (Nat.zero_le s)

/-- Approximability is monotone in the gate budget. -/
theorem HasCircuitWordApproximation.mono_length {generator : gate → G} {ε : ℝ} {s s' : ℕ} {x : G}
    (h : HasCircuitWordApproximation generator ε s x) (hs : s ≤ s') :
    HasCircuitWordApproximation generator ε s' x := by
  obtain ⟨w, hlen, hdist⟩ := h
  exact ⟨w, hlen.trans hs, hdist⟩

/-- Approximability is monotone in the tolerance. -/
theorem HasCircuitWordApproximation.mono_tolerance {generator : gate → G} {ε ε' : ℝ} {s : ℕ}
    {x : G} (h : HasCircuitWordApproximation generator ε s x) (hε : ε ≤ ε') :
    HasCircuitWordApproximation generator ε' s x := by
  obtain ⟨w, hlen, hdist⟩ := h
  exact ⟨w, hlen, hdist.trans hε⟩

end GaloisForLFunctions.HTGeometry
