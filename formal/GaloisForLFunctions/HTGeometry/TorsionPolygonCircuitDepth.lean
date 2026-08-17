import GaloisForLFunctions.HTGeometry.TorsionCapAnchoredCount
import GaloisForLFunctions.RHTower.LocalCircuitTraceCapacity

/-!
# Circuit-depth specialization of the recurrence polygon

Taking the target dictionary to be the endpoints reachable by circuits of depth at most `s` turns
target hardness into a lower bound on robust circuit complexity: a state farther than `δ` from every
depth-`s` endpoint cannot be prepared at depth `s` or less.

The dictionary size is paid before the recurrence time is chosen.  The local-circuit heap capacity
law bounds it by `(s+1) * choose (M+s-1) s * 2^{Δs}`, and once that quantity satisfies the torsion
cap condition, every one of the `k-1` equally spaced interior slices of arbitrarily late recurrence
cycles has robust circuit complexity greater than `s`.
-/

open Real RHTower

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section CircuitDepth

variable {D : ℕ}

/-- No endpoint of the depth-`s` dictionary comes within `δ` of the state. -/
def DepthHard (dict : ℕ → Finset (EuclideanSpace ℂ (Fin D))) (δ : ℝ) (s : ℕ)
    (ψ : EuclideanSpace ℂ (Fin D)) : Prop :=
  ∀ y ∈ dict s, δ < pureStateTraceDistance ψ y

/-- The robust circuit complexity: the least depth whose dictionary reaches the state to accuracy
`δ`, and `⊤` if no depth does. -/
def robustCircuitComplexity (dict : ℕ → Finset (EuclideanSpace ℂ (Fin D))) (δ : ℝ)
    (ψ : EuclideanSpace ℂ (Fin D)) : ℕ∞ :=
  sInf ((fun r : ℕ => (r : ℕ∞)) ''
    {r : ℕ | ∃ y ∈ dict r, pureStateTraceDistance ψ y ≤ δ})

/-- Depth-`s` hardness is exactly a robust complexity strictly above `s`. -/
theorem lt_robustCircuitComplexity_of_depthHard
    {dict : ℕ → Finset (EuclideanSpace ℂ (Fin D))} (hmono : Monotone dict) {δ : ℝ} {s : ℕ}
    {ψ : EuclideanSpace ℂ (Fin D)} (h : DepthHard dict δ s ψ) :
    (s : ℕ∞) < robustCircuitComplexity dict δ ψ := by
  have hle : ((s + 1 : ℕ) : ℕ∞) ≤ robustCircuitComplexity dict δ ψ := by
    refine le_sInf ?_
    rintro x ⟨r, ⟨y, hy, hyd⟩, rfl⟩
    show ((s + 1 : ℕ) : ℕ∞) ≤ (r : ℕ∞)
    have hsr : s < r := by
      rcases lt_or_ge s r with h' | h'
      · exact h'
      · exact absurd hyd (not_le.mpr (h y (hmono h' hy)))
    exact_mod_cast Nat.succ_le_of_lt hsr
  refine lt_of_lt_of_le ?_ hle
  exact_mod_cast Nat.lt_succ_self s

end CircuitDepth

section Specialization

variable {d k : ℕ}

/-- **`(24)` implies `(25)`.**  Once the heap-capacity bound on the depth-`s` dictionary satisfies
the torsion cap condition, there are arbitrarily late recurrence cycles all of whose `k-1` equally
spaced interior rational slices have robust circuit complexity greater than `s`. -/
theorem exists_late_recurrence_depthHard [NeZero k] (hk : k.Prime)
    (E : Fin (d + 1) → ℝ) (hind : LinearIndependent ℚ (projectiveGapPacket E))
    (dict : ℕ → Finset (EuclideanSpace ℂ (Fin (d + 1)))) (hmono : Monotone dict)
    (s M Δ : ℕ) (hunit : ∀ y ∈ dict s, ‖y‖ = 1)
    (hcap : (dict s).card ≤ (s + 1) * (M + s - 1).choose s * 2 ^ (Δ * s))
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ2 : 2 * δ ^ 2 ≤ 1)
    (h24 : 4 * ((k : ℝ) - 1) * (((s + 1) * (M + s - 1).choose s * 2 ^ (Δ * s) : ℕ) : ℝ)
      * Real.exp (-((1 - 4 * δ ^ 2) / 4) * ((d : ℝ) + 1)) < 1)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ R : ℝ, A < R ∧
      pureStateTraceDistance (flowRay E R) (flowRay E 0) < ρ ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 →
        (s : ℕ∞) < robustCircuitComplexity dict δ (flowRay E ((j : ℝ) * R / (k : ℝ))) := by
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk.one_lt
  have hcapR : ((dict s).card : ℝ)
      ≤ (((s + 1) * (M + s - 1).choose s * 2 ^ (Δ * s) : ℕ) : ℝ) := by exact_mod_cast hcap
  have h13 : 4 * ((k : ℝ) - 1) * ((dict s).card : ℝ)
      * Real.exp (-((1 - 4 * δ ^ 2) / 4) * ((d : ℝ) + 1)) < 1 := by
    refine lt_of_le_of_lt ?_ h24
    have hc : (0 : ℝ) ≤ 4 * ((k : ℝ) - 1) * Real.exp (-((1 - 4 * δ ^ 2) / 4) * ((d : ℝ) + 1)) := by
      have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      positivity
    calc 4 * ((k : ℝ) - 1) * ((dict s).card : ℝ)
          * Real.exp (-((1 - 4 * δ ^ 2) / 4) * ((d : ℝ) + 1))
        = (4 * ((k : ℝ) - 1) * Real.exp (-((1 - 4 * δ ^ 2) / 4) * ((d : ℝ) + 1)))
            * ((dict s).card : ℝ) := by ring
      _ ≤ (4 * ((k : ℝ) - 1) * Real.exp (-((1 - 4 * δ ^ 2) / 4) * ((d : ℝ) + 1)))
            * (((s + 1) * (M + s - 1).choose s * 2 ^ (Δ * s) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hcapR hc
      _ = 4 * ((k : ℝ) - 1) * (((s + 1) * (M + s - 1).choose s * 2 ^ (Δ * s) : ℕ) : ℝ)
            * Real.exp (-((1 - 4 * δ ^ 2) / 4) * ((d : ℝ) + 1)) := by ring
  obtain ⟨R, hRA, hrec, hhard⟩ :=
    exists_late_recurrence_hard_polygon_of_cap hk E hind (dict s) hunit hδ hδ2 h13 hρ A
  exact ⟨R, hRA, hrec, fun j hj1 hj2 =>
    lt_robustCircuitComplexity_of_depthHard hmono (fun y hy => hhard j hj1 hj2 y hy)⟩

end Specialization

end

end GaloisForLFunctions.HTGeometry
