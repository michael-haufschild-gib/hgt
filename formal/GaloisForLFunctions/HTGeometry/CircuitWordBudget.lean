import GaloisForLFunctions.HTGeometry.CircuitWordApproximationWitnesses

/-!
# Error and length budgets for circuit-word approximations

Two budgeting laws are used by every split-system synthesis argument:

* moving the endpoint by `δ` costs `δ` of tolerance and no gates;
* concatenating two circuits adds their lengths and their tolerances, provided multiplication does
  not expand distance on either side.

The second is the exact content of "prepare the two factors and concatenate their disjoint
circuits": disjointness is not needed as a separate hypothesis, only that composition is
non-expanding, which holds for unitary conjugation and for channel composition alike.

The separation form transfers the same way, which is what turns a synthesis cap into a lower bound
on the first time an endpoint can exceed it.
-/

namespace GaloisForLFunctions.HTGeometry

variable {gate G : Type*} [Monoid G] [PseudoMetricSpace G]

/-- **Error transfer.**  Moving the endpoint by `δ` costs `δ` of tolerance and no gates. -/
theorem HasCircuitWordApproximation.transfer {generator : gate → G} {ε δ : ℝ} {s : ℕ} {x y : G}
    (h : HasCircuitWordApproximation generator ε s x) (hxy : dist x y ≤ δ) :
    HasCircuitWordApproximation generator (ε + δ) s y := by
  obtain ⟨w, hlen, hdist⟩ := h
  refine ⟨w, hlen, ?_⟩
  calc dist (circuitWordValue generator w) y
      ≤ dist (circuitWordValue generator w) x + dist x y := dist_triangle _ _ _
    _ ≤ ε + δ := add_le_add hdist hxy

/-- **Concatenation.**  Composing two approximations adds lengths and tolerances. -/
theorem HasCircuitWordApproximation.mul {generator : gate → G} {ε₁ ε₂ : ℝ} {s₁ s₂ : ℕ} {x y : G}
    (hleft : ∀ a b c : G, dist (c * a) (c * b) ≤ dist a b)
    (hright : ∀ a b c : G, dist (a * c) (b * c) ≤ dist a b)
    (hx : HasCircuitWordApproximation generator ε₁ s₁ x)
    (hy : HasCircuitWordApproximation generator ε₂ s₂ y) :
    HasCircuitWordApproximation generator (ε₁ + ε₂) (s₁ + s₂) (x * y) := by
  obtain ⟨w₁, hlen₁, hdist₁⟩ := hx
  obtain ⟨w₂, hlen₂, hdist₂⟩ := hy
  refine ⟨w₁ ++ w₂, ?_, ?_⟩
  · rw [List.length_append]
    exact Nat.add_le_add hlen₁ hlen₂
  · rw [circuitWordValue_append]
    set V₁ := circuitWordValue generator w₁
    set V₂ := circuitWordValue generator w₂
    calc dist (V₁ * V₂) (x * y)
        ≤ dist (V₁ * V₂) (x * V₂) + dist (x * V₂) (x * y) := dist_triangle _ _ _
      _ ≤ ε₁ + ε₂ :=
          add_le_add (le_trans (hright V₁ x V₂) hdist₁) (le_trans (hleft V₂ y x) hdist₂)

/-- **Separation transfer.**  A separated endpoint stays separated after a small move, with the
separation radius reduced by exactly the displacement. -/
theorem CircuitWordSeparated.transfer {generator : gate → G} {ε δ : ℝ} {s : ℕ} {x y : G}
    (h : CircuitWordSeparated generator ε s x) (hxy : dist x y ≤ δ) :
    CircuitWordSeparated generator (ε - δ) s y := by
  intro w hlen
  have hsep := h w hlen
  have htri : dist (circuitWordValue generator w) x
      ≤ dist (circuitWordValue generator w) y + dist y x := dist_triangle _ _ _
  have hyx : dist y x ≤ δ := by rwa [dist_comm] at hxy
  linarith

/-- **The synthesis cap is a lower bound on onset time.**  If the endpoint is separated at budget
`s` and radius `ε`, then no endpoint within `ε` of it is approximable at that budget. -/
theorem not_hasCircuitWordApproximation_of_separated {generator : gate → G} {ε δ : ℝ} {s : ℕ}
    {x y : G} (h : CircuitWordSeparated generator ε s x) (hxy : dist x y ≤ δ) :
    ¬ HasCircuitWordApproximation generator (ε - δ) s y := by
  rintro ⟨w, hlen, hdist⟩
  exact absurd hdist (not_le.mpr (h.transfer hxy w hlen))

end GaloisForLFunctions.HTGeometry
