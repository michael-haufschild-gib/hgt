import GaloisForLFunctions.HTGeometry.QuadrantHolomorphic
import GaloisForLFunctions.HTGeometry.LocallyConvexDenseOfVanishingDual

/-!
# The finite-support joint graph of prime fields and Euler tangents

The joint graph pairs a finitely supported prime coefficient field with the holomorphic function on
the critical quadrant it produces, the generator at `p` being the weighted coordinate mass together
with the symmetrised Euler unit tangent `u_p`.

Its closure in the product is the whole product, and the two factors contribute very differently to
that statement.  The coefficient factor is settled outright: an annihilating functional is forced to
vanish there by the single-support argument in `ℓ¹`.  What the statement really rests on is the
second factor, where the annihilating analytic functional has to be shown zero — and once it is,
the graph relation transfers the vanishing back to the first factor for free.

* `HTGeometry.primeQuadrantGen`, `HTGeometry.primeQuadrantGraph`;
* `HTGeometry.topologicalClosure_primeQuadrantGraph_eq_top`.
-/

noncomputable section

namespace HTGeometry

/-- The Euler unit tangent at a prime, as an element of the quadrant's holomorphic space. -/
def eulerTangentElement (p : Nat.Primes) : holoQuadrant :=
  ⟨feEulerTangentMap p, feEulerTangentMap_mem_holoQuadrant p⟩

/-- The joint graph generator at a prime: the weighted coordinate mass paired with the Euler unit
tangent it produces. -/
def primeQuadrantGen (p : Nat.Primes) : PrimeTangent × holoQuadrant :=
  (primeTangentGen p, eulerTangentElement p)

/-- The finite-support joint graph. -/
def primeQuadrantGraph : Submodule ℝ (PrimeTangent × holoQuadrant) :=
  Submodule.span ℝ (Set.range primeQuadrantGen)

/-- **The joint graph is dense in the product once the analytic factor is settled.**

The coefficient factor needs no hypothesis: the graph relation turns the vanishing of the analytic
functional into the vanishing of the coefficient functional on every weighted coordinate mass, and
the single-support argument in `ℓ¹` finishes it. -/
theorem topologicalClosure_primeQuadrantGraph_eq_top
    (helim : ∀ (f₁ : PrimeTangent →L[ℝ] ℝ) (f₂ : holoQuadrant →L[ℝ] ℝ),
      (∀ p : Nat.Primes, f₁ (primeTangentGen p) + f₂ (eulerTangentElement p) = 0) →
      ∀ y : holoQuadrant, f₂ y = 0) :
    primeQuadrantGraph.topologicalClosure = ⊤ := by
  refine topologicalClosure_span_eq_top_of_pair_dual_lcs primeTangentGen eulerTangentElement ?_
  intro f₁ f₂ hgraph
  have hf₂ : ∀ y : holoQuadrant, f₂ y = 0 := helim f₁ f₂ hgraph
  have hf₁gen : ∀ p : Nat.Primes, f₁ (primeTangentGen p) = 0 := by
    intro p
    have h := hgraph p
    rw [hf₂ (eulerTangentElement p), add_zero] at h
    exact h
  exact ⟨primeTangent_eq_zero_of_forall_gen f₁ hf₁gen, hf₂⟩

end HTGeometry
