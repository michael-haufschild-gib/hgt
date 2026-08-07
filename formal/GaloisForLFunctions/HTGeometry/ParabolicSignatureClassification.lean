import GaloisForLFunctions.HTGeometry.EuclideanConeSignature
import GaloisForLFunctions.HTGeometry.ParabolicOrbifoldTwelveCharge

/-!
# The six parabolic sphere signatures are exactly the Euclidean solutions

The parabolic condition on a sphere orbifold with `c` cusps and cone orders `ν₁ ≤ … ≤ ν_n` is

`c + ∑ (1 - 1/νᵢ) = 2`.

Every one of the six recorded signatures satisfies it, and conversely every solution is one of the
six.  So the enumerated datatype is not a convention: it is the complete solution set.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Each recorded signature has vanishing orbifold Euler characteristic. -/
theorem ParabolicSphereSignature.euclidean (s : ParabolicSphereSignature) :
    (s.cuspCount : ℚ)
      + (s.finiteConeOrders.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum = 2 := by
  cases s <;>
    simp [ParabolicSphereSignature.cuspCount, ParabolicSphereSignature.finiteConeOrders] <;>
    norm_num

/-- Each recorded signature has weakly increasing cone orders, all at least two. -/
theorem ParabolicSphereSignature.coneOrders_spec (s : ParabolicSphereSignature) :
    s.finiteConeOrders.Pairwise (· ≤ ·) ∧ ∀ ν ∈ s.finiteConeOrders, 2 ≤ ν := by
  cases s <;>
    refine ⟨?_, ?_⟩ <;>
    simp [ParabolicSphereSignature.finiteConeOrders]

/-- **The classification is exact.**  Every parabolic sphere datum is one of the six recorded
signatures. -/
theorem exists_parabolicSphereSignature (c : ℕ) (l : List ℕ)
    (hsorted : l.Pairwise (· ≤ ·)) (h2 : ∀ ν ∈ l, 2 ≤ ν)
    (heq : (c : ℚ) + (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum = 2) :
    ∃ s : ParabolicSphereSignature, s.cuspCount = c ∧ s.finiteConeOrders = l := by
  rcases parabolic_signature_classification c l hsorted h2 heq with
    ⟨hc, hl⟩ | ⟨hc, hl⟩ | ⟨hc, hl⟩ | ⟨hc, hl⟩ | ⟨hc, hl⟩ | ⟨hc, hl⟩
  · exact ⟨.twoCusps, by simp [ParabolicSphereSignature.cuspCount, hc],
      by simp [ParabolicSphereSignature.finiteConeOrders, hl]⟩
  · exact ⟨.twoTwosCusp, by simp [ParabolicSphereSignature.cuspCount, hc],
      by simp [ParabolicSphereSignature.finiteConeOrders, hl]⟩
  · exact ⟨.fourTwos, by simp [ParabolicSphereSignature.cuspCount, hc],
      by simp [ParabolicSphereSignature.finiteConeOrders, hl]⟩
  · exact ⟨.twoThreeSix, by simp [ParabolicSphereSignature.cuspCount, hc],
      by simp [ParabolicSphereSignature.finiteConeOrders, hl]⟩
  · exact ⟨.twoFourFour, by simp [ParabolicSphereSignature.cuspCount, hc],
      by simp [ParabolicSphereSignature.finiteConeOrders, hl]⟩
  · exact ⟨.threeThrees, by simp [ParabolicSphereSignature.cuspCount, hc],
      by simp [ParabolicSphereSignature.finiteConeOrders, hl]⟩

/-- **The six signatures are exactly the parabolic sphere data.** -/
theorem parabolicSphereSignature_iff (c : ℕ) (l : List ℕ) :
    (l.Pairwise (· ≤ ·) ∧ (∀ ν ∈ l, 2 ≤ ν) ∧
        (c : ℚ) + (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum = 2)
      ↔ ∃ s : ParabolicSphereSignature, s.cuspCount = c ∧ s.finiteConeOrders = l := by
  constructor
  · rintro ⟨hsorted, h2, heq⟩
    exact exists_parabolicSphereSignature c l hsorted h2 heq
  · rintro ⟨s, hc, hl⟩
    subst hc
    subst hl
    obtain ⟨hsorted, h2⟩ := s.coneOrders_spec
    exact ⟨hsorted, h2, s.euclidean⟩

end GaloisForLFunctions.HTGeometry
