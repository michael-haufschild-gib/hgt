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


/-- The parabolic third of the triangle trichotomy, stated with reciprocals. -/
theorem parabolic_triple_classification {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (heq : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ = 1) :
    (a = 2 ∧ b = 3 ∧ c = 6) ∨ (a = 2 ∧ b = 4 ∧ c = 4) ∨ (a = 3 ∧ b = 3 ∧ c = 3) :=
  euclidean_cone_triple ha hab hbc (by simpa [one_div] using heq)


/-- Pulling the tensor weight out of a pole-order sum. -/
theorem sum_map_const_mul (l : List ℕ) (lam : ℚ) :
    (l.map (fun ν : ℕ => lam * (1 - 1 / (ν : ℚ)))).sum
      = lam * (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- **From the pole-order budget of an `ℓ`-differential to the parabolic equation.**  If the poles
of a nonzero `ℓ`-differential on the sphere have orders `ℓ(1 - 1/ν_y)` at the cone points and `ℓ` at
the cusps, and the total pole order is `2ℓ`, then the signature is parabolic. -/
theorem parabolic_of_pole_orders {lam : ℚ} (hlam : lam ≠ 0) (c : ℕ) (l : List ℕ)
    (hsum : lam * (c : ℚ) + (l.map (fun ν : ℕ => lam * (1 - 1 / (ν : ℚ)))).sum = 2 * lam) :
    (c : ℚ) + (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum = 2 := by
  rw [sum_map_const_mul] at hsum
  have h : lam * ((c : ℚ) + (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum) = lam * 2 := by
    linarith
  exact mul_left_cancel₀ hlam h

/-- **The pole-order budget of a transported tensor forces one of the six signatures.** -/
theorem parabolicSphereSignature_of_pole_orders {lam : ℚ} (hlam : lam ≠ 0) (c : ℕ) (l : List ℕ)
    (hsorted : l.Pairwise (· ≤ ·)) (h2 : ∀ ν ∈ l, 2 ≤ ν)
    (hsum : lam * (c : ℚ) + (l.map (fun ν : ℕ => lam * (1 - 1 / (ν : ℚ)))).sum = 2 * lam) :
    ∃ s : ParabolicSphereSignature, s.cuspCount = c ∧ s.finiteConeOrders = l :=
  exists_parabolicSphereSignature c l hsorted h2 (parabolic_of_pole_orders hlam c l hsum)

end GaloisForLFunctions.HTGeometry
