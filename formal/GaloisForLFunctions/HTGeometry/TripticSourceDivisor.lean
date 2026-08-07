import GaloisForLFunctions.HTGeometry.TripticOrbitResidueReciprocity

/-!
# The integral source divisor of a triptic multiplicative class

The zero/pole order of the shift quotient `Y(·+σ)/Y` at a point is the integer

`shiftOrder Y σ w = ord (Y, w + σ) - ord (Y, w)`,

and summing it along a `σ`-orbit gives the `τ`-side orbital divisor of the card.  This file records
the two structural facts that make that assignment a divisor homomorphism: it is additive under
multiplication of sources, and it is invariant under the integer period, so the orbital sum depends
only on the orbit.

Reciprocity (proved separately) makes the `τ`-side and `σ`-side orbital sums equal, so the two
noncommensurable elliptic realizations produce one integer-valued function on orbits.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- The zero/pole order of the shift quotient `Y(·+σ)/Y` at a point. -/
noncomputable def shiftOrder (Y : ℂ → ℂ) (σ : ℂ) (w : ℂ) : ℤ :=
  (meromorphicOrderAt Y (w + σ)).untop₀ - (meromorphicOrderAt Y w).untop₀

/-- **The order of a product is the sum of the orders**, in the untopped integer form available
when neither factor vanishes identically near the point. -/
theorem untop₀_meromorphicOrderAt_mul {Y₁ Y₂ : ℂ → ℂ} {w : ℂ}
    (h₁ : MeromorphicAt Y₁ w) (h₂ : MeromorphicAt Y₂ w)
    (hf₁ : meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : meromorphicOrderAt Y₂ w ≠ ⊤) :
    (meromorphicOrderAt (fun z => Y₁ z * Y₂ z) w).untop₀
      = (meromorphicOrderAt Y₁ w).untop₀ + (meromorphicOrderAt Y₂ w).untop₀ := by
  obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.mp hf₁
  obtain ⟨n₂, hn₂⟩ := WithTop.ne_top_iff_exists.mp hf₂
  have hmul : meromorphicOrderAt (fun z => Y₁ z * Y₂ z) w
      = meromorphicOrderAt Y₁ w + meromorphicOrderAt Y₂ w := meromorphicOrderAt_mul h₁ h₂
  rw [hmul, ← hn₁, ← hn₂]
  simp

/-- **The shift order is additive under multiplication of sources.** -/
theorem shiftOrder_mul {Y₁ Y₂ : ℂ → ℂ} {σ : ℂ}
    (h₁ : MeromorphicOn Y₁ Set.univ) (h₂ : MeromorphicOn Y₂ Set.univ)
    (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤)
    (w : ℂ) :
    shiftOrder (fun z => Y₁ z * Y₂ z) σ w = shiftOrder Y₁ σ w + shiftOrder Y₂ σ w := by
  simp only [shiftOrder]
  rw [untop₀_meromorphicOrderAt_mul (h₁ _ (Set.mem_univ _)) (h₂ _ (Set.mem_univ _))
      (hf₁ _) (hf₂ _),
    untop₀_meromorphicOrderAt_mul (h₁ w (Set.mem_univ w)) (h₂ w (Set.mem_univ w))
      (hf₁ w) (hf₂ w)]
  ring

/-- The order is invariant under a period of the source. -/
theorem untop₀_meromorphicOrderAt_period {Y : ℂ → ℂ} {h : ℂ}
    (hper : ∀ z : ℂ, Y (z + h) = Y z) (w : ℂ) :
    (meromorphicOrderAt Y (w + h)).untop₀ = (meromorphicOrderAt Y w).untop₀ := by
  have hfun : (fun z : ℂ => Y (z + h)) = Y := funext hper
  rw [← meromorphicOrderAt_comp_add Y w h, hfun]

/-- **The shift order is invariant under a period of the source.** -/
theorem shiftOrder_period {Y : ℂ → ℂ} {σ h : ℂ}
    (hper : ∀ z : ℂ, Y (z + h) = Y z) (w : ℂ) :
    shiftOrder Y σ (w + h) = shiftOrder Y σ w := by
  simp only [shiftOrder]
  rw [show w + h + σ = w + σ + h from by ring,
    untop₀_meromorphicOrderAt_period hper (w + σ),
    untop₀_meromorphicOrderAt_period hper w]

end GaloisForLFunctions.HTGeometry
