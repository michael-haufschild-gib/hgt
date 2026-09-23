import GaloisForLFunctions.RHTower.RouteEIncidenceSwitchParityRigidity

/-!
# Route E three-toggle common-neighbor rigidity

Odd prime-support distance is exactly what reverses the Möbius sign.  This file opens the first
direct move class surviving the one-toggle Hall obstruction and the two-by-two switch no-go:
supports at symmetric-difference distance three, including both `0 ↔ 3` and `1 ↔ 2` moves.

The new collision law is exact.  If one support is distance three from two sources, the source
separation equals twice the overlap between its first toggle set and the source difference.
Consequently common neighbors occur only at source separations zero, two, four, or six.  At
separation six the complete common-neighbor fibre is precisely the image of the three-subsets of
the six changed coordinates, and therefore has cardinality `Nat.choose 6 3`.

This is unsigned source geometry, not a Hall estimate.  Separations two and four still have
dimension-sensitive collision families, and a multiplicative cutoff can destroy full-cube row
regularity.  The remaining Route E problem is a family-level coefficient-one expansion theorem
for the thresholded graph, with the same interval and seam compatibility needed downstream.
-/

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius symmDiff

noncomputable section

namespace RHTower

/-- The full prime-support move class at Hamming distance three. -/
def routeEThreeToggleAdjacent (S T : Finset ℕ) : Prop :=
  (S ∆ T).card = 3

/-- Cancelling the same support from two symmetric differences leaves the endpoint difference. -/
theorem routeE_symmDiff_symmDiff_left (S T U : Finset ℕ) :
    (S ∆ T) ∆ (S ∆ U) = T ∆ U := by
  ext p
  simp only [mem_symmDiff]
  tauto

/-- Toggling the same finite support twice is the identity. -/
theorem routeE_symmDiff_self_left (S A : Finset ℕ) :
    S ∆ (S ∆ A) = A := by
  ext p
  simp only [mem_symmDiff]
  tauto

/-- Three symmetric differences may be reassociated and reordered coordinatewise. -/
theorem routeE_symmDiff_three_reassociate (S U A : Finset ℕ) :
    U ∆ (S ∆ A) = A ∆ (S ∆ U) := by
  ext p
  simp only [mem_symmDiff]
  tauto

/-- Toggling from a fixed support is injective. -/
theorem routeE_symmDiff_left_injective (S : Finset ℕ) :
    Function.Injective fun A : Finset ℕ => S ∆ A := by
  intro A B h
  have h' := congrArg (fun X : Finset ℕ => S ∆ X) h
  simpa only [routeE_symmDiff_self_left] using h'

/-- **Every distance-three edge reverses Möbius sign.** -/
theorem routeE_threeToggle_reverses_moebius
    {S T : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (hST : routeEThreeToggleAdjacent S T) :
    (μ (∏ p ∈ T, p) : ℤ) = -(μ (∏ p ∈ S, p) : ℤ) := by
  rw [moebius_primeProducts_eq_neg_iff_odd_symmDiff hS hT]
  exact ⟨1, hST⟩

/-- **Exact common-neighbor overlap law.** If `T` is a distance-three neighbor of both `S` and
`U`, then the source distance is twice the part of the `S → T` toggle set lying in `S ∆ U`. -/
theorem routeE_threeToggle_common_neighbor_exact_overlap
    {S U T : Finset ℕ}
    (hST : routeEThreeToggleAdjacent S T)
    (hUT : routeEThreeToggleAdjacent U T) :
    (S ∆ U).card = 2 * ((S ∆ T) ∩ (S ∆ U)).card := by
  have hsymm : ((S ∆ T) ∆ (S ∆ U)).card = 3 := by
    rw [routeE_symmDiff_symmDiff_left]
    simpa only [routeEThreeToggleAdjacent, symmDiff_comm] using hUT
  have hcard := card_add_eq_card_symmDiff_add_twice_inter_routeEIncidenceSwitchParityRigidity (S ∆ T) (S ∆ U)
  rw [hST] at hcard
  rw [hsymm] at hcard
  omega

/-- Common distance-three neighbors force even source separation. -/
theorem routeE_threeToggle_common_neighbor_even_separation
    {S U T : Finset ℕ}
    (hST : routeEThreeToggleAdjacent S T)
    (hUT : routeEThreeToggleAdjacent U T) :
    Even (S ∆ U).card := by
  exact ⟨((S ∆ T) ∩ (S ∆ U)).card,
    by simpa [two_mul] using routeE_threeToggle_common_neighbor_exact_overlap hST hUT⟩

/-- Common distance-three neighbors force source separation at most six. -/
theorem routeE_threeToggle_common_neighbor_separation_le_six
    {S U T : Finset ℕ}
    (hST : routeEThreeToggleAdjacent S T)
    (hUT : routeEThreeToggleAdjacent U T) :
    (S ∆ U).card ≤ 6 := by
  rw [routeE_threeToggle_common_neighbor_exact_overlap hST hUT]
  have hinter : ((S ∆ T) ∩ (S ∆ U)).card ≤ (S ∆ T).card :=
    card_le_card inter_subset_left
  rw [hST] at hinter
  omega

/-- **Common-neighbor separation classification.** These are the only possible source distances
inside the distance-three graph. -/
theorem routeE_threeToggle_common_neighbor_separation_cases
    {S U T : Finset ℕ}
    (hST : routeEThreeToggleAdjacent S T)
    (hUT : routeEThreeToggleAdjacent U T) :
    (S ∆ U).card = 0 ∨ (S ∆ U).card = 2 ∨
      (S ∆ U).card = 4 ∨ (S ∆ U).card = 6 := by
  obtain ⟨k, hk⟩ := routeE_threeToggle_common_neighbor_even_separation hST hUT
  have hle := routeE_threeToggle_common_neighbor_separation_le_six hST hUT
  omega

/-- At source separation six, toggle three of the six changed coordinates. -/
def routeEThreeToggleDistanceSixCommonNeighbors (S U : Finset ℕ) : Finset (Finset ℕ) :=
  ((S ∆ U).powersetCard 3).image fun A => S ∆ A

/-- **Exact distance-six common-neighbor fibre.** No ambient prime coordinate can occur in a
common neighbor at source separation six. -/
theorem mem_routeEThreeToggleDistanceSixCommonNeighbors_iff
    {S U T : Finset ℕ} (hSU : (S ∆ U).card = 6) :
    T ∈ routeEThreeToggleDistanceSixCommonNeighbors S U ↔
      routeEThreeToggleAdjacent S T ∧ routeEThreeToggleAdjacent U T := by
  simp only [routeEThreeToggleDistanceSixCommonNeighbors, mem_image, mem_powersetCard]
  constructor
  · rintro ⟨A, ⟨hAD, hAcard⟩, rfl⟩
    constructor
    · rw [routeEThreeToggleAdjacent, routeE_symmDiff_self_left, hAcard]
    · rw [routeEThreeToggleAdjacent, routeE_symmDiff_three_reassociate]
      have hinter : A ∩ (S ∆ U) = A := inter_eq_left.mpr hAD
      have hcard := card_add_eq_card_symmDiff_add_twice_inter_routeEIncidenceSwitchParityRigidity A (S ∆ U)
      rw [hAcard, hSU, hinter, hAcard] at hcard
      omega
  · rintro ⟨hST, hUT⟩
    refine ⟨S ∆ T, ?_, ?_⟩
    · constructor
      · have hoverlap := routeE_threeToggle_common_neighbor_exact_overlap hST hUT
        rw [hSU] at hoverlap
        have hintercard : ((S ∆ T) ∩ (S ∆ U)).card = (S ∆ T).card := by
          rw [hST]
          omega
        exact inter_eq_left.mp (eq_of_subset_of_card_le inter_subset_left (by omega))
      · exact hST
    · exact routeE_symmDiff_self_left S T

/-- The exact distance-six codegree is the number of three-subsets of six changed coordinates. -/
theorem card_routeEThreeToggleDistanceSixCommonNeighbors
    {S U : Finset ℕ} (hSU : (S ∆ U).card = 6) :
    (routeEThreeToggleDistanceSixCommonNeighbors S U).card = Nat.choose 6 3 := by
  rw [routeEThreeToggleDistanceSixCommonNeighbors,
    card_image_of_injective _ (routeE_symmDiff_left_injective S), card_powersetCard, hSU]

end RHTower
