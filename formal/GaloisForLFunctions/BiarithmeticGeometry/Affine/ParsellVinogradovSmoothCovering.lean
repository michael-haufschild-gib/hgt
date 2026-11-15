import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovFrameCutoffs
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovFiniteCovering
import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteOrderedPartitions
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovMomentTopology

/-!
# Smooth finite coverings of the unit moment image

The dimension-dependent integer grid supplies a compactly supported smooth function
equal to one on an open neighborhood of every moment of the physical unit
cube. Ordered cutoff weights decompose this function into nonnegative
pieces, each supported in its own moment box.
-/

open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.FiniteOrderedPartitions

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The smooth union of all frame cutoffs in the dimension-dependent grid. -/
def smoothCovering (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ)
    (x : AffineAxisSpace r k) : ℝ :=
  cutoffUnion (dimensionCoveringGrid r q ε)
    (fun i => frameCutoff r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x)

/-- The union of the open frame plateaus in the covering grid. -/
def coveringNeighborhood (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) :
    Set (AffineAxisSpace r k) :=
  ⋃ i ∈ dimensionCoveringGrid r q ε, frameCore r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ))

/-- The finite closed union containing all covering cutoff supports. -/
def coveringBoxUnion (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) :
    Set (AffineAxisSpace r k) :=
  ⋃ i ∈ dimensionCoveringGrid r q ε,
    momentCoveringBox r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ))

/-- Ordered pieces partition the smooth union without dividing by a cutoff sum. -/
def coveringWeight (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (i : ℤ)
    (x : AffineAxisSpace r k) : ℝ :=
  orderedWeight (dimensionCoveringGrid r q ε)
    (fun j => frameCutoff r k ε δ (ε * (j : ℝ) / (q + 1 : ℝ)) x) i

theorem smoothCovering_mem_Icc (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ)
    (x : AffineAxisSpace r k) : smoothCovering r k q ε δ x ∈ Set.Icc (0 : ℝ) 1 :=
  cutoffUnion_mem_Icc (dimensionCoveringGrid r q ε)
    (fun i => frameCutoff r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x)
    (fun i _ => frameCutoff_mem_Icc r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x)

theorem contDiff_smoothCovering (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothCovering r k q ε δ) := by
  unfold smoothCovering cutoffUnion
  apply contDiff_const.sub
  apply contDiff_prod
  intro i _
  exact contDiff_const.sub (contDiff_frameCutoff r k ε δ _)

theorem isOpen_coveringNeighborhood (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) :
    IsOpen (coveringNeighborhood r k q ε δ) :=
  isOpen_iUnion (fun i => isOpen_iUnion
    (fun _ => isOpen_frameCore r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ))))

/-- The finite smooth union is identically one throughout its open plateau union. -/
theorem smoothCovering_eqOn_neighborhood (r k q : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) :
    Set.EqOn (smoothCovering r k q ε δ) 1 (coveringNeighborhood r k q ε δ) := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
  exact cutoffUnion_eq_one _ _ ⟨i, hi, frameCutoff_eqOn_frameCore r k ε δ _ hx⟩

/-- Every unit physical moment belongs to the open union, not merely its closure. -/
theorem horizontalMoment_mem_coveringNeighborhood (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ u : Fin (r + 1) → ℝ) (z : ℝ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hθ : ∀ i, 0 ≤ ε * δ i ∧ ε * δ i ≤ 1)
    (hz : 0 ≤ z ∧ z ≤ 1) :
    horizontalMoment r k u z ∈ coveringNeighborhood r k q ε δ := by
  obtain ⟨i, hi, y, hy, he⟩ := exists_dimensionGrid_unitFrame r k q ε hε δ u z hu hθ hz
  apply Set.mem_iUnion₂.mpr
  refine ⟨i, hi, momentFrame_unitCube_subset_frameCore r k ε hε δ _ ?_⟩
  exact ⟨y, hy, he⟩

/-- The dimension-dependent grid produces an open neighborhood of the full unit moment image. -/
theorem unitMomentImage_subset_coveringNeighborhood (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (hθ : ∀ i, 0 ≤ ε * δ i ∧ ε * δ i ≤ 1) :
    unitMomentImage r k ⊆ coveringNeighborhood r k q ε δ := by
  rintro x ⟨u, hu, rfl⟩
  have he : horizontalMoment r k (fun i => u i.succ) (u 0) = canonicalMoment r k u := by
    exact congrArg (canonicalMoment r k) (Fin.cons_self_tail u)
  rw [← he]
  exact horizontalMoment_mem_coveringNeighborhood r k q ε hε δ _ _
    (fun i => ⟨hu.1 i.succ, hu.2 i.succ⟩) hθ ⟨hu.1 0, hu.2 0⟩

theorem isCompact_coveringBoxUnion (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) :
    IsCompact (coveringBoxUnion r k q ε δ) :=
  (dimensionCoveringGrid r q ε).isCompact_biUnion
    (fun i _ => isCompact_momentCoveringBox r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)))

/-- Outside the finite box union every factor cutoff vanishes. -/
theorem support_smoothCovering_subset (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) :
    Function.support (smoothCovering r k q ε δ) ⊆ coveringBoxUnion r k q ε δ := by
  intro x hx
  by_contra hn
  apply hx
  apply cutoffUnion_eq_zero
  intro i hi
  by_contra hne
  apply hn
  exact Set.mem_iUnion₂.mpr ⟨i, hi, support_frameCutoff_subset r k ε hε δ _ hne⟩

theorem tsupport_smoothCovering_subset (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) :
    tsupport (smoothCovering r k q ε δ) ⊆ coveringBoxUnion r k q ε δ :=
  closure_minimal (support_smoothCovering_subset r k q ε hε δ)
    (isCompact_coveringBoxUnion r k q ε δ).isClosed

theorem hasCompactSupport_smoothCovering (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) : HasCompactSupport (smoothCovering r k q ε δ) :=
  (isCompact_coveringBoxUnion r k q ε δ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smoothCovering_subset r k q ε hε δ)

/-- The smooth neighborhood cutoff as an actual complex Schwartz function. -/
def smoothCoveringSchwartz (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) : SchwartzMap (AffineAxisSpace r k) ℂ :=
  ((hasCompactSupport_smoothCovering r k q ε hε δ).comp_left
    (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (contDiff_smoothCovering r k q ε δ))

theorem sum_coveringWeight (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ)
    (x : AffineAxisSpace r k) :
    (∑ i ∈ dimensionCoveringGrid r q ε, coveringWeight r k q ε δ i x) =
      smoothCovering r k q ε δ x :=
  sum_orderedWeight (dimensionCoveringGrid r q ε)
    (fun i => frameCutoff r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x)

theorem coveringWeight_mem_Icc (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ)
    (i : ℤ) (hi : i ∈ dimensionCoveringGrid r q ε) (x : AffineAxisSpace r k) :
    coveringWeight r k q ε δ i x ∈ Set.Icc 0
      (frameCutoff r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x) :=
  orderedWeight_mem_Icc (dimensionCoveringGrid r q ε)
    (fun j => frameCutoff r k ε δ (ε * (j : ℝ) / (q + 1 : ℝ)) x)
    (fun j _ => frameCutoff_mem_Icc r k ε δ (ε * (j : ℝ) / (q + 1 : ℝ)) x) i hi

theorem contDiff_coveringWeight (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (i : ℤ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coveringWeight r k q ε δ i) := by
  unfold coveringWeight orderedWeight
  apply (contDiff_frameCutoff r k ε δ _).mul
  apply contDiff_prod
  intro j _
  exact contDiff_const.sub (contDiff_frameCutoff r k ε δ _)

/-- Each ordered piece retains compact support in its own frame. -/
theorem hasCompactSupport_coveringWeight (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) : HasCompactSupport (coveringWeight r k q ε δ i) :=
  (hasCompactSupport_frameCutoff r k ε hε δ _).mul_right

/-- Ordering does not enlarge the support of an individual cutoff. -/
theorem tsupport_coveringWeight_subset (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) :
    tsupport (coveringWeight r k q ε δ i) ⊆
      momentCoveringBox r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) := by
  apply closure_minimal _ (isCompact_momentCoveringBox r k ε δ _).isClosed
  intro x hx
  apply support_frameCutoff_subset r k ε hε δ _
  intro hz
  apply hx
  change frameCutoff r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x * _ = 0
  rw [hz, zero_mul]

#print axioms smoothCovering_mem_Icc
#print axioms contDiff_smoothCovering
#print axioms isOpen_coveringNeighborhood
#print axioms smoothCovering_eqOn_neighborhood
#print axioms horizontalMoment_mem_coveringNeighborhood
#print axioms unitMomentImage_subset_coveringNeighborhood
#print axioms isCompact_coveringBoxUnion
#print axioms support_smoothCovering_subset
#print axioms tsupport_smoothCovering_subset
#print axioms hasCompactSupport_smoothCovering
#print axioms smoothCoveringSchwartz
#print axioms sum_coveringWeight
#print axioms coveringWeight_mem_Icc
#print axioms contDiff_coveringWeight
#print axioms hasCompactSupport_coveringWeight
#print axioms tsupport_coveringWeight_subset

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
