import GaloisForLFunctions.HilbertMetric.EnclosingBallHelly
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancySpectrum

/-!
# Three-point certificates for triangular-lattice disk counts

A disk can contain a prescribed finite set of Eisenstein integers exactly
when every subset of at most three points fits in a disk of that radius.
Its minimum radius is attained and is determined by one such small subset.
Consequently the maximal occupancy threshold has an exact finite-set
certificate using only three-point enclosing radii.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy

open HilbertMetric

/-- Occupancy feasibility is equivalent to three-point feasibility on one finite witness set. -/
theorem feasible_iff_triple_subsets (r : ℝ) (k : ℕ) :
    (∃ z : ℂ, z ∈ centres r k) ↔ ∃ s : Finset O, s.card = k ∧
      ∀ t ⊆ s, t.card ≤ 3 → FitsBall ringComplex t r := by
  constructor
  · rintro ⟨z, s, hs, hcov⟩
    refine ⟨s, hs, (fitsDisk_iff_triples ringComplex s r).mp ?_⟩
    exact ⟨z, fun n hn => by simpa only [dist_comm] using hcov n hn⟩
  · rintro ⟨s, hs, hsmall⟩
    obtain ⟨z, hz⟩ := (fitsDisk_iff_triples ringComplex s r).mpr hsmall
    exact ⟨z, s, hs, fun n hn => by simpa only [dist_comm] using hz n hn⟩

/-- A three-point radius certificate characterizes every maximal-occupancy threshold. -/
theorem le_maxCount_iff_triple_radii {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    k ≤ maxCount r ↔ ∃ s : Finset O, s.card = k ∧
      ∀ t ⊆ s, t.card ≤ 3 → enclosingRadius ringComplex t ≤ r := by
  rw [← feasible_iff_le_maxCount, feasible_iff_triple_subsets]
  constructor
  · rintro ⟨s, hs, ht⟩
    exact ⟨s, hs, fun t hts hcard =>
      (fitsBall_iff_enclosingRadius_le ringComplex t hr).mp (ht t hts hcard)⟩
  · rintro ⟨s, hs, ht⟩
    exact ⟨s, hs, fun t hts hcard =>
      (fitsBall_iff_enclosingRadius_le ringComplex t hr).mpr (ht t hts hcard)⟩

/-- Every finite lattice cluster has an attained radius determined by at most three of its points. -/
theorem finite_cluster_three_point_support (s : Finset O) :
    ∃ t ⊆ s, t.card ≤ 3 ∧
      enclosingRadius ringComplex s = enclosingRadius ringComplex t :=
  exists_three_point_support ringComplex s

/-- A nonempty integral cluster has a unique disk centre at its attained minimum radius. -/
theorem finite_cluster_unique_minimum_centre (s : Finset O) (hs : s.Nonempty) :
    ∃! z : ℂ, ∀ n ∈ s, dist (ringComplex n) z ≤ enclosingRadius ringComplex s := by
  obtain ⟨z, hz⟩ := fitsBall_enclosingRadius ringComplex s
  exact ⟨z, hz, fun w hw => minimum_enclosing_centre_unique ringComplex s hs hw hz⟩

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.le_maxCount_iff_triple_radii
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.finite_cluster_three_point_support
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.finite_cluster_unique_minimum_centre
