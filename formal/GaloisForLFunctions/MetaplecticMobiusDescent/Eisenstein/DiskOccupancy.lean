import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinNearestPoint

/-!
# Closed occupancy thresholds in the Eisenstein lattice

The centres of disks containing at least `k` lattice points form a closed,
lattice-periodic set. Locally, only finitely many lattice points can occur;
the threshold is therefore a finite union of intersections of closed disks.
This supplies the topological input for the line obstruction in Lemma 7.5
of Kittipassorn--Phetmak--Sriamorn without enumerating lattice configurations.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy

open Metric Set Filter Topology

/-- A disk at an arbitrary centre contains finitely many integral points. -/
theorem finite_disk_points (z : ℂ) (r : ℝ) :
    Set.Finite {n : O | dist z (ringComplex n) ≤ r} := by
  apply (finite_norm_sublevel (‖z‖ + r)).subset
  intro n hn
  change dist z (ringComplex n) ≤ r at hn
  have ht := dist_triangle (ringComplex n) z 0
  rw [dist_zero_right, dist_zero_right, dist_comm (ringComplex n) z] at ht
  exact ht.trans (by linarith only [hn])

/-- The exact finite set of lattice points in a closed disk. -/
def points (z : ℂ) (r : ℝ) : Finset O := (finite_disk_points z r).toFinset

theorem mem_points (z : ℂ) (r : ℝ) (n : O) :
    n ∈ points z r ↔ dist z (ringComplex n) ≤ r :=
  (finite_disk_points z r).mem_toFinset

/-- Centres admitting `k` distinct lattice points in their closed radius-`r` disk. -/
def centres (r : ℝ) (k : ℕ) : Set ℂ :=
  {z | ∃ s : Finset O, s.card = k ∧ ∀ n ∈ s, dist z (ringComplex n) ≤ r}

/-- The witness definition is exactly the cardinality threshold. -/
theorem mem_centres_iff_card (z : ℂ) (r : ℝ) (k : ℕ) :
    z ∈ centres r k ↔ k ≤ (points z r).card := by
  constructor
  · rintro ⟨s, hs, hcov⟩
    rw [← hs]
    exact Finset.card_le_card (fun n hn => (mem_points z r n).mpr (hcov n hn))
  · intro hk
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hk
    exact ⟨s, hcard, fun n hn => (mem_points z r n).mp (hs hn)⟩

/-- Each occupancy threshold is closed; no points disappear in a limiting closed disk. -/
theorem isClosed_centres (r : ℝ) (k : ℕ) : IsClosed (centres r k) := by
  classical
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
  let t := points z (r + 1)
  let F : Set ℂ := ⋃ s ∈ t.powersetCard k, ⋂ n ∈ s, closedBall (ringComplex n) r
  have hF : IsClosed F := isClosed_biUnion_finset fun _ _ =>
    isClosed_biInter fun _ _ => isClosed_closedBall
  have hsub : F ⊆ centres r k := by
    intro w hw
    obtain ⟨s, hw⟩ := mem_iUnion.mp hw
    obtain ⟨hs, hw⟩ := mem_iUnion.mp hw
    exact ⟨s, (Finset.mem_powersetCard.mp hs).2,
      fun n hn => mem_iInter.mp (mem_iInter.mp hw n) hn⟩
  have hzF : z ∈ Fᶜ := fun h => hz (hsub h)
  have hnhds := Filter.inter_mem (ball_mem_nhds z zero_lt_one)
    (hF.isOpen_compl.mem_nhds hzF)
  apply Filter.mem_of_superset hnhds
  rintro w ⟨hwz, hwF⟩ hw
  obtain ⟨s, hs, hcov⟩ := hw
  have hst : s ⊆ t := by
    intro n hn
    apply (mem_points z (r + 1) n).mpr
    have ht := dist_triangle z w (ringComplex n)
    have hwz' : dist z w < 1 := by simpa only [mem_ball, dist_comm] using hwz
    linarith only [ht, hwz', hcov n hn]
  apply hwF
  refine mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨Finset.mem_powersetCard.mpr ⟨hst, hs⟩, ?_⟩⟩
  exact mem_iInter.mpr fun n => mem_iInter.mpr fun hn => hcov n hn

/-- Translation by a lattice point preserves the number of admissible distinct points. -/
theorem add_mem_centres {z : ℂ} {r : ℝ} {k : ℕ}
    (hz : z ∈ centres r k) (m : O) : z + ringComplex m ∈ centres r k := by
  classical
  obtain ⟨s, hs, hcov⟩ := hz
  refine ⟨s.image (fun n => n + m), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h), hs]
  · intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    rw [map_add, dist_add_right]
    exact hcov a ha

/-- The admissible-centre set is periodic under the full Eisenstein lattice. -/
theorem add_mem_centres_iff (z : ℂ) (r : ℝ) (k : ℕ) (m : O) :
    z + ringComplex m ∈ centres r k ↔ z ∈ centres r k := by
  constructor
  · intro h
    simpa only [map_neg, add_neg_cancel_right] using add_mem_centres h (-m)
  · intro h
    exact add_mem_centres h m

/-- Enlarging a disk can only enlarge every occupancy threshold. -/
theorem centres_mono_radius {r s : ℝ} (hrs : r ≤ s) (k : ℕ) :
    centres r k ⊆ centres s k := by
  rintro z ⟨t, ht, hcov⟩
  exact ⟨t, ht, fun n hn => (hcov n hn).trans hrs⟩

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.mem_centres_iff_card
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.isClosed_centres
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.add_mem_centres_iff
