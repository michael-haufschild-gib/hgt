import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The radius spectrum of triangular-lattice occupancy

Nearest-point reduction confines disk centres to a fixed compact set.
Jointly closed occupancy thresholds therefore have closed radius spectra.
Finite norm sublevels bound the number of points uniformly over all centres.
These are the compactness mechanisms behind Lemma 5.3 of
Kittipassorn--Phetmak--Sriamorn.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy

open Set Metric

/-- Every feasible disk can be translated to a centre within unit distance of zero. -/
theorem exists_reduced_centre (r : ℝ) (k : ℕ) :
    (∃ z : ℂ, z ∈ centres r k) ↔
      ∃ z : ℂ, z ∈ closedBall 0 1 ∧ z ∈ centres r k := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨n, hn⟩ := exists_eisenstein_distance_sq_le_third z
    refine ⟨z - ringComplex n, ?_, ?_⟩
    · rw [Complex.normSq_eq_norm_sq] at hn
      rw [mem_closedBall, dist_zero_right]
      nlinarith only [hn, sq_nonneg (‖z - ringComplex n‖ - 1)]
    · simpa only [map_neg, sub_eq_add_neg] using add_mem_centres hz (-n)
  · rintro ⟨z, _, hz⟩
    exact ⟨z, hz⟩

/-- Feasible radii form a closed set, including the first radius attaining a threshold. -/
theorem isClosed_feasible_radii (k : ℕ) :
    IsClosed {r : ℝ | ∃ z : ℂ, z ∈ centres r k} := by
  let K : Set ℂ := closedBall 0 1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  let A : Set (K × ℝ) := {p | p.1.val ∈ centres p.2 k}
  have hA : IsClosed A := (isClosed_radius_centres k).preimage
    (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
  have heq : Prod.snd '' A = {r : ℝ | ∃ z : ℂ, z ∈ centres r k} := by
    ext r
    constructor
    · rintro ⟨⟨z, r⟩, hz, rfl⟩
      exact ⟨z.val, hz⟩
    · intro hr
      obtain ⟨z, hz, hzr⟩ := (exists_reduced_centre r k).mp hr
      exact ⟨(⟨z, hz⟩, r), hzr, rfl⟩
  rw [← heq]
  exact isClosedMap_snd_of_compactSpace A hA

/-- One finite norm sublevel bounds occupancy in every translated disk. -/
theorem feasible_occupancy_le (r : ℝ) (k : ℕ) (hk : ∃ z : ℂ, z ∈ centres r k) :
    k ≤ (points 0 (r + 1)).card := by
  obtain ⟨z, hz, s, hs, hcov⟩ := (exists_reduced_centre r k).mp hk
  rw [← hs]
  apply Finset.card_le_card
  intro n hn
  apply (mem_points 0 (r + 1) n).mpr
  have ht := dist_triangle (0 : ℂ) z (ringComplex n)
  change dist z 0 ≤ 1 at hz
  rw [dist_comm (0 : ℂ) z] at ht
  linarith only [ht, hz, hcov n hn]

/-- The largest number of lattice points in any closed disk of radius `r`. -/
def maxCount (r : ℝ) : ℕ := sSup {k : ℕ | ∃ z : ℂ, z ∈ centres r k}

private theorem feasible_nonempty (r : ℝ) :
    ({k : ℕ | ∃ z : ℂ, z ∈ centres r k}).Nonempty :=
  ⟨0, 0, ∅, rfl, by simp⟩

private theorem feasible_bddAbove (r : ℝ) :
    BddAbove {k : ℕ | ∃ z : ℂ, z ∈ centres r k} :=
  ⟨(points 0 (r + 1)).card, fun k hk => feasible_occupancy_le r k hk⟩

/-- The supremum is attained by an actual disk, rather than only approached. -/
theorem maxCount_attained (r : ℝ) : ∃ z : ℂ, (points z r).card = maxCount r := by
  obtain ⟨z, hz⟩ := Nat.sSup_mem (feasible_nonempty r) (feasible_bddAbove r)
  refine ⟨z, le_antisymm ?_ ((mem_centres_iff_card z r (maxCount r)).mp hz)⟩
  exact le_csSup (feasible_bddAbove r)
    ⟨z, (mem_centres_iff_card z r (points z r).card).mpr le_rfl⟩

/-- Every disk has cardinality at most the attained maximum. -/
theorem card_points_le_maxCount (z : ℂ) (r : ℝ) : (points z r).card ≤ maxCount r :=
  le_csSup (feasible_bddAbove r)
    ⟨z, (mem_centres_iff_card z r (points z r).card).mpr le_rfl⟩

theorem feasible_iff_le_maxCount (r : ℝ) (k : ℕ) :
    (∃ z : ℂ, z ∈ centres r k) ↔ k ≤ maxCount r := by
  constructor
  · exact fun h => le_csSup (feasible_bddAbove r) h
  · intro hk
    obtain ⟨z, hz⟩ := maxCount_attained r
    exact ⟨z, (mem_centres_iff_card z r k).mpr (by rwa [hz])⟩

/-- Enlarging the radius increases the maximum weakly. -/
theorem maxCount_monotone : Monotone maxCount := by
  intro r s hrs
  apply (feasible_iff_le_maxCount s (maxCount r)).mp
  obtain ⟨z, hz⟩ := (feasible_iff_le_maxCount r (maxCount r)).mpr le_rfl
  exact ⟨z, centres_mono_radius hrs _ hz⟩

/-- Each radius has a right neighbourhood on which the integer maximum is constant. -/
theorem maxCount_right_plateau (r : ℝ) :
    ∃ ε > 0, ∀ s : ℝ, r ≤ s → s < r + ε → maxCount s = maxCount r := by
  have hr : r ∈ {s : ℝ | ∃ z : ℂ, z ∈ centres s (maxCount r + 1)}ᶜ := by
    intro h
    have hle := (feasible_iff_le_maxCount r (maxCount r + 1)).mp h
    omega
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp
    (isClosed_feasible_radii (maxCount r + 1)).isOpen_compl r hr
  refine ⟨ε, hε, fun s hrs hs => le_antisymm ?_ (maxCount_monotone hrs)⟩
  have hdist : dist s r < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hrs)]
    linarith only [hs]
  have hnot := he hdist
  have hnotle : ¬ maxCount r + 1 ≤ maxCount s :=
    fun h => hnot ((feasible_iff_le_maxCount s (maxCount r + 1)).mpr h)
  omega

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.isClosed_feasible_radii
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.feasible_occupancy_le
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.maxCount_attained
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancy.maxCount_right_plateau
