import GaloisForLFunctions.HilbertMetric.PlanarDiskObstruction
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.TriangularDiskCovering

/-!
# The smallest obstruction survives fine triangular sampling

The plane has a finite noncoverable set, hence a least obstruction size.
Stability and nearest-point rounding realize exactly that size in every
sufficiently fine Eisenstein lattice. Minimality prevents rounding from
identifying any points. This is the cardinality conclusion of Proposition
9.3 of Kittipassorn--Phetmak--Sriamorn, without a configuration search.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering

open HilbertMetric

/-- There is a planar obstruction smaller than no other planar obstruction. -/
theorem exists_minimal_planar_obstruction :
    ∃ s : Finset ℂ, ¬ BallCoverable 1 (fun z : s => (z : ℂ)) ∧
      ∀ t : Finset ℂ, t.card < s.card → BallCoverable 1 (fun z : t => (z : ℂ)) := by
  classical
  have hex : ∃ n : ℕ, ∃ s : Finset ℂ, s.card = n ∧
      ¬ BallCoverable 1 (fun z : s => (z : ℂ)) := by
    obtain ⟨s, hs⟩ := exists_noncoverable_finset_complex
    exact ⟨s.card, s, rfl, hs⟩
  obtain ⟨s, hcard, hs⟩ := Nat.find_spec hex
  refine ⟨s, hs, fun t ht => ?_⟩
  by_contra hbad
  have hlt : t.card < Nat.find hex := by simpa only [hcard] using ht
  exact Nat.find_min hex hlt ⟨t, rfl, hbad⟩

/-- The universal minimum is attained by distinct lattice points at every sufficiently small scale. -/
theorem smallest_obstruction_in_every_fine_lattice :
    ∃ (s : Finset ℂ) (ε : ℝ), 0 < ε ∧
      ¬ BallCoverable 1 (fun z : s => (z : ℂ)) ∧
      (∀ u : Finset ℂ, u.card < s.card → BallCoverable 1 (fun z : u => (z : ℂ))) ∧
      ∀ d : ℝ, 0 < d → d < ε →
        (∃ t : Finset O, t.card = s.card ∧ ¬ BallCoverable 1 (fun n : t => point d n)) ∧
        (∀ t : Finset O, t.card < s.card → BallCoverable 1 (fun n : t => point d n)) := by
  classical
  obtain ⟨s, hs, hmin⟩ := exists_minimal_planar_obstruction
  obtain ⟨ε, hε, hround⟩ := round_noncoverable_configuration (fun z : s => (z : ℂ)) hs
  refine ⟨s, ε, hε, hs, hmin, fun d hd hdε => ?_⟩
  have hsmaller (t : Finset O) (ht : t.card < s.card) :
      BallCoverable 1 (fun n : t => point d n) := by
    let u := t.image (point d)
    have hucard : u.card < s.card := (Finset.card_image_le).trans_lt ht
    exact (hmin u hucard).comp (fun n : t =>
      ⟨point d n, Finset.mem_image.mpr ⟨n, n.property, rfl⟩⟩)
  refine ⟨?_, hsmaller⟩
  obtain ⟨n, hn⟩ := hround d hd hdε
  let t := Finset.univ.image n
  have htbad : ¬ BallCoverable 1 (fun a : t => point d a) := by
    intro hc
    exact hn (hc.comp (fun i => ⟨n i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩))
  have hle : t.card ≤ s.card := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset s)) (f := n)
    simpa only [Finset.card_univ, Fintype.card_coe] using h
  have hge : s.card ≤ t.card := by
    by_contra h
    exact htbad (hsmaller t (lt_of_not_ge h))
  exact ⟨t, le_antisymm hle hge, htbad⟩

/-- An interval next to the collapsed scale consists entirely of noncoverable positive spacings. -/
theorem exists_initial_noncoverable_interval :
    ∃ ε > 0, ∀ d : ℝ, 0 < d → d < ε → ¬ CoverableSpacing d := by
  obtain ⟨s, ε, hε, _, _, h⟩ := smallest_obstruction_in_every_fine_lattice
  refine ⟨ε, hε, fun d hd hdε hc => ?_⟩
  obtain ⟨t, _, ht⟩ := (h d hd hdε).1
  exact ht (hc.comp Subtype.val)

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering.smallest_obstruction_in_every_fine_lattice
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering.exists_initial_noncoverable_interval
