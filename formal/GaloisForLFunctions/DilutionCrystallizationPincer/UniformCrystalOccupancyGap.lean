import GaloisForLFunctions.DilutionCrystallizationPincer.IncommensurateDiskOccupancy
import Mathlib.Topology.Maps.Proper.Basic

/-!
# A uniform radius gap for nonnorm triangular patterns

Translations can be reduced to a fixed compact set of centres. Complex
scales of fixed squared norm are also bounded. Closed occupancy constraints
then make the set of radii admitting a full triangular pattern closed.
The critical nonnorm obstruction consequently persists on one radius
neighbourhood valid for every translation and orientation simultaneously.
-/

noncomputable section
namespace GaloisForLFunctions.DilutionCrystallizationPincer

open Set Metric MetaplecticMobiusDescent.Eisenstein DiskOccupancy
open FamilyContinuationTheory.EisensteinNorm

/-- Some triangular coset of squared scale `n` meets the occupancy threshold at every centre. -/
def CrystalFeasibleRadius (n : ℕ) (r : ℝ) : Prop :=
  ∃ α c : ℂ, ‖α‖ ^ 2 = n ∧ ∀ a : O, c + α * ringComplex a ∈ centres r n

/-- Allowing arbitrary translations and orientations still gives a closed radius locus. -/
theorem isClosed_crystalFeasibleRadius (n : ℕ) : IsClosed {r | CrystalFeasibleRadius n r} := by
  let C : Set ℂ := closedBall 0 1
  let B : Set ℂ := closedBall 0 ((n : ℝ) + 1)
  letI : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  letI : CompactSpace B := isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1))
  let K := C × B
  let A : Set (K × ℝ) := {q | ‖q.1.2.val‖ ^ 2 = n ∧
    ∀ a : O, q.1.1.val + q.1.2.val * ringComplex a ∈ centres q.2 n}
  have hc : Continuous (fun q : K × ℝ => q.1.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hα : Continuous (fun q : K × ℝ => q.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hpoints : IsClosed {q : K × ℝ | ∀ a : O,
      q.1.1.val + q.1.2.val * ringComplex a ∈ centres q.2 n} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun a => (isClosed_radius_centres n).preimage
      (continuous_snd.prodMk (hc.add (hα.mul continuous_const)))
  have hA : IsClosed A := (isClosed_eq (hα.norm.pow 2) continuous_const).inter hpoints
  have heq : Prod.snd '' A = {r | CrystalFeasibleRadius n r} := by
    ext r
    constructor
    · rintro ⟨⟨⟨c, α⟩, r⟩, ⟨hnorm, hall⟩, rfl⟩
      exact ⟨α.val, c.val, hnorm, hall⟩
    · rintro ⟨α, c, hnorm, hall⟩
      obtain ⟨m, hm⟩ := exists_eisenstein_distance_sq_le_third c
      have hc' : c - ringComplex m ∈ C := by
        rw [Complex.normSq_eq_norm_sq] at hm
        change dist (c - ringComplex m) 0 ≤ 1
        rw [dist_zero_right]
        nlinarith only [hm, sq_nonneg (‖c - ringComplex m‖ - 1)]
      have hα' : α ∈ B := by
        change dist α 0 ≤ (n : ℝ) + 1
        rw [dist_zero_right]
        nlinarith only [hnorm, sq_nonneg (‖α‖ - (1 / 2 : ℝ))]
      refine ⟨((⟨c - ringComplex m, hc'⟩, ⟨α, hα'⟩), r), ⟨hnorm, ?_⟩, rfl⟩
      intro a
      have he : (c - ringComplex m) + α * ringComplex a =
          (c + α * ringComplex a) + ringComplex (-m) := by
        rw [map_neg]
        ring
      change (c - ringComplex m) + α * ringComplex a ∈ centres r n
      rw [he]
      exact add_mem_centres (hall a) (-m)
  rw [← heq]
  exact isClosedMap_snd_of_compactSpace A hA

/-- A nonnorm critical radius has one positive exclusion margin for all cosets and orientations. -/
theorem critical_nonnorm_uniform_gap (n : ℕ) (hn : ¬ (normSet n).Nonempty) :
    ∃ ε > 0, ∀ r : ℝ, dist r (Real.sqrt n / 2) < ε →
      ∀ α c : ℂ, ‖α‖ ^ 2 = n →
        ∃ a : O, (points (c + α * ringComplex a) r).card < n := by
  have hcritical : ¬ CrystalFeasibleRadius n (Real.sqrt n / 2) := by
    rintro ⟨α, c, hnorm, hall⟩
    obtain ⟨a, ha⟩ := critical_nonnorm_coset_obstruction α c n hnorm hn
    exact (not_le_of_gt ha) ((mem_centres_iff_card _ _ n).mp (hall a))
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp
    (isClosed_crystalFeasibleRadius n).isOpen_compl (Real.sqrt n / 2) hcritical
  refine ⟨ε, hε, fun r hr α c hnorm => ?_⟩
  by_contra h
  apply he hr
  refine ⟨α, c, hnorm, fun a => ?_⟩
  apply (mem_centres_iff_card _ r n).mpr
  exact Nat.le_of_not_gt (fun ha => h ⟨a, ha⟩)

end GaloisForLFunctions.DilutionCrystallizationPincer

#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.isClosed_crystalFeasibleRadius
#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.critical_nonnorm_uniform_gap
