import GaloisForLFunctions.DilutionCrystallizationPincer.EisensteinCommensurability
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancyMean

/-!
# A single excluded centre obstructs an incommensurate crystal

Disk-occupancy thresholds are closed and Eisenstein-periodic. The mixed
lattice density theorem therefore upgrades an exclusion at one centre to
an exclusion on every triangular coset with a nonnorm integral squared
scale. This applies the strengthened form of Lemma 7.5 of
Kittipassorn--Phetmak--Sriamorn without constructing a line-blocking fence.
-/

noncomputable section
namespace GaloisForLFunctions.DilutionCrystallizationPincer

open Set MetaplecticMobiusDescent.Eisenstein
open DiskOccupancy EisensteinCommensurability
open FamilyContinuationTheory.EisensteinNorm

/-- A dense mixed triangular coset tests every closed occupancy threshold. -/
theorem all_centres_iff_incommensurate_coset (α c : ℂ) (hα : mixedClosure α = ⊤)
    (r : ℝ) (k : ℕ) :
    centres r k = univ ↔ ∀ a : O, k ≤ (points (c + α * ringComplex a) r).card := by
  constructor
  · intro hall a
    apply (mem_centres_iff_card _ r k).mp
    rw [hall]
    exact mem_univ _
  · intro h
    exact closed_periodic_set_eq_univ α c hα (centres r k) (isClosed_centres r k)
      (fun _ hz a => add_mem_centres hz a)
      (fun a => (mem_centres_iff_card _ r k).mpr (h a))

/-- One low-occupancy centre forces a low-occupancy point on every nonnorm triangular coset. -/
theorem exists_low_occupancy_on_nonnorm_coset (α c : ℂ) (n : ℕ)
    (hnorm : ‖α‖ ^ 2 = n) (hn : ¬ (normSet n).Nonempty)
    (r : ℝ) (k : ℕ) (z : ℂ) (hz : (points z r).card < k) :
    ∃ a : O, (points (c + α * ringComplex a) r).card < k := by
  by_contra h
  have hall : centres r k = univ :=
    (all_centres_iff_incommensurate_coset α c
      (mixedClosure_eq_top_of_norm_not_represented α n hnorm hn) r k).mpr
        (fun a => Nat.le_of_not_gt (fun ha => h ⟨a, ha⟩))
  have hmem : z ∈ centres r k := by rw [hall]; exact mem_univ _
  exact (not_le_of_gt hz) ((mem_centres_iff_card z r k).mp hmem)

/-- The area average supplies the excluded centre needed by the arithmetic obstruction. -/
theorem exists_low_occupancy_on_nonnorm_coset_of_area_lt (α c : ℂ) (n : ℕ)
    (hnorm : ‖α‖ ^ 2 = n) (hn : ¬ (normSet n).Nonempty)
    (r : ℝ) (hr : 0 ≤ r) (k : ℕ)
    (harea : Real.pi * r ^ 2 < (k : ℝ) * (Real.sqrt 3 / 2)) :
    ∃ a : O, (points (c + α * ringComplex a) r).card < k := by
  obtain ⟨z, hz⟩ := exists_low_occupancy_of_area_lt hr k harea
  exact exists_low_occupancy_on_nonnorm_coset α c n hnorm hn r k z hz

/-- At a nonnorm packing-critical scale, every triangular coset has a deficient disk. -/
theorem critical_nonnorm_coset_obstruction (α c : ℂ) (n : ℕ)
    (hnorm : ‖α‖ ^ 2 = n) (hn : ¬ (normSet n).Nonempty) :
    ∃ a : O, (points (c + α * ringComplex a) (Real.sqrt n / 2)).card < n := by
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    apply hn
    refine ⟨0, mem_normSet.mpr ?_⟩
    change (0 : ℤ) ^ 2 - 0 * 0 + 0 ^ 2 = 0
    ring
  obtain ⟨z, hz⟩ := exists_low_occupancy_critical n (Nat.pos_of_ne_zero hn0)
  exact exists_low_occupancy_on_nonnorm_coset α c n hnorm hn (Real.sqrt n / 2) n z hz

end GaloisForLFunctions.DilutionCrystallizationPincer

#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.all_centres_iff_incommensurate_coset
#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.exists_low_occupancy_on_nonnorm_coset
#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.exists_low_occupancy_on_nonnorm_coset_of_area_lt
#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.critical_nonnorm_coset_obstruction
