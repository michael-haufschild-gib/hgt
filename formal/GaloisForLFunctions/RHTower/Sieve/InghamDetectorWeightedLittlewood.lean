import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodRectangle
import GaloisForLFunctions.RHTower.Sieve.InghamPoleRegularizedDetector
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling

open Complex MeasureTheory intervalIntegral Set Topology

namespace RHTower.Sieve

noncomputable section

noncomputable def inghamLittlewoodBoundary
    (X : ℕ) (c d T₁ T₂ : ℝ) : ℝ :=
  (∫ t in T₁..T₂, Real.log ‖inghamDetector X ((c : ℂ) + t * I)‖)
    - (∫ t in T₁..T₂, Real.log ‖inghamDetector X ((d : ℂ) + t * I)‖)
    + (d - c) *
      (∫ t in T₁..T₂, (logDeriv (inghamDetector X) ((d : ℂ) + t * I)).re)
    + (∫ x in c..d,
      (x - c) * (logDeriv (inghamDetector X) ((x : ℂ) + T₁ * I)).im)
    - ∫ x in c..d,
      (x - c) * (logDeriv (inghamDetector X) ((x : ℂ) + T₂ * I)).im

theorem exists_inghamDetector_weighted_littlewood_rectangle
    (X : ℕ) {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, inghamDetector X ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, inghamDetector X ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, inghamDetector X ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ t ∈ uIcc T₁ T₂, inghamDetector X ((c : ℂ) + t * I) ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ inghamDetector X z = 0) ∧
      2 * Real.pi *
          (∑ w ∈ Z,
            ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c)) =
        inghamLittlewoodBoundary X c d T₁ T₂ := by
  have hne : ∃ z : ℂ, inghamDetector X z ≠ 0 :=
    ⟨(c : ℂ) + T₁ * I, hleft T₁ left_mem_uIcc⟩
  simpa [inghamLittlewoodBoundary] using
    (exists_entire_weighted_littlewood_rectangle
      (inghamDetector_analyticOnNhd_univ X) hne hcd hT hbot htop hright hleft)

theorem two_pi_mul_zetaZeroMass_le_inghamLittlewoodBoundary
    (X : ℕ) {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, inghamDetector X ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, inghamDetector X ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, inghamDetector X ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ t ∈ uIcc T₁ T₂, inghamDetector X ((c : ℂ) + t * I) ≠ 0) :
    2 * Real.pi *
        (∑ w ∈ zetaResidueUnitClosedRectangleZeros
            ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I),
          ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) ≤
      inghamLittlewoodBoundary X c d T₁ T₂ := by
  have hne : ∃ z : ℂ, inghamDetector X z ≠ 0 :=
    ⟨(c : ℂ) + T₁ * I, hleft T₁ left_mem_uIcc⟩
  obtain ⟨Z, hmem, hboundary⟩ :=
    exists_inghamDetector_weighted_littlewood_rectangle X hcd hT
      hbot htop hright hleft
  let ZG : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I)
  have hsub : ZG ⊆ Z := by
    intro w hw
    obtain ⟨hwK, hwzero⟩ := mem_zetaResidueUnitClosedRectangleZeros.mp hw
    apply (hmem w).mpr
    refine ⟨?_, inghamDetector_eq_zero_of_zetaResidueUnit_eq_zero X hwzero⟩
    simpa [ZG] using hwK
  have hfirst :
      (∑ w ∈ ZG,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) ≤
        ∑ w ∈ ZG,
          ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c) := by
    apply Finset.sum_le_sum
    intro w hw
    have hwK := (mem_zetaResidueUnitClosedRectangleZeros.mp hw).1
    have hwre := (Complex.mem_reProdIm.mp hwK).1
    have hwre' : w.re ∈ Set.Icc c d := by
      simpa [ZG, uIcc_of_le hcd.le] using hwre
    have hordN := zetaResidueUnit_multiplicity_le_inghamDetector X w hne
    have hordR : ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) ≤
        ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) := by
      exact_mod_cast hordN
    exact mul_le_mul_of_nonneg_right hordR (sub_nonneg.mpr hwre'.1)
  have hsecond :
      (∑ w ∈ ZG,
          ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c)) ≤
        ∑ w ∈ Z,
          ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro w hwZ _
    have hwK := ((hmem w).mp hwZ).1
    have hwre := (Complex.mem_reProdIm.mp hwK).1
    rw [uIcc_of_le hcd.le] at hwre
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hwre.1)
  have hmass :
      (∑ w ∈ ZG,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) ≤
        ∑ w ∈ Z,
          ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c) :=
    hfirst.trans hsecond
  calc
    2 * Real.pi *
        (∑ w ∈ zetaResidueUnitClosedRectangleZeros
            ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I),
          ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) =
        2 * Real.pi *
          (∑ w ∈ ZG,
            ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) := by rfl
    _ ≤ 2 * Real.pi *
          (∑ w ∈ Z,
            ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c)) := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = inghamLittlewoodBoundary X c d T₁ T₂ := hboundary

end

end RHTower.Sieve
