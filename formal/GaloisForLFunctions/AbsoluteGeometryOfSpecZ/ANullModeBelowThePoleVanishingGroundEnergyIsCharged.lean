import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheChargedNullModesAreTheCrossingsOfThePolarLagrangian
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundState
import GaloisForLFunctions.RHTower.PoleVanishingWeilPositivityPrimeTwo

/-!
# A null mode below the pole-vanishing ground energy is charged

The pole-vanishing ground energy `μ₀(a)` is the floor of Weil's form at the aperture `a` on the
vectors without charge; the ground energy `μ(a) ≤ μ₀(a)` is its floor on all vectors.

* **The charged window.** A null mode at an energy `E < μ₀(a)` is charged
  (`neutralNullity_eq_zero_of_lt_polarGroundEnergy`): a neutral null mode is a vector without
  charge of Rayleigh quotient `E`. Its nullity is at most two.
* **The index up to the floor.** For `E ≤ μ₀(a)` the index is at most two
  (`negativeRank_le_two_of_le_polarGroundEnergy`): the charge map is injective on a negative
  space.
* **The ground modes.** The null modes at the ground energy are all charged exactly when
  `μ(a) < μ₀(a)` (`neutralNullity_groundEnergy_eq_zero_iff`): if the two floors agree, a ground
  state of the constrained form is a neutral ground mode.
* **The index as a crossing number.** For `E < μ₀(b)` the index at `b` is the number of crossings
  of the polar Lagrangian with the charge axis below `b`
  (`negativeRank_eq_sum_chargedNullity_of_lt_polarGroundEnergy`).
* On every aperture up to `½ (log 2 + 1/50)` and every energy below `1/20` this holds without
  hypothesis (`negativeRank_eq_sum_chargedNullity_of_le_primeTwo`).
-/

open Module Finset
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil
open ArithmeticContinuationAndCriticalEnergy HTGeometry

variable {a : SuzukiPositiveAperture} {E : ℝ}

/-- **A null mode below the pole-vanishing ground energy is charged.** -/
theorem neutralNullity_eq_zero_of_lt_polarGroundEnergy
    (h : E < ccmRestrictedWeilPolarGroundEnergy a) : neutralNullity a E = 0 := by
  rw [neutralNullity_eq_zero_iff]
  intro u hu hc
  by_contra hu0
  have hJ : ccmArchimedeanFormToAperture a u ≠ 0 := fun hz =>
    hu0 (ccmArchimedeanFormToAperture_injective a (by rw [hz, map_zero]))
  have hpos : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    have := norm_pos_iff.mpr hJ
    positivity
  have hq : (inner ℂ (operator a E u) u).re = 0 := by
    rw [hu, inner_zero_left, Complex.zero_re]
  rw [operator_quadratic] at hq
  have hfloor := ccmRestrictedWeilPolarGroundEnergy_mul_le a u hc
  nlinarith [mul_pos (sub_pos.mpr h) hpos]

/-- Below the pole-vanishing ground energy the nullity is at most two. -/
theorem weilNullity_le_two_of_lt_polarGroundEnergy
    (h : E < ccmRestrictedWeilPolarGroundEnergy a) : weilNullity a E ≤ 2 := by
  rw [weilNullity_eq_charged_add_neutral, neutralNullity_eq_zero_of_lt_polarGroundEnergy h,
    add_zero]
  exact chargedNullity_le_two a E

/-- **Up to the pole-vanishing ground energy the index is at most two**: the charge map is
injective on the negative space. -/
theorem negativeRank_le_two_of_le_polarGroundEnergy
    (h : E ≤ ccmRestrictedWeilPolarGroundEnergy a) : negativeRank a E ≤ 2 := by
  have hinj : Function.Injective
      ((polarCharge a : Space a →ₗ[ℂ] ChargeSpace).domRestrict (negativeSpace a E)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, hu⟩ hd
    have hc : IsPolarConstrained a u := (polarCharge_eq_zero_iff a u).mp hd
    by_contra hu0
    have hneg := PaperNegativePart.negativeSpace_strict _ (operator_selfAdjoint a E) hu
      (fun hz => hu0 (Subtype.ext hz))
    rw [operator_quadratic] at hneg
    have hfloor := ccmRestrictedWeilPolarGroundEnergy_mul_le a u hc
    nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg ‖ccmArchimedeanFormToAperture a u‖)]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_euclideanSpace_fin] at hle
  exact hle

/-- **The null modes at the ground energy are all charged exactly when the ground energy is
strictly below the pole-vanishing ground energy.** -/
theorem neutralNullity_groundEnergy_eq_zero_iff (a : SuzukiPositiveAperture) :
    neutralNullity a (ccmRestrictedWeilGroundEnergy a) = 0 ↔
      ccmRestrictedWeilGroundEnergy a < ccmRestrictedWeilPolarGroundEnergy a := by
  constructor
  · intro h
    refine lt_of_le_of_ne (ccmRestrictedWeilGroundEnergy_le_polar a) fun heq => ?_
    -- a ground state of the constrained form is a neutral ground mode
    obtain ⟨u, hc, hnorm, hq⟩ := exists_polarConstrained_groundState a
    have hpos : (operator a (ccmRestrictedWeilGroundEnergy a)).IsPositive :=
      (negativeRank_eq_zero_iff a _).mp ((negativeRank_eq_zero_iff_ground a _).mpr le_rfl)
    have hre : (inner ℂ (operator a (ccmRestrictedWeilGroundEnergy a) u) u).re = 0 := by
      rw [operator_quadratic, hq, hnorm, ← heq]
      ring
    have hi : inner ℂ (operator a (ccmRestrictedWeilGroundEnergy a) u) u = 0 := by
      apply Complex.ext
      · exact hre
      · exact ((Complex.nonneg_iff).1 (hpos.inner_nonneg_left u)).2.symm
    have hsym : inner ℂ u (operator a (ccmRestrictedWeilGroundEnergy a) u) =
        (starRingEnd ℂ) (inner ℂ (operator a (ccmRestrictedWeilGroundEnergy a) u) u) :=
      (inner_conj_symm u (operator a (ccmRestrictedWeilGroundEnergy a) u)).symm
    have hz := hpos.apply_eq_zero_of_inner_eq_zero
      (show inner ℂ u (operator a (ccmRestrictedWeilGroundEnergy a) u) = 0 by
        rw [hsym, hi, map_zero])
    have hu0 := (neutralNullity_eq_zero_iff a _).mp h u hz hc
    rw [hu0, map_zero, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · exact neutralNullity_eq_zero_of_lt_polarGroundEnergy

/-- **Below the pole-vanishing ground energy the index is the number of crossings of the polar
Lagrangian with the charge axis.** -/
theorem negativeRank_eq_sum_chargedNullity_of_lt_polarGroundEnergy {b : SuzukiPositiveAperture}
    (h : E < ccmRestrictedWeilPolarGroundEnergy b) :
    negativeRank b E = ∑ a ∈ resonantBelow b E, chargedNullity a E :=
  negativeRank_eq_sum_chargedNullity fun a hab =>
    (neutralNullity_eq_zero_iff a E).mp (neutralNullity_eq_zero_of_lt_polarGroundEnergy
      (h.trans_le (ccmRestrictedWeilPolarGroundEnergy_antitone hab.le)))

/-- **On every aperture up to `½ (log 2 + 1/50)` and at every energy below `1/20`, the index is
the number of crossings of the polar Lagrangian with the charge axis, and it is at most two.** -/
theorem negativeRank_eq_sum_chargedNullity_of_le_primeTwo {b : SuzukiPositiveAperture}
    (hb : b.1 ≤ (Real.log 2 + 1 / 50) / 2) (hE : E < 1 / 20) :
    negativeRank b E = ∑ a ∈ resonantBelow b E, chargedNullity a E ∧ negativeRank b E ≤ 2 := by
  have hfloor := one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo b hb
  exact ⟨negativeRank_eq_sum_chargedNullity_of_lt_polarGroundEnergy (hE.trans_le hfloor),
    negativeRank_le_two_of_le_polarGroundEnergy (hE.le.trans hfloor)⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
