import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexAtAnApertureIsTheSumOfTheNullitiesBelowIt
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePolarRelationOfASelfAdjointFredholmOperatorIsLagrangian
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundForcing

/-!
# The charged null modes are the crossings of the polar Lagrangian

A vector `ξ` of the form domain at the aperture `a` has two **charges**, its coefficients at the
two poles (`polarCharge`). The two pole profiles span the **forcings**. At the energy `E`, the
solutions of the forced equation

  `𝔚_a(ξ, v) − E ⟨ξ, v⟩ = ⟨c₊ e₊ + c₋ e₋, v⟩`   for every `v`

give the pairs (charges of `ξ`, forcing `(c₊, c₋)`): the **polar Lagrangian** of the aperture
(`polarLagrangian`, `mem_polarLagrangian_iff`). It is a Lagrangian plane in the fixed space
`ℂ² × ℂ²` (`polarLagrangian_isotropic`, `finrank_polarLagrangian`), so the apertures form a path
of Lagrangian planes in one four-dimensional space.

* The plane meets the charge axis `ℂ² × 0` in the charges of the null modes
  (`mem_nullCharges_iff`). Its dimension there is the **charged nullity**, at most two.
* A null mode without charge is **neutral**; the neutral null modes are not seen by the plane, and
  `weilNullity = chargedNullity + neutralNullity` (`weilNullity_eq_charged_add_neutral`).
* The plane meets the forcing axis `0 × ℂ²` in the null modes of the form restricted to the
  vectors without charge (`exists_forcing_iff_constrained_null`).

With the index law of the aperture path, the index at an aperture is the number of crossings of
the path with the charge axis plus the neutral nullities below it
(`negativeRank_eq_sum_charged_add_neutral`). If no null mode below the aperture is neutral, the
index is the number of crossings (`negativeRank_eq_sum_chargedNullity`) and lies between the
number of resonant apertures and its double (`negativeRank_le_two_mul_card_resonantBelow`).
-/

open Module Finset
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil
open ArithmeticContinuationAndCriticalEnergy HTGeometry

/-- The space of charges: one coordinate for each pole. -/
abbrev ChargeSpace : Type := EuclideanSpace ℂ (Fin 2)

/-- **The charges of a vector**: its two pole coefficients. -/
def polarCharge (a : SuzukiPositiveAperture) : Space a →L[ℂ] ChargeSpace :=
  ((EuclideanSpace.equiv (Fin 2) ℂ).symm : (Fin 2 → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin 2)).comp
    (ContinuousLinearMap.pi ![ccmPolarCoordinate a (1 / 2), ccmPolarCoordinate a (-1 / 2)])

theorem polarCharge_zero (a : SuzukiPositiveAperture) (u : Space a) :
    polarCharge a u 0 = ccmPolarCoordinate a (1 / 2) u :=
  rfl

theorem polarCharge_one (a : SuzukiPositiveAperture) (u : Space a) :
    polarCharge a u 1 = ccmPolarCoordinate a (-1 / 2) u :=
  rfl

/-- A vector has no charge exactly when it is polar constrained. -/
theorem polarCharge_eq_zero_iff (a : SuzukiPositiveAperture) (u : Space a) :
    polarCharge a u = 0 ↔ IsPolarConstrained a u := by
  change polarCharge a u = 0 ↔
    ccmPolarCoordinate a (1 / 2) u = 0 ∧ ccmPolarCoordinate a (-1 / 2) u = 0
  constructor
  · intro h
    exact ⟨by rw [← polarCharge_zero, h]; rfl, by rw [← polarCharge_one, h]; rfl⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · exact h0
    · exact h1

/-- Every pair of charges is carried by a vector. -/
theorem polarCharge_surjective (a : SuzukiPositiveAperture) :
    Function.Surjective (polarCharge a) := by
  intro x
  refine ⟨ccmPolarCoordinateSection a (x 0) (x 1), ?_⟩
  ext i
  fin_cases i
  · exact ccmPolarCoordinate_section_plus a (x 0) (x 1)
  · exact ccmPolarCoordinate_section_minus a (x 0) (x 1)

/-- The adjoint of the charge map sends a pair of coefficients to the forcing by the two pole
profiles. -/
theorem inner_adjoint_polarCharge (a : SuzukiPositiveAperture) (y : ChargeSpace) (v : Space a) :
    ⟪ContinuousLinearMap.adjoint (polarCharge a) y, v⟫_ℂ =
      ⟪ccmPolarForcing a (y 0, y 1), ccmArchimedeanFormToAperture a v⟫_ℂ := by
  rw [ContinuousLinearMap.adjoint_inner_left, inner_ccmPolarForcing, PiLp.inner_apply,
    Fin.sum_univ_two, polarCharge_zero, polarCharge_one]
  simp only [RCLike.inner_apply]
  ring

/-- **The polar Lagrangian** of an aperture at an energy: the pairs (charges, forcing) of the
solutions of the forced equation. -/
def polarLagrangian (a : SuzukiPositiveAperture) (E : ℝ) :
    Submodule ℂ (ChargeSpace × ChargeSpace) :=
  polarRelation (operator a E) (polarCharge a)

/-- Membership in the polar Lagrangian is the forced equation of Weil's form. -/
theorem mem_polarLagrangian_iff {a : SuzukiPositiveAperture} {E : ℝ}
    {p : ChargeSpace × ChargeSpace} :
    p ∈ polarLagrangian a E ↔ ∃ ξ : Space a, polarCharge a ξ = p.1 ∧ ∀ v : Space a,
      ccmRestrictedWeilForm a ξ v - (E : ℂ) * ⟪ccmArchimedeanFormToAperture a ξ,
          ccmArchimedeanFormToAperture a v⟫_ℂ =
        ⟪ccmPolarForcing a (p.2 0, p.2 1), ccmArchimedeanFormToAperture a v⟫_ℂ := by
  constructor
  · rintro ⟨ξ, h1, h2⟩
    refine ⟨ξ, h1, fun v => ?_⟩
    rw [← operator_mixed, h2, inner_adjoint_polarCharge]
  · rintro ⟨ξ, h1, h2⟩
    refine ⟨ξ, h1, ext_inner_right ℂ fun v => ?_⟩
    rw [operator_mixed, h2, inner_adjoint_polarCharge]

/-- **The polar Lagrangian is isotropic.** -/
theorem polarLagrangian_isotropic (a : SuzukiPositiveAperture) (E : ℝ)
    {p q : ChargeSpace × ChargeSpace} (hp : p ∈ polarLagrangian a E)
    (hq : q ∈ polarLagrangian a E) : ⟪p.2, q.1⟫_ℂ = ⟪p.1, q.2⟫_ℂ :=
  polarRelation_isotropic (operator_selfAdjoint a E) hp hq

/-- **The polar Lagrangian is a plane** in the four-dimensional space of charges and forcings. -/
theorem finrank_polarLagrangian (a : SuzukiPositiveAperture) (E : ℝ) :
    finrank ℂ (polarLagrangian a E) = 2 := by
  rw [polarLagrangian,
    finrank_polarRelation (operator_selfAdjoint a E) (one_sub_operator_compact a E),
    finrank_euclideanSpace_fin]

/-! ### The crossings with the charge axis -/

/-- The charges of the null modes. -/
def nullCharges (a : SuzukiPositiveAperture) (E : ℝ) : Submodule ℂ ChargeSpace :=
  (LinearMap.ker (operator a E : Space a →ₗ[ℂ] Space a)).map
    (polarCharge a : Space a →ₗ[ℂ] ChargeSpace)

/-- **The polar Lagrangian meets the charge axis in the charges of the null modes.** -/
theorem mem_nullCharges_iff {a : SuzukiPositiveAperture} {E : ℝ} {x : ChargeSpace} :
    x ∈ nullCharges a E ↔ (x, (0 : ChargeSpace)) ∈ polarLagrangian a E := by
  rw [polarLagrangian, mem_polarRelation_zero_right]
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨ξ, hξ, rfl⟩
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨ξ, hξ, rfl⟩

/-- The dimension of the crossing of the polar Lagrangian with the charge axis. -/
def chargedNullity (a : SuzukiPositiveAperture) (E : ℝ) : ℕ :=
  finrank ℂ (nullCharges a E)

/-- The dimension of the space of null modes without charge. -/
def neutralNullity (a : SuzukiPositiveAperture) (E : ℝ) : ℕ :=
  finrank ℂ (LinearMap.ker ((polarCharge a : Space a →ₗ[ℂ] ChargeSpace).domRestrict
    (LinearMap.ker (operator a E : Space a →ₗ[ℂ] Space a))))

/-- **The nullity is the charged nullity plus the neutral nullity.** -/
theorem weilNullity_eq_charged_add_neutral (a : SuzukiPositiveAperture) (E : ℝ) :
    weilNullity a E = chargedNullity a E + neutralNullity a E :=
  finrank_ker_eq_charged_add_neutral

/-- A crossing with the charge axis has dimension at most two. -/
theorem chargedNullity_le_two (a : SuzukiPositiveAperture) (E : ℝ) : chargedNullity a E ≤ 2 := by
  have h := finrank_map_ker_le (T := operator a E) (d := polarCharge a)
  rwa [finrank_euclideanSpace_fin] at h

/-- No null mode is neutral exactly when the neutral nullity vanishes. -/
theorem neutralNullity_eq_zero_iff (a : SuzukiPositiveAperture) (E : ℝ) :
    neutralNullity a E = 0 ↔
      ∀ u : Space a, operator a E u = 0 → IsPolarConstrained a u → u = 0 := by
  rw [neutralNullity, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot']
  constructor
  · intro h u hu hc
    exact congrArg Subtype.val (h ⟨u, hu⟩ ((polarCharge_eq_zero_iff a u).mpr hc))
  · rintro h ⟨u, hu⟩ hd
    exact Subtype.ext (h u hu ((polarCharge_eq_zero_iff a u).mp hd))

/-! ### The crossings with the forcing axis -/

/-- **The polar Lagrangian meets the forcing axis in the null modes of the constrained form**: a
vector without charge solves a forced equation exactly when Weil's form, shifted by the energy,
pairs it to zero with every vector without charge. -/
theorem exists_forcing_iff_constrained_null (a : SuzukiPositiveAperture) (E : ℝ) (ξ : Space a) :
    (∃ y : ChargeSpace, operator a E ξ = ContinuousLinearMap.adjoint (polarCharge a) y) ↔
      ∀ v : Space a, IsPolarConstrained a v →
        ccmRestrictedWeilForm a ξ v - (E : ℂ) * ⟪ccmArchimedeanFormToAperture a ξ,
          ccmArchimedeanFormToAperture a v⟫_ℂ = 0 := by
  rw [exists_eq_adjoint_iff]
  constructor
  · intro h v hv
    rw [← operator_mixed]
    exact h v ((polarCharge_eq_zero_iff a v).mpr hv)
  · intro h v hv
    rw [operator_mixed]
    exact h v ((polarCharge_eq_zero_iff a v).mp hv)

/-! ### The index along the path -/

/-- **The index at an aperture is the number of crossings of the polar Lagrangian with the charge
axis plus the neutral nullities below it.** -/
theorem negativeRank_eq_sum_charged_add_neutral (b : SuzukiPositiveAperture) (E : ℝ) :
    negativeRank b E =
      ∑ a ∈ resonantBelow b E, (chargedNullity a E + neutralNullity a E) := by
  rw [negativeRank_eq_sum_nullity]
  exact Finset.sum_congr rfl fun a _ => weilNullity_eq_charged_add_neutral a E

/-- **If no null mode below an aperture is neutral, the index is the number of crossings of the
polar Lagrangian with the charge axis.** -/
theorem negativeRank_eq_sum_chargedNullity {b : SuzukiPositiveAperture} {E : ℝ}
    (h : ∀ a : SuzukiPositiveAperture, a.1 < b.1 → ∀ u : Space a, operator a E u = 0 →
      IsPolarConstrained a u → u = 0) :
    negativeRank b E = ∑ a ∈ resonantBelow b E, chargedNullity a E := by
  rw [negativeRank_eq_sum_charged_add_neutral]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(neutralNullity_eq_zero_iff a E).mpr (h a (mem_resonantBelow.mp ha).1), add_zero]

/-- The index is at least the number of resonant apertures below. -/
theorem card_resonantBelow_le_negativeRank (b : SuzukiPositiveAperture) (E : ℝ) :
    (resonantBelow b E).card ≤ negativeRank b E := by
  rw [negativeRank_eq_sum_nullity, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun a ha => (mem_resonantBelow.mp ha).2

/-- **Without neutral null modes the index is at most twice the number of resonant apertures.** -/
theorem negativeRank_le_two_mul_card_resonantBelow {b : SuzukiPositiveAperture} {E : ℝ}
    (h : ∀ a : SuzukiPositiveAperture, a.1 < b.1 → ∀ u : Space a, operator a E u = 0 →
      IsPolarConstrained a u → u = 0) :
    negativeRank b E ≤ 2 * (resonantBelow b E).card := by
  rw [negativeRank_eq_sum_chargedNullity h, Finset.card_eq_sum_ones, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => by simpa using chargedNullity_le_two a E

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
