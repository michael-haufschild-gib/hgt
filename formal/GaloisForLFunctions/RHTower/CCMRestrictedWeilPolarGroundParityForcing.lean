import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarGroundForcing
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundParity

/-!
# Pure-parity constrained Weil grounds and their single-profile forcing

The full-domain reflection swaps the pole coordinates and preserves their common kernel.
The exact energy and physical-mass splitting therefore puts every nonzero parity component
of a constrained minimizer at the same ground energy. At least one such component is nonzero.

Complex polarization upgrades the corpus's quadratic reflection law to the complete
sesquilinear form. Hence a pure-parity forced state has equal or opposite pole coefficients.
Every aperture consequently has a nonzero constrained operator ground forced by a single
profile `p₊+p₋` or `p₊-p₋`. No simplicity, parity selection, regularity, or RH hypothesis enters.
The scalar forcing is retained; this does not claim an unrestricted zero eigenstate or RH.
-/

open Complex MeasureTheory Set
open scoped InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

theorem ccmPolarCoordinate_reflection (a : SuzukiPositiveAperture) (s : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    ccmPolarCoordinate a s (ccmArchimedeanFormReflection a u) = ccmPolarCoordinate a (-s) u := by
  change inner ℂ (ccmPolarL2Vector a s)
    (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u) : SoninL2) =
      inner ℂ (ccmPolarL2Vector a (-s)) (ccmArchimedeanFormToAperture a u : SoninL2)
  rw [ccmArchimedeanFormToAperture_reflection, inner_ccmPolarL2Vector_reflection]

theorem IsPolarConstrained.reflection {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} (hu : IsPolarConstrained a u) :
    IsPolarConstrained a (ccmArchimedeanFormReflection a u) := by
  change ccmPolarCoordinate a (1 / 2) (ccmArchimedeanFormReflection a u) = 0 ∧
    ccmPolarCoordinate a (-1 / 2) (ccmArchimedeanFormReflection a u) = 0
  rw [ccmPolarCoordinate_reflection, ccmPolarCoordinate_reflection]
  constructor
  · simpa only [neg_div] using (show ccmPolarCoordinate a (-1 / 2) u = 0 from hu.2)
  · simpa only [neg_div, neg_neg] using (show ccmPolarCoordinate a (1 / 2) u = 0 from hu.1)

theorem IsPolarConstrained.evenPart {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} (hu : IsPolarConstrained a u) :
    IsPolarConstrained a (ccmRestrictedWeilEvenPart a u) :=
  (ccmPolarConstraintSubmodule a).smul_mem _
    ((ccmPolarConstraintSubmodule a).add_mem hu hu.reflection)

theorem IsPolarConstrained.oddPart {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} (hu : IsPolarConstrained a u) :
    IsPolarConstrained a (ccmRestrictedWeilOddPart a u) :=
  (ccmPolarConstraintSubmodule a).smul_mem _
    ((ccmPolarConstraintSubmodule a).sub_mem hu hu.reflection)

/-- Each parity component of a constrained minimizer is a constrained minimizer. -/
theorem polarGround_evenOdd_components (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (hground : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ)) :
    ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilEvenPart a u) =
      ccmRestrictedWeilPolarGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a (ccmRestrictedWeilEvenPart a u)‖ ^ (2 : ℕ) ∧
    ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilOddPart a u) =
      ccmRestrictedWeilPolarGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a (ccmRestrictedWeilOddPart a u)‖ ^ (2 : ℕ) := by
  have he := ccmRestrictedWeilPolarGroundEnergy_mul_le a _ hu.evenPart
  have ho := ccmRestrictedWeilPolarGroundEnergy_mul_le a _ hu.oddPart
  have henergy := ccmRestrictedWeilSourceQuadratic_evenOdd_split a u
  have hnorm := norm_sq_ccmArchimedeanFormToAperture_evenOdd a u
  have hmass := congrArg (fun x => ccmRestrictedWeilPolarGroundEnergy a * x) hnorm
  rw [mul_add] at hmass
  constructor <;> nlinarith

/-- A nonzero constrained ground of pure reflection parity exists at every aperture. -/
theorem exists_polar_pureParity_groundFormState (a : SuzukiPositiveAperture) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
      (ccmArchimedeanFormReflection a u = u ∨ ccmArchimedeanFormReflection a u = -u) ∧
      ccmRestrictedWeilSourceQuadratic a u =
        ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) := by
  obtain ⟨u, hu, hn, hQ⟩ := exists_polarConstrained_groundState a
  have hcomponents := polarGround_evenOdd_components a u hu (by simpa only [hn, one_pow, mul_one] using hQ)
  have hne : ccmArchimedeanFormToAperture a u ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  let e := ccmRestrictedWeilEvenPart a u
  let o := ccmRestrictedWeilOddPart a u
  by_cases he : ccmArchimedeanFormToAperture a e = 0
  · refine ⟨o, hu.oddPart, ?_, Or.inr (ccmArchimedeanFormReflection_oddPart a u), hcomponents.2⟩
    intro ho
    apply hne
    rw [← ccmRestrictedWeilEvenPart_add_oddPart a u, map_add]
    exact (congrArg₂ (· + ·) he ho).trans (zero_add _)
  · exact ⟨e, hu.evenPart, he, Or.inl (ccmArchimedeanFormReflection_evenPart a u), hcomponents.1⟩

private theorem weil_form_identity (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    inner ℂ ((ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) - ccmRestrictedWeilFormBirmanSchwinger a 0) u) v =
      ccmRestrictedWeilForm a u v := by
  simpa only [Complex.ofReal_zero, zero_smul, inner_zero_left, sub_zero] using
    (ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger a 0 u v).symm

/-- Reflection preserves the full sesquilinear form, not only its real diagonal. -/
theorem ccmRestrictedWeilForm_reflection (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a (ccmArchimedeanFormReflection a u)
      (ccmArchimedeanFormReflection a v) = ccmRestrictedWeilForm a u v := by
  let T : CCMArchimedeanFormDomain a →ₗ[ℂ] CCMArchimedeanFormDomain a :=
    (ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) - ccmRestrictedWeilFormBirmanSchwinger a 0).toLinearMap
  let R := ccmArchimedeanFormReflection a
  have hT : T.IsSymmetric := by
    intro x y
    change inner ℂ (x - ccmRestrictedWeilFormBirmanSchwinger a 0 x) y =
      inner ℂ x (y - ccmRestrictedWeilFormBirmanSchwinger a 0 y)
    have hs := (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a 0).isSymmetric x y
    change inner ℂ (ccmRestrictedWeilFormBirmanSchwinger a 0 x) y =
      inner ℂ x (ccmRestrictedWeilFormBirmanSchwinger a 0 y) at hs
    rw [inner_sub_left, inner_sub_right, hs]
  have hdiag (z : CCMArchimedeanFormDomain a) :
      inner ℂ (T z) z = (ccmRestrictedWeilSourceQuadratic a z : ℂ) := by
    have hr := hT.coe_re_inner_apply_self z
    change ((inner ℂ (T z) z).re : ℂ) = inner ℂ (T z) z at hr
    rw [show inner ℂ (T z) z = ccmRestrictedWeilForm a z z from weil_form_identity a z z,
      ccmRestrictedWeilForm_self_re_eq_source] at hr
    exact (weil_form_identity a z z).trans hr.symm
  have hdiagr (z : CCMArchimedeanFormDomain a) :
      inner ℂ (T (R z)) (R z) = inner ℂ (T z) z := by
    rw [hdiag, hdiag]
    exact congrArg Complex.ofReal (ccmRestrictedWeilSourceQuadratic_reflection a z)
  have h1 := inner_map_polarization' T (R u) (R v)
  have h2 := inner_map_polarization' T u v
  rw [← map_add, ← map_sub, ← map_smul R, ← map_add, ← map_sub] at h1
  simp only [hdiagr] at h1
  exact (weil_form_identity a (R u) (R v)).symm.trans
    (h1.trans (h2.symm.trans (weil_form_identity a u v)))

end RHTower

namespace RHTower

private theorem physical_inner_reflection (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u))
      (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a v)) =
        inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
  change inner ℂ
    (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u) : SoninL2)
    (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a v) : SoninL2) = _
  rw [ccmArchimedeanFormToAperture_reflection, ccmArchimedeanFormToAperture_reflection]
  exact l2ReflectionIsometry.inner_map_map _ _

private theorem shifted_pair_reflection (a : SuzukiPositiveAperture) (E : ℝ)
    (u v : CCMArchimedeanFormDomain a) :
    inner ℂ ((ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) - ccmRestrictedWeilFormBirmanSchwinger a E)
      (ccmArchimedeanFormReflection a u)) (ccmArchimedeanFormReflection a v) =
    inner ℂ ((ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) - ccmRestrictedWeilFormBirmanSchwinger a E) u) v := by
  rw [← ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger,
    ← ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger,
    ccmRestrictedWeilForm_reflection]
  rw [inner_smul_left (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u))
    (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a v)) (E : ℂ),
    inner_smul_left (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) (E : ℂ),
    physical_inner_reflection]

/-- Reflection of a forced state fixes the relation between its two pole coefficients:
even forcing has equal coefficients and odd forcing has opposite coefficients. -/
theorem polarForcing_coefficient_reflection (a : SuzukiPositiveAperture) (E r : ℝ)
    (hr : r ^ (2 : ℕ) = 1) (u : CCMArchimedeanFormDomain a)
    (hRu : ccmArchimedeanFormReflection a u = (r : ℂ) • u) (c : ℂ × ℂ)
    (hc : ∀ v, ccmRestrictedWeilForm a u v =
      inner ℂ ((E : ℂ) • ccmArchimedeanFormToAperture a u + ccmPolarForcing a c)
        (ccmArchimedeanFormToAperture a v)) : c.2 = (r : ℂ) * c.1 := by
  let T : CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
    ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) - ccmRestrictedWeilFormBirmanSchwinger a E
  have hpair (v : CCMArchimedeanFormDomain a) :
      inner ℂ (T u) v = inner ℂ (ccmPolarForcing a c) (ccmArchimedeanFormToAperture a v) := by
    rw [← ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger,
      hc, inner_add_left]
    ring
  let v := ccmPolarCoordinateSection a 1 0
  have hp := shifted_pair_reflection a E u v
  rw [hRu] at hp
  change inner ℂ (T ((r : ℂ) • u)) (ccmArchimedeanFormReflection a v) = inner ℂ (T u) v at hp
  rw [map_smul, inner_smul_left (T u) (ccmArchimedeanFormReflection a v) (r : ℂ),
    Complex.conj_ofReal, hpair, hpair, inner_ccmPolarForcing, inner_ccmPolarForcing,
    ccmPolarCoordinate_reflection, ccmPolarCoordinate_reflection] at hp
  have hminus : ccmPolarCoordinate a (-(1 / 2)) (ccmPolarCoordinateSection a 1 0) = 0 := by
    simpa only [neg_div] using ccmPolarCoordinate_section_minus a 1 0
  simp only [v, neg_div, neg_neg, ccmPolarCoordinate_section_plus,
    hminus, mul_one, mul_zero, add_zero, zero_add] at hp
  have hconj := congrArg (starRingEnd ℂ) hp
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj] at hconj
  have hrr : (r : ℂ) ^ (2 : ℕ) = 1 := by exact_mod_cast hr
  calc
    c.2 = (r : ℂ) * ((r : ℂ) * c.2) := by rw [← mul_assoc, ← pow_two, hrr, one_mul]
    _ = (r : ℂ) * c.1 := congrArg ((r : ℂ) * ·) hconj

/-- At every aperture the actual constrained ground has a one-profile forced operator
realization in one reflection sector. No parity choice or source sign is assumed. -/
theorem exists_polarGround_singleProfile_forcing (a : SuzukiPositiveAperture) :
    ∃ (u : CCMArchimedeanFormDomain a) (r : ℝ) (c : ℂ),
      (r = 1 ∨ r = -1) ∧ IsPolarConstrained a u ∧
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
      ccmArchimedeanFormReflection a u = (r : ℂ) • u ∧
      ccmRestrictedWeilSourceQuadratic a u =
        ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ∧
      ∃ hmem : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain,
        ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u, hmem⟩ =
          (ccmRestrictedWeilPolarGroundEnergy a : ℂ) • ccmArchimedeanFormToAperture a u +
            c • (ccmPolarApertureVector a (1 / 2) + (r : ℂ) • ccmPolarApertureVector a (-1 / 2)) := by
  obtain ⟨u, hu, hne, hparity, hQ⟩ := exists_polar_pureParity_groundFormState a
  obtain ⟨r, hr, hRu⟩ : ∃ r : ℝ, (r = 1 ∨ r = -1) ∧
      ccmArchimedeanFormReflection a u = (r : ℂ) • u := by
    rcases hparity with he | ho
    · exact ⟨1, Or.inl rfl, by simpa only [Complex.ofReal_one, one_smul] using he⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul] using ho⟩
  have hrsq : r ^ (2 : ℕ) = 1 := by rcases hr with rfl | rfl <;> norm_num
  obtain ⟨c, hc, _⟩ := existsUnique_polarGround_forcing_form a u hu hQ
  have hc2 := polarForcing_coefficient_reflection a _ r hrsq u hRu c hc
  obtain ⟨hm, hA⟩ := boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (ccmArchimedeanFormToAperture a) (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a) (denseRange_ccmArchimedeanFormToAperture a)
    u ((ccmRestrictedWeilPolarGroundEnergy a : ℂ) • ccmArchimedeanFormToAperture a u +
      ccmPolarForcing a c) hc
  refine ⟨u, r, c.1, hr, hu, hne, hRu, hQ, hm, hA.trans ?_⟩
  rw [ccmPolarForcing, hc2, smul_add, smul_smul, mul_comm c.1]

end RHTower
