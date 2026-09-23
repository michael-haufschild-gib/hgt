import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarParitySourceCoupling
import GaloisForLFunctions.HTGeometry.BesselPSD

/-!
# Exact source variance and the unrestricted Weil gap

An actual constrained parity ground has a phase-independent residual variance equal to
its boundary–arithmetic source moment squared divided by the exact parity Gram factor.
Cauchy–Schwarz for the full form shifted by its unrestricted floor bounds that moment by
the constrained–unrestricted gap and the full shifted pole energy. A normalized actual
ground satisfies both formulas without an RH or source-sign premise.

The equality cases distinguish a forced constrained state from an unrestricted eigenstate.
A Hermitian two-coordinate countermodel retains a zero constrained floor, nonzero coupling,
and an attained negative unrestricted floor: variance and shifted positivity alone do not
exclude the arithmetic zero-ground alternative. No second operator application is assumed.
-/

open Complex MeasureTheory Set
open scoped InnerProduct
noncomputable section
namespace RHTower

/-- The literal parity pole, lifted into the complete form domain. -/
def ccmPolarParityFormVector (a : SuzukiPositiveAperture) (r : ℝ) :
    CCMArchimedeanFormDomain a :=
  ccmPolarFormVector a (1/2) + (r:ℂ) • ccmPolarFormVector a (-1/2)

theorem ccmArchimedeanFormToAperture_polarParity (a : SuzukiPositiveAperture) (r : ℝ) :
    ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r) =
      ccmPolarApertureVector a (1/2) + (r:ℂ) • ccmPolarApertureVector a (-1/2) := by
  simp only [ccmPolarParityFormVector, map_add, map_smul, ccmArchimedeanFormToAperture_polar]

/-- Exact norm of either parity pole; the odd Gram denominator is retained. -/
theorem norm_sq_ccmPolarParityFormVector_physical (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) :
    ‖ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)‖ ^ (2 : ℕ) =
      2*(2*Real.sinh a.1+2*a.1*r) := by
  have hn : ‖ccmPolarApertureVector a (-1/2)‖ ^ (2 : ℕ) = 2*Real.sinh a.1 := by
    have h := l2ReflectionIsometry.norm_map (ccmPolarL2Vector a (1/2))
    change ‖l2Reflection (ccmPolarL2Vector a (1/2))‖ = _ at h
    rw [l2Reflection_ccmPolarL2Vector] at h
    change ‖ccmPolarApertureVector a (-(1/2))‖ = ‖ccmPolarApertureVector a (1/2)‖ at h
    rw [show (-1/2:ℝ)=-(1/2) by ring, h, norm_sq_ccmPolarApertureVector_half]
  have hc : inner ℂ (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2)) =
      ((2*a.1:ℝ):ℂ) := by
    simpa only [neg_neg, neg_div] using inner_ccmPolarApertureVector_opposite a (-1/2)
  rw [ccmArchimedeanFormToAperture_polarParity, norm_add_sq (𝕜:=ℂ),
    inner_smul_right (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2)),
    hc, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    norm_sq_ccmPolarApertureVector_half, hn]
  rcases hr with rfl | rfl <;> simp <;> ring

/-- Every constrained vector is orthogonal to the actual parity pole. -/
theorem inner_polarParity_constrained (a : SuzukiPositiveAperture) (r : ℝ)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) :
    inner ℂ (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r))
      (ccmArchimedeanFormToAperture a u) = 0 := by
  rw [ccmArchimedeanFormToAperture_polarParity, inner_add_left,
    inner_smul_left (ccmPolarApertureVector a (-1/2)) (ccmArchimedeanFormToAperture a u),
    hu.1, hu.2, mul_zero, add_zero]

/-- The exact residual variance of an actual constrained one-profile state. No second
operator application or extra operator-domain regularity is used. -/
theorem polarSingleForcing_residual_norm_sq (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (r E : ℝ) (hr : r=1 ∨ r=-1) (c : ℂ)
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain)
    (hH : ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (E:ℂ) • ccmArchimedeanFormToAperture a u + c •
        (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2))) :
    ‖ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ -
      (E:ℂ) • ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) =
      2*‖ccmPolarBoundarySourceFunctional a u‖ ^ (2 : ℕ) / (2*Real.sinh a.1+2*a.1*r) := by
  have hc := polarSingleForcing_coefficient_eq_source_div a u hu r E hr c hm hH
  rw [hH, add_sub_cancel_left, ← ccmArchimedeanFormToAperture_polarParity,
    norm_smul, mul_pow, norm_sq_ccmPolarParityFormVector_physical a hr, hc,
    norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (polarParityGram_pos a hr), div_pow]
  field_simp [(polarParityGram_pos a hr).ne']

/-- The full operator norm splits into the ground mass and the exact source variance. -/
theorem polarSingleForcing_operator_norm_sq (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (r E : ℝ) (hr : r=1 ∨ r=-1) (c : ℂ)
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain)
    (hH : ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (E:ℂ) • ccmArchimedeanFormToAperture a u + c •
        (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2))) :
    ‖ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩‖ ^ (2 : ℕ) =
      E^(2 : ℕ)*‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) +
      2*‖ccmPolarBoundarySourceFunctional a u‖ ^ (2 : ℕ) / (2*Real.sinh a.1+2*a.1*r) := by
  have hres := polarSingleForcing_residual_norm_sq a u hu r E hr c hm hH
  rw [hH, add_sub_cancel_left, ← ccmArchimedeanFormToAperture_polarParity] at hres
  have ho : inner ℂ (ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)) = 0 := by
    rw [← inner_conj_symm (𝕜:=ℂ) (ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)),
      inner_polarParity_constrained a r u hu, map_zero]
  rw [hH, ← ccmArchimedeanFormToAperture_polarParity, norm_add_sq (𝕜:=ℂ),
    inner_smul_left (ccmArchimedeanFormToAperture a u),
    inner_smul_right (ccmArchimedeanFormToAperture a u), ho, mul_zero, mul_zero,
    show RCLike.re (0:ℂ) = (0:ℝ) from rfl, mul_zero, add_zero, hres, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Cauchy–Schwarz for the actual full form shifted by its actual unrestricted floor. -/
theorem ccmRestrictedWeil_groundShift_cauchySchwarz (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    ‖ccmRestrictedWeilForm a u v - inner ℂ
      ((ccmRestrictedWeilGroundEnergy a:ℂ) • ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a v)‖ ^ (2 : ℕ) ≤
      (ccmRestrictedWeilSourceQuadratic a u - ccmRestrictedWeilGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ)) *
      (ccmRestrictedWeilSourceQuadratic a v - ccmRestrictedWeilGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a v‖ ^ (2 : ℕ)) := by
  let K := ccmRestrictedWeilFormBirmanSchwinger a (ccmRestrictedWeilGroundEnergy a)
  have hK := (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a
    (ccmRestrictedWeilGroundEnergy a)).isSymmetric
  have hc := HTGeometry.cauchy_schwarz_psd
    (fun x y : CCMArchimedeanFormDomain a => inner ℂ y (x-K x))
    (fun x y z => by rw [map_add, add_sub_add_comm, inner_add_right])
    (fun c x y => by rw [map_smul, ← smul_sub, inner_smul_right])
    (fun x y => by
      rw [inner_conj_symm (𝕜:=ℂ) (x-K x) y, inner_sub_left, inner_sub_right]
      exact congrArg (inner ℂ x y - ·) (hK x y).symm)
    (fun x => by
      rw [ccmRestrictedWeil_shifted_diagonal]
      exact sub_nonneg.mpr (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a x)) u v
  change ‖inner ℂ v (u-K u)‖ ^ (2 : ℕ) ≤ _ at hc
  rw [ccmRestrictedWeil_shifted_diagonal, ccmRestrictedWeil_shifted_diagonal] at hc
  rw [ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger]
  change ‖inner ℂ (u-K u) v‖ ^ (2 : ℕ) ≤ _
  rw [← inner_conj_symm (𝕜:=ℂ) (u-K u) v, norm_conj]
  exact hc

private theorem actual_operator_form (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a)
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain) :
    ccmRestrictedWeilForm a u v = inner ℂ
      (ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩)
      (ccmArchimedeanFormToAperture a v) := by
  obtain ⟨w,hw,hrep⟩ := ccmRestrictedWeilOperator_exists_completeFormLift_mixed a
    ⟨ccmArchimedeanFormToAperture a u,hm⟩
  have heq : w=u := ccmArchimedeanFormToAperture_injective a hw
  simpa only [heq] using hrep v

private theorem forcing_shifted_pole_pair (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (r E m : ℝ) (hr : r=1 ∨ r=-1) (c : ℂ)
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain)
    (hH : ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (E:ℂ) • ccmArchimedeanFormToAperture a u + c •
        (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2))) :
    ccmRestrictedWeilForm a u (ccmPolarParityFormVector a r) -
      inner ℂ ((m:ℂ) • ccmArchimedeanFormToAperture a u)
        (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)) =
      2 * (starRingEnd ℂ) (ccmPolarBoundarySourceFunctional a u) := by
  have hc := polarSingleForcing_coefficient_eq_source_div a u hu r E hr c hm hH
  have hd : (((2*Real.sinh a.1+2*a.1*r:ℝ):ℂ)) ≠ 0 := by
    exact_mod_cast (polarParityGram_pos a hr).ne'
  have hmul := congrArg (starRingEnd ℂ) ((eq_div_iff hd).mp hc)
  rw [map_mul, Complex.conj_ofReal] at hmul
  have ho : inner ℂ (ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)) = 0 := by
    rw [← inner_conj_symm (𝕜:=ℂ) (ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)),
      inner_polarParity_constrained a r u hu, map_zero]
  rw [actual_operator_form a u _ hm, hH,
    ← ccmArchimedeanFormToAperture_polarParity, inner_add_left,
    inner_smul_left (ccmArchimedeanFormToAperture a u),
    inner_smul_left (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)),
    inner_smul_left (ccmArchimedeanFormToAperture a u), ho, mul_zero, mul_zero,
    zero_add, sub_zero, inner_self_eq_norm_sq_to_K]
  change (starRingEnd ℂ) c *
    (‖ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)‖:ℂ)^(2 : ℕ) = _
  rw [← Complex.ofReal_pow, norm_sq_ccmPolarParityFormVector_physical a hr]
  push_cast at hmul ⊢
  linear_combination 2*hmul

/-- The selected constrained ground's literal source moment is bounded by the actual
unrestricted spectral gap and the full shifted pole energy, retaining all source terms. -/
theorem polarGround_source_gap_bound (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (r : ℝ) (hr : r=1 ∨ r=-1) (c : ℂ)
    (hground : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ))
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain)
    (hH : ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (ccmRestrictedWeilPolarGroundEnergy a:ℂ) • ccmArchimedeanFormToAperture a u + c •
        (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2))) :
    4*‖ccmPolarBoundarySourceFunctional a u‖ ^ (2 : ℕ) ≤
      (ccmRestrictedWeilPolarGroundEnergy a-ccmRestrictedWeilGroundEnergy a) *
      ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) *
      (ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) -
        2*ccmRestrictedWeilGroundEnergy a*(2*Real.sinh a.1+2*a.1*r)) := by
  have h := ccmRestrictedWeil_groundShift_cauchySchwarz a u (ccmPolarParityFormVector a r)
  rw [forcing_shifted_pole_pair a u hu r (ccmRestrictedWeilPolarGroundEnergy a)
    (ccmRestrictedWeilGroundEnergy a) hr c hm hH, norm_mul, norm_conj, norm_ofNat,
    mul_pow, hground, norm_sq_ccmPolarParityFormVector_physical a hr] at h
  convert h using 1 <;> ring

/-- The full shifted pole energy on the right side of the source estimate is nonnegative. -/
theorem polarParity_shifted_energy_nonneg (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) :
    0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) -
      2*ccmRestrictedWeilGroundEnergy a*(2*Real.sinh a.1+2*a.1*r) := by
  have h := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a
    (ccmPolarParityFormVector a r)
  rw [norm_sq_ccmPolarParityFormVector_physical a hr] at h
  nlinarith

/-- Exact integral version of the variational comparison, with both boundary and all
arithmetic errors retained before estimation. -/
theorem polarGround_parityIntegral_gap_bound (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (r : ℝ) (hr : r=1 ∨ r=-1) (c : ℂ)
    (hpar : ccmArchimedeanFormReflection a u = (r:ℂ) • u)
    (hground : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ))
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain)
    (hH : ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (ccmRestrictedWeilPolarGroundEnergy a:ℂ) • ccmArchimedeanFormToAperture a u + c •
        (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2))) :
    ‖∫ x : ℝ, (centralInterval a.1).indicator (ccmPolarParityBoundaryProfile a r) x *
        (ccmArchimedeanFormToAperture a u : SoninL2) x‖ ^ (2 : ℕ) ≤
      (ccmRestrictedWeilPolarGroundEnergy a-ccmRestrictedWeilGroundEnergy a) *
      ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) *
      (ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) -
        2*ccmRestrictedWeilGroundEnergy a*(2*Real.sinh a.1+2*a.1*r)) := by
  have h := polarGround_source_gap_bound a u hu r hr c hground hm hH
  have he := ccmPolarParityBoundarySourceFunctional_eq_integral a r u
  rw [ccmPolarParityBoundarySourceFunctional_on_parity a hr u hpar] at he
  rw [← he, norm_mul, norm_ofNat, mul_pow]
  convert h using 1
  ring

/-- Nonzero source coupling of a constrained ground forces a strictly lower unrestricted floor. -/
theorem polarGround_unrestricted_lt_of_source_ne_zero (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (r : ℝ) (hr : r=1 ∨ r=-1) (c : ℂ)
    (hground : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ))
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain)
    (hH : ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (ccmRestrictedWeilPolarGroundEnergy a:ℂ) • ccmArchimedeanFormToAperture a u + c •
        (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2)))
    (hF : ccmPolarBoundarySourceFunctional a u ≠ 0) :
    ccmRestrictedWeilGroundEnergy a < ccmRestrictedWeilPolarGroundEnergy a := by
  have h := polarGround_source_gap_bound a u hu r hr c hground hm hH
  have hle := ccmRestrictedWeilGroundEnergy_le_polar a
  have hp := norm_pos_iff.mpr hF
  by_contra hn
  have heq := le_antisymm hle (not_lt.mp hn)
  rw [heq, sub_self, zero_mul, zero_mul] at h
  nlinarith

/-- If both floors agree, every constrained one-profile ground has zero source moment. -/
theorem polarGround_source_eq_zero_of_floors_eq (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (r : ℝ) (hr : r=1 ∨ r=-1) (c : ℂ)
    (hground : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ))
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain)
    (hH : ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (ccmRestrictedWeilPolarGroundEnergy a:ℂ) • ccmArchimedeanFormToAperture a u + c •
        (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2)))
    (heq : ccmRestrictedWeilGroundEnergy a = ccmRestrictedWeilPolarGroundEnergy a) :
    ccmPolarBoundarySourceFunctional a u = 0 := by
  by_contra hF
  have h := polarGround_unrestricted_lt_of_source_ne_zero a u hu r hr c hground hm hH hF
  rw [heq] at h
  exact (lt_irrefl _ h)

/-- The variance vanishes precisely when the constrained state is an unrestricted eigenvector. -/
theorem polarSingleForcing_eigen_iff_source_zero (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (r E : ℝ) (hr : r=1 ∨ r=-1) (c : ℂ)
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain)
    (hH : ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (E:ℂ) • ccmArchimedeanFormToAperture a u + c •
        (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2))) :
    ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (E:ℂ) • ccmArchimedeanFormToAperture a u ↔ ccmPolarBoundarySourceFunctional a u = 0 := by
  constructor
  · intro he
    have h := polarSingleForcing_residual_norm_sq a u hu r E hr c hm hH
    rw [he, sub_self, norm_zero, zero_pow (by decide)] at h
    have hn : 2*‖ccmPolarBoundarySourceFunctional a u‖ ^ (2 : ℕ) = 0 :=
      (div_eq_zero_iff).mp h.symm |>.resolve_right (polarParityGram_pos a hr).ne'
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ccmPolarBoundarySourceFunctional a u)])
  · intro hF
    have hc := polarSingleForcing_coefficient_eq_source_div a u hu r E hr c hm hH
    rw [hF, zero_div] at hc
    simpa only [hc, zero_smul, add_zero] using hH

/-- A physically normalized parity ground exists in the actual operator domain. -/
theorem exists_normalized_polarGround_singleProfile_forcing (a : SuzukiPositiveAperture) :
    ∃ (u : CCMArchimedeanFormDomain a) (r : ℝ) (c : ℂ),
      (r=1 ∨ r=-1) ∧ IsPolarConstrained a u ∧
      ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
      ccmArchimedeanFormReflection a u = (r:ℂ) • u ∧
      ccmRestrictedWeilSourceQuadratic a u = ccmRestrictedWeilPolarGroundEnergy a ∧
      ∃ hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain,
        ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
          (ccmRestrictedWeilPolarGroundEnergy a:ℂ) • ccmArchimedeanFormToAperture a u + c •
            (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2)) := by
  obtain ⟨u,r,c,hr,hu,hne,hpar,hQ,hm,hH⟩ := exists_polarGround_singleProfile_forcing a
  let s : ℂ := (‖ccmArchimedeanFormToAperture a u‖:ℂ)⁻¹
  let v : CCMArchimedeanFormDomain a := s • u
  have hp := norm_pos_iff.mpr hne
  have hn : ‖ccmArchimedeanFormToAperture a v‖ = 1 := by
    rw [show v=s • u from rfl, map_smul, norm_smul]
    simp only [s, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    exact inv_mul_cancel₀ hp.ne'
  have hvQ : ccmRestrictedWeilSourceQuadratic a v = ccmRestrictedWeilPolarGroundEnergy a := by
    rw [show v=s • u from rfl, ccmRestrictedWeilSourceQuadratic_smul, hQ]
    simp only [s, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    field_simp [hp.ne']
  have hvm : ccmArchimedeanFormToAperture a v ∈ (ccmRestrictedWeilOperator a).domain := by
    rw [show v=s • u from rfl, map_smul]
    exact (ccmRestrictedWeilOperator a).domain.smul_mem s hm
  refine ⟨v,r,s*c,hr,hu.smul s,hn,?_,hvQ,hvm,?_⟩
  · change ccmArchimedeanFormReflection a (s • u) = (r:ℂ) • (s • u)
    rw [map_smul, hpar, smul_comm]
  · have hvsub : (⟨ccmArchimedeanFormToAperture a v,hvm⟩ :
        (ccmRestrictedWeilOperator a).domain) = s • ⟨ccmArchimedeanFormToAperture a u,hm⟩ := by
      apply Subtype.ext
      exact map_smul (ccmArchimedeanFormToAperture a) s u
    rw [hvsub, LinearPMap.map_smul, hH, smul_add, ← smul_smul]
    congr 1
    rw [show v=s • u from rfl, map_smul, smul_comm]

/-- Unconditional actual-source witness: a normalized parity ground obeys the exact
variance identity and the unrestricted-gap bound at every positive aperture. -/
theorem exists_normalized_polarGround_source_variance_gap (a : SuzukiPositiveAperture) :
    ∃ (u : CCMArchimedeanFormDomain a) (r : ℝ),
      (r=1 ∨ r=-1) ∧ IsPolarConstrained a u ∧
      ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
      ccmArchimedeanFormReflection a u = (r:ℂ) • u ∧
      ccmRestrictedWeilSourceQuadratic a u = ccmRestrictedWeilPolarGroundEnergy a ∧
      4*‖ccmPolarBoundarySourceFunctional a u‖ ^ (2 : ℕ) ≤
        (ccmRestrictedWeilPolarGroundEnergy a-ccmRestrictedWeilGroundEnergy a) *
        (ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) -
          2*ccmRestrictedWeilGroundEnergy a*(2*Real.sinh a.1+2*a.1*r)) ∧
      ∃ hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain,
        ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
          (ccmRestrictedWeilPolarGroundEnergy a:ℂ) • ccmArchimedeanFormToAperture a u +
            (ccmPolarBoundarySourceFunctional a u / ((2*Real.sinh a.1+2*a.1*r:ℝ):ℂ)) •
              (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2)) ∧
        ‖ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩‖ ^ (2 : ℕ) =
          (ccmRestrictedWeilPolarGroundEnergy a)^(2 : ℕ) +
          2*‖ccmPolarBoundarySourceFunctional a u‖ ^ (2 : ℕ) / (2*Real.sinh a.1+2*a.1*r) := by
  obtain ⟨u,r,c,hr,hu,hn,hpar,hQ,hm,hH⟩ := exists_normalized_polarGround_singleProfile_forcing a
  have hground : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) := by
    simpa only [hn, one_pow, mul_one] using hQ
  refine ⟨u,r,hr,hu,hn,hpar,hQ,?_,hm,?_,?_⟩
  · simpa only [hn, one_pow, mul_one] using
      polarGround_source_gap_bound a u hu r hr c hground hm hH
  · rwa [← polarSingleForcing_coefficient_eq_source_div a u hu r
      (ccmRestrictedWeilPolarGroundEnergy a) hr c hm hH]
  · simpa only [hn, one_pow, mul_one] using polarSingleForcing_operator_norm_sq a u hu r
      (ccmRestrictedWeilPolarGroundEnergy a) hr c hm hH

/-- A Hermitian two-coordinate model has a zero constrained floor, nonzero mixed source,
and a positive semidefinite shift with an attained negative unrestricted floor. Hence
the variance identity and shifted positivity alone do not exclude a zero constrained
ground. This is a model obstruction, not an assertion about the arithmetic operator. -/
theorem zeroGround_nonzeroSource_shiftedPositive_model :
    ∃ B : (ℂ × ℂ) → (ℂ × ℂ) → ℂ,
      (∀ x y z, B (x+y) z = B x z + B y z) ∧
      (∀ (c:ℂ) x y, B (c • x) y = c * B x y) ∧
      (∀ x y, B y x = (starRingEnd ℂ) (B x y)) ∧
      (∀ x, -(‖x.1‖^(2 : ℕ)+‖x.2‖^(2 : ℕ)) ≤ (B x x).re) ∧
      (∀ z:ℂ, B (z,0) (z,0) = 0) ∧
      B (1,0) (0,1) = 1 ∧
      B (1,-1) (1,-1) = -2 ∧ ‖(1:ℂ)‖^(2 : ℕ)+‖(-1:ℂ)‖^(2 : ℕ) = 2 := by
  let B : (ℂ × ℂ) → (ℂ × ℂ) → ℂ :=
    fun x y => x.1*(starRingEnd ℂ) y.2 + x.2*(starRingEnd ℂ) y.1
  refine ⟨B,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x y z
    dsimp [B]
    ring
  · intro c x y
    dsimp [B]
    ring
  · intro x y
    simp only [B, map_add, map_mul, Complex.conj_conj]
    ring
  · intro x
    simp only [B, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (x.1.re+x.2.re), sq_nonneg (x.1.im+x.2.im)]
  · intro z
    simp [B]
  · norm_num [B]
  · norm_num [B]
  · norm_num

end RHTower
