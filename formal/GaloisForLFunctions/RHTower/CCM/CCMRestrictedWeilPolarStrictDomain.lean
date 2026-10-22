import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFormTranslation
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilCanonicalGroundHeadEnergy
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarMultiplierCriterion
import GaloisForLFunctions.HTGeometry.L2TranslationPolynomialIndependence
import GaloisForLFunctions.HTGeometry.CompactConstrainedRadical

/-!
# Strict domain decrease of the actual pole-constrained Weil ground

Every strict increase of aperture strictly lowers the attained constrained ground energy.
If two apertures had the same ground energy `E`, every small translate of a normalized
minimizer would lie in the constrained radical of the shifted form `Q-E‖·‖²`. Compactness
makes this radical finite-dimensional, while Fourier polynomial independence supplies
arbitrarily many independent translates.

Consequently RH is equivalent to strict positive ground energy at every finite aperture.
Otherwise exactly one aperture has zero ground energy, with positive floors below and
negative floors above. Every nonzero smooth strict-interior constrained test lies strictly
above its aperture's ground energy, even away from the zero threshold. These conclusions
classify the remaining sign problem; they do not prove RH or assert a zero threshold exists.
-/

open Complex MeasureTheory Set
open scoped InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

/-- The closed complex sector with both exponential pole coordinates zero. -/
def ccmPolarConstraintSubmodule (a : SuzukiPositiveAperture) :
    Submodule ℂ (CCMArchimedeanFormDomain a) where
  carrier := {u | IsPolarConstrained a u}
  zero_mem' := by simp [IsPolarConstrained]
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, IsPolarConstrained, map_add, inner_add_right,
      hu.1, hu.2, hv.1, hv.2, add_zero, and_self]
  smul_mem' := fun c u hu => hu.smul c

theorem isClosed_ccmPolarConstraintSubmodule (a : SuzukiPositiveAperture) :
    IsClosed (ccmPolarConstraintSubmodule a : Set (CCMArchimedeanFormDomain a)) := by
  change IsClosed ({u | inner ℂ (ccmPolarApertureVector a (1 / 2))
      (ccmArchimedeanFormToAperture a u) = 0} ∩
    {u | inner ℂ (ccmPolarApertureVector a (-1 / 2))
      (ccmArchimedeanFormToAperture a u) = 0})
  exact (isClosed_eq (continuous_const.inner (ccmArchimedeanFormToAperture a).continuous)
    continuous_const).inter
      (isClosed_eq (continuous_const.inner (ccmArchimedeanFormToAperture a).continuous)
        continuous_const)

/-- Exact energy-shift identity for the literal source and actual compact pencil. -/
theorem ccmRestrictedWeil_shifted_diagonal (a : SuzukiPositiveAperture) (E : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    (inner ℂ u (u - ccmRestrictedWeilFormBirmanSchwinger a E u)).re =
      ccmRestrictedWeilSourceQuadratic a u - E * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) := by
  have hmass : (inner ℂ ((E : ℂ) • ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a u)).re =
      E * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) := by
    rw [inner_smul_left (ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a u) (E : ℂ), Complex.conj_ofReal,
      inner_self_eq_norm_sq_to_K]
    change (((E : ℂ) * (‖ccmArchimedeanFormToAperture a u‖ : ℂ) ^ (2 : ℕ)).re) = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hid := congrArg Complex.re
    (ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger a E u u)
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    Complex.sub_re, ccmRestrictedWeilForm_self_re_eq_source, hmass] at hid
  exact (inner_re_symm (𝕜 := ℂ) u (u - ccmRestrictedWeilFormBirmanSchwinger a E u)).trans
    hid.symm

/-- Every strict increase of aperture strictly decreases the actual constrained ground energy.
The proof uses full-domain translation and compactness, without ground-state smoothness. -/
theorem strictAnti_ccmRestrictedWeilPolarGroundEnergy :
    StrictAnti ccmRestrictedWeilPolarGroundEnergy := by
  intro a b hab
  have habv : a.1 < b.1 := hab
  have hle := ccmRestrictedWeilPolarGroundEnergy_antitone habv.le
  by_contra hn
  have heq : ccmRestrictedWeilPolarGroundEnergy b = ccmRestrictedWeilPolarGroundEnergy a :=
    le_antisymm hle (not_lt.mp hn)
  let E := ccmRestrictedWeilPolarGroundEnergy a
  let S := ccmPolarConstraintSubmodule b
  let K := ccmRestrictedWeilFormBirmanSchwinger b E
  let N := compactConstrainedRadical S K
  haveI : FiniteDimensional ℂ N := finiteDimensional_compactConstrainedRadical S
    (isClosed_ccmPolarConstraintSubmodule b) K
    (isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger b E)
  obtain ⟨u, hu, hun, huQ⟩ := exists_polarConstrained_groundState a
  let n := Module.finrank ℂ N + 1
  let h : ℝ := (b.1 - a.1) / (n + 1)
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hh : 0 < h := div_pos (sub_pos.mpr habv) hn0
  have hfit : ∀ i : Fin n, a.1 + |(i : ℝ) * h| ≤ b.1 := by
    intro i
    have hi : (i : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : i.val ≤ n + 1)
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg i.val) hh.le)]
    have hprod := mul_le_mul_of_nonneg_right hi hh.le
    have he : ((n : ℝ) + 1) * h = b.1 - a.1 := by
      dsimp [h]
      exact mul_div_cancel₀ _ hn0.ne'
    linarith
  let v (i : Fin n) := ccmArchimedeanFormTranslate ((i : ℝ) * h) (hfit i) u
  have hvN : ∀ i, v i ∈ N := by
    intro i
    apply mem_compactConstrainedRadical_of_null S K
      (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint b E)
    · intro w hw
      rw [ccmRestrictedWeil_shifted_diagonal]
      have hf := ccmRestrictedWeilPolarGroundEnergy_mul_le b w hw
      rw [heq] at hf
      exact sub_nonneg.mpr hf
    · exact hu.translate _ _
    · change (inner ℂ (v i) (v i - ccmRestrictedWeilFormBirmanSchwinger b E (v i))).re = 0
      rw [ccmRestrictedWeil_shifted_diagonal,
        ccmRestrictedWeilSourceQuadratic_translate _ _ u hu,
        norm_ccmArchimedeanFormTranslate_physical, hun, huQ, one_pow, mul_one, sub_self]
  let w (i : Fin n) : N := ⟨v i, hvN i⟩
  have hune : (ccmArchimedeanFormToAperture a u : SoninL2) ≠ 0 := by
    intro hz
    have hnorm : ‖(ccmArchimedeanFormToAperture a u : SoninL2)‖ = 1 := hun
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hli := linearIndependent_arithmetic_L2_translates n hh.ne' hune
  have hwli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hm := congrArg (fun z : N =>
      (ccmArchimedeanFormToAperture b z.1 : SoninL2)) hc
    have hm' : ∑ i : Fin n, c i •
        (ccmArchimedeanFormToAperture b (v i) : SoninL2) = 0 := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        map_sum, map_smul, map_zero] using hm
    simp only [v, ccmArchimedeanFormTranslate_physical] at hm'
    exact (Fintype.linearIndependent_iff.mp hli) c hm'
  have hdim := hwli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hdim
  dsimp [n] at hdim
  omega

end RHTower

namespace RHTower

/-- A constrained zero ground forces strict negativity at every larger aperture. -/
theorem polarGroundEnergy_neg_above_zero {a b : SuzukiPositiveAperture}
    (ha : ccmRestrictedWeilPolarGroundEnergy a = 0) (hab : a.1 < b.1) :
    ccmRestrictedWeilPolarGroundEnergy b < 0 := by
  simpa only [ha] using strictAnti_ccmRestrictedWeilPolarGroundEnergy hab

/-- Nonnegativity at all apertures automatically gives strict positivity at every finite one. -/
theorem riemannHypothesis_iff_polarGroundEnergy_pos :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture,
      0 < ccmRestrictedWeilPolarGroundEnergy a := by
  constructor
  · intro hRH a
    let b : SuzukiPositiveAperture := ⟨a.1 + 1, by linarith [a.2]⟩
    have hab : a < b := by change a.1 < a.1 + 1; linarith
    exact lt_of_le_of_lt ((riemannHypothesis_iff_polarGroundEnergy_nonneg.mp hRH) b)
      (strictAnti_ccmRestrictedWeilPolarGroundEnergy hab)
  · intro h
    exact riemannHypothesis_iff_polarGroundEnergy_nonneg.mpr fun a => (h a).le

/-- The only possible failure pattern is one zero aperture, positive below and negative above.
This theorem does not decide which branch holds for the arithmetic source. -/
theorem riemannHypothesis_or_unique_polarGroundZero :
    RiemannHypothesis ∨ ∃ astar : SuzukiPositiveAperture,
      ccmRestrictedWeilPolarGroundEnergy astar = 0 ∧
      (∀ a : SuzukiPositiveAperture, a < astar →
        0 < ccmRestrictedWeilPolarGroundEnergy a) ∧
      (∀ a : SuzukiPositiveAperture, astar < a →
        ccmRestrictedWeilPolarGroundEnergy a < 0) ∧
      (∀ a : SuzukiPositiveAperture,
        ccmRestrictedWeilPolarGroundEnergy a = 0 → a = astar) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  right
  have hn : ¬ ∀ a, 0 ≤ ccmRestrictedWeilPolarGroundEnergy a :=
    fun h => hRH (riemannHypothesis_iff_polarGroundEnergy_nonneg.mpr h)
  push Not at hn
  obtain ⟨b, hb⟩ := hn
  obtain ⟨astar, hz, hpos, _⟩ := exists_polar_degeneracy_threshold hb.le
  refine ⟨astar, hz, hpos, fun a ha => polarGroundEnergy_neg_above_zero hz ha, ?_⟩
  intro a ha
  exact strictAnti_ccmRestrictedWeilPolarGroundEnergy.injective (ha.trans hz.symm)

/-- Every nonzero smooth strict-interior test lies strictly above the constrained ground.
Thus smooth-core density never supplies a strict-interior ground minimizer, at any energy. -/
theorem polarSmoothSource_strict_ground_floor (a : SuzukiPositiveAperture)
    (f : CCMComplexSmoothInteriorSource a) (hf : IsPolarConstrained a f.toCCMFormVector)
    (hne : ccmArchimedeanFormToAperture a f.toCCMFormVector ≠ 0) :
    ccmRestrictedWeilPolarGroundEnergy a *
      ‖ccmArchimedeanFormToAperture a f.toCCMFormVector‖ ^ (2 : ℕ) <
        ccmRestrictedWeilSourceQuadratic a f.toCCMFormVector := by
  obtain ⟨b, hba, hs⟩ := exists_strict_smaller_aperture_of_compact_tsupport a f
  let fb := f.restrictAperture b hs
  have hval : f.toCCMFormVector.1 = fb.toCCMFormVector.1 :=
    (f.restrictAperture_toCCMFormVector_val b hs).symm
  have hfb : IsPolarConstrained b fb.toCCMFormVector :=
    (isPolarConstrained_iff_of_val_eq hba.le hval).mp hf
  have hnorm := norm_ccmArchimedeanFormToAperture_eq_of_val_eq hval
  have hbmass : 0 < ‖ccmArchimedeanFormToAperture b fb.toCCMFormVector‖ ^ (2 : ℕ) := by
    rw [← hnorm]
    exact pow_pos (norm_pos_iff.mpr hne) 2
  rw [ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hba.le hval, hnorm]
  exact (mul_lt_mul_of_pos_right (strictAnti_ccmRestrictedWeilPolarGroundEnergy hba)
    hbmass).trans_le (ccmRestrictedWeilPolarGroundEnergy_mul_le b _ hfb)

end RHTower
