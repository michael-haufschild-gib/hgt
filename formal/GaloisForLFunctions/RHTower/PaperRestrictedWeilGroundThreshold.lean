import GaloisForLFunctions.RHTower.PaperRestrictedWeilInertia
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion

/-! # Exact ground threshold and the zero-repair-rank RH receiver

The full source at energy `E` needs no repair exactly when `E` is at most the
actual ground energy. At energy zero, vanishing of every aperture's exact
minimum repair rank is equivalent to RH through the proven native criterion.
-/

noncomputable section

namespace RHTower.PaperRestrictedWeil

theorem operator_positive_iff_source (a : SuzukiPositiveAperture) (E : ℝ) :
    (operator a E).IsPositive ↔ ∀ u : Space a,
      E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a u := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · intro h u
    have hu := h.2 u
    change 0 ≤ (inner ℂ (operator a E u) u).re at hu
    rw [operator_quadratic] at hu
    linarith
  · intro h
    refine ⟨operator_selfAdjoint a E, fun u => ?_⟩
    change 0 ≤ (inner ℂ (operator a E u) u).re
    rw [operator_quadratic]
    exact sub_nonneg.2 (h u)

theorem groundLift_source (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilCanonicalGroundFormLift a) =
      ccmRestrictedWeilGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a (ccmRestrictedWeilCanonicalGroundFormLift a)‖ ^ 2 := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source,
    ccmRestrictedWeilCanonicalGroundFormLift_mixed,
    ccmRestrictedWeilCanonicalGroundFormLift_embedding,
    inner_smul_left (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)
      (ccmRestrictedWeilGroundEnergy a : ℂ),
    Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hr : (inner ℂ
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)).re =
      ‖(ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)).symm
  rw [hr]

theorem groundLift_norm_pos (a : SuzukiPositiveAperture) :
    0 < ‖ccmArchimedeanFormToAperture a (ccmRestrictedWeilCanonicalGroundFormLift a)‖ ^ 2 := by
  rw [ccmRestrictedWeilCanonicalGroundFormLift_embedding]
  exact sq_pos_of_pos (norm_pos_iff.2 (ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a))

theorem operator_positive_iff_ground (a : SuzukiPositiveAperture) (E : ℝ) :
    (operator a E).IsPositive ↔ E ≤ ccmRestrictedWeilGroundEnergy a := by
  rw [operator_positive_iff_source]
  constructor
  · intro h
    have hg := h (ccmRestrictedWeilCanonicalGroundFormLift a)
    rw [groundLift_source] at hg
    exact (mul_le_mul_iff_left₀ (groundLift_norm_pos a)).1 hg
  · intro h u
    exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans
      (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u)

theorem negativeRank_eq_zero_iff_ground (a : SuzukiPositiveAperture) (E : ℝ) :
    negativeRank a E = 0 ↔ E ≤ ccmRestrictedWeilGroundEnergy a := by
  rw [negativeRank_eq_zero_iff, operator_positive_iff_ground]

theorem negativeRank_pos_iff_ground (a : SuzukiPositiveAperture) (E : ℝ) :
    0 < negativeRank a E ↔ ccmRestrictedWeilGroundEnergy a < E := by
  rw [← Nat.ne_zero_iff_zero_lt, ne_eq, negativeRank_eq_zero_iff_ground, not_le]

theorem all_zeroRank_iff_riemannHypothesis :
    (∀ a : SuzukiPositiveAperture, negativeRank a 0 = 0) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_iff_parityPole_nonneg.2
    intro a
    have ha := (operator_positive_iff_source a 0).1 ((negativeRank_eq_zero_iff a 0).1 (h a))
    exact ⟨by simpa only [zero_mul] using ha (ccmPolarParityFormVector a 1),
      by simpa only [zero_mul] using ha (ccmPolarParityFormVector a (-1))⟩
  · intro h a
    apply (negativeRank_eq_zero_iff a 0).2
    apply (operator_positive_iff_source a 0).2
    intro u
    simpa only [zero_mul] using ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis h a u

theorem all_rank_zero_repair_iff_riemannHypothesis :
    (∀ a : SuzukiPositiveAperture, ∃ F : Space a →L[ℂ] Space a,
      HasRankLE F 0 ∧ (operator a 0 + F).IsPositive) ↔ RiemannHypothesis := by
  simp only [positive_repair_rank_iff, Nat.le_zero]
  exact all_zeroRank_iff_riemannHypothesis

end RHTower.PaperRestrictedWeil
