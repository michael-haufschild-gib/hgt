import GaloisForLFunctions.RHTower.CCMRestrictedWeilExactFiniteSchur
import GaloisForLFunctions.RHTower.SuzukiFirstContactBoundaryRoughness

/-!
# Literal completed-source kernel at a CCM first contact

At an aperture whose exact restricted-Weil ground energy is zero, the literal completed source
form is positive semidefinite.  Therefore a vector of zero source energy is not merely isotropic:
it lies in the kernel of its exact bounded self-adjoint representing operator.  Applied to the
first-contact alternative, failure of RH would produce a nonzero physical completion-boundary
kernel vector.  This is a source-level necessary condition, not a positivity proof.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform

noncomputable section

namespace RHTower

/-- At a zero ground-energy aperture, a zero-energy source vector is annihilated by the exact
bounded operator representing the literal completed restricted-Weil form. -/
theorem ccmRestrictedWeilZeroFormOperator_apply_eq_zero_of_groundEnergy_eq_zero
    (a : SuzukiPositiveAperture)
    (hground : ccmRestrictedWeilGroundEnergy a = 0)
    (q : CCMArchimedeanFormDomain a)
    (hq : ccmRestrictedWeilSourceQuadratic a q = 0) :
    ccmRestrictedWeilZeroFormOperator a q = 0 := by
  let T := ccmRestrictedWeilZeroFormOperator a
  have hsym (x y : CCMArchimedeanFormDomain a) :
      inner ℂ (T x) y = inner ℂ x (T y) := by
    calc
      inner ℂ (T x) y = inner ℂ x (T.adjoint y) :=
        (T.adjoint_inner_right x y).symm
      _ = inner ℂ x (T y) := by
        rw [show T.adjoint = T by
          exact ccmRestrictedWeilZeroFormOperator_adjoint a]
  have hnon (u : CCMArchimedeanFormDomain a) :
      0 ≤ (inner ℂ (T u) u).re := by
    rw [show T = ccmRestrictedWeilZeroFormOperator a by rfl,
      inner_ccmRestrictedWeilZeroFormOperator,
      ccmRestrictedWeilForm_self_re_eq_source]
    have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u
    rw [hground, zero_mul] at hfloor
    exact hfloor
  have hqq : (inner ℂ (T q) q).re = 0 := by
    rw [show T = ccmRestrictedWeilZeroFormOperator a by rfl,
      inner_ccmRestrictedWeilZeroFormOperator,
      ccmRestrictedWeilForm_self_re_eq_source, hq]
  by_contra hTq
  let v : CCMArchimedeanFormDomain a := T q
  let A : ℝ := ‖v‖ ^ 2
  let B : ℝ := (inner ℂ (T v) v).re
  let r : ℝ := A / (B + 1)
  have hv : v ≠ 0 := hTq
  have hApos : 0 < A := by
    dsimp only [A]
    exact pow_pos (norm_pos_iff.mpr hv) 2
  have hBnonneg : 0 ≤ B := hnon v
  have hdenpos : 0 < B + 1 := by linarith
  have hTqv : inner ℂ (T q) v = inner ℂ v v := by rfl
  have hTvq : inner ℂ (T v) q = inner ℂ v v := by
    rw [hsym]
  have hvv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
    rw [h]
    simp [pow_two]
  have hstar : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := by
    change star (r : ℂ) = (r : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
  have hquad := hnon (q - (r : ℂ) • v)
  have hquadEq :
      (inner ℂ (T (q - (r : ℂ) • v)) (q - (r : ℂ) • v)).re =
        -2 * r * A + r ^ 2 * B := by
    rw [map_sub, map_smul, inner_sub_left, inner_sub_right,
      inner_sub_right]
    rw [Complex.sub_re, Complex.sub_re, Complex.sub_re,
      inner_smul_right (T q) v (r : ℂ),
      inner_smul_left (T v) q (r : ℂ),
      inner_smul_left (T v) ((r : ℂ) • v) (r : ℂ),
      inner_smul_right (T v) v (r : ℂ)]
    rw [hqq, hTqv, hTvq, hstar]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.mul_im, sub_zero, zero_mul, add_zero]
    rw [hvv]
    dsimp only [A, B]
    ring
  rw [hquadEq] at hquad
  have hneg : -2 * r * A + r ^ 2 * B < 0 := by
    dsimp only [r]
    field_simp
    nlinarith [sq_pos_of_pos hdenpos, hApos]
  exact (not_lt_of_ge hquad) hneg

/-- A failure of RH would first appear as a nonzero physical kernel vector of the exact operator
representing the completed source form, with every smaller aperture strictly positive. -/
def CCMFirstContactPhysicalSourceKernel : Prop :=
  ∃ (a : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain a),
    ccmRestrictedWeilGroundEnergy a = 0 ∧
      (∀ b : SuzukiPositiveAperture, b.1 < a.1 →
        0 < ccmRestrictedWeilGroundEnergy b) ∧
      ccmArchimedeanFormToAperture a q ≠ 0 ∧
      ccmRestrictedWeilZeroFormOperator a q = 0 ∧
      ∀ u : CCMComplexSmoothInteriorSource a, u.toCCMFormVector ≠ q

/-- The existing first-contact boundary-roughness alternative has an exact source-operator
strengthening: its null vector is in the literal completed source kernel. -/
theorem ccmFirstContactBoundaryRoughness_implies_physicalSourceKernel
    (h : CCMFirstContactBoundaryRoughness) :
    CCMFirstContactPhysicalSourceKernel := by
  obtain ⟨a, q, hground, hbefore, hphysical, hnull, hsmooth⟩ := h
  exact ⟨a, q, hground, hbefore, hphysical,
    ccmRestrictedWeilZeroFormOperator_apply_eq_zero_of_groundEnergy_eq_zero
      a hground q hnull,
    hsmooth⟩

/-- Route-O source-level alternative: RH holds, or the exact completed restricted-Weil form
operator has a nonzero physical completion-boundary kernel at its first contact. -/
theorem riemannHypothesis_or_ccmFirstContactPhysicalSourceKernel :
    RiemannHypothesis ∨ CCMFirstContactPhysicalSourceKernel := by
  rcases riemannHypothesis_or_ccmFirstContactBoundaryRoughness with hRH | hrough
  · exact Or.inl hRH
  · exact Or.inr
      (ccmFirstContactBoundaryRoughness_implies_physicalSourceKernel hrough)

end RHTower
