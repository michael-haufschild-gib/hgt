import GaloisForLFunctions.HTGeometry.ImageProjectionTrace
import GaloisForLFunctions.HTGeometry.CentralCasimirComplementHallExpansion

/-!
# Completing a Hermitian family by a scaled kernel projector

Adjoining a real multiple of the projector onto a Hermitian family's simultaneous kernel leaves
the quadratic Casimir central and makes the simultaneous kernel trivial, so the completed family
is exactly bi-tight after normalization by the inverse square root of its Casimir.  Choosing the
multiple to be the square root of the family's spectral gap makes the completed Casimir dominate
that gap on the whole space, and therefore makes the normalization a uniform contraction by the
reciprocal of the gap.

This is the transfer step that turns a Casimir gap off the simultaneous kernel into a quantitative
statement about the normalized family, with no loss in the constant.
-/

open scoped BigOperators Matrix MatrixOrder

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The coordinate inner product is additive in its second slot. -/
theorem cinner_add_right (u v w : X → ℂ) : cinner u (v + w) = cinner u v + cinner u w := by
  simp only [cinner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.add_apply, mul_add]

/-- The coordinate inner product is homogeneous in its second slot. -/
theorem cinner_smul_right (c : ℂ) (u v : X → ℂ) : cinner u (c • v) = c * cinner u v := by
  simp only [cinner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply]
  ring

/-- The form of a Hermitian idempotent is the square norm of the captured part. -/
theorem cinner_hermitian_idem {P : Matrix X X ℂ} (hP : Pᴴ = P) (hPP : P * P = P) (v : X → ℂ) :
    cinner v (P *ᵥ v) = ((cnormSq (P *ᵥ v) : ℝ) : ℂ) := by
  have hPv : P *ᵥ (P *ᵥ v) = P *ᵥ v := by rw [Matrix.mulVec_mulVec, hPP]
  have h := cinner_mulVec P v (P *ᵥ v)
  rw [hPv, hP] at h
  rw [h, cinner_self]

variable {J : Type*} [Fintype J]

/-- The family completed by a scaled projector onto its simultaneous kernel. -/
def scaledCompletedFamily (A : J → Matrix X X ℂ) (t : ℝ) : Option J → Matrix X X ℂ :=
  fun j => j.elim (((t : ℂ)) • hermitianMatrixFamilyCommonKernelProjection A) A

/-- The scaled completion is a Hermitian family. -/
theorem scaledCompletedFamily_conjTranspose (A : J → Matrix X X ℂ)
    (hsymm : ∀ j, (A j)ᴴ = A j) (t : ℝ) (j : Option J) :
    (scaledCompletedFamily A t j)ᴴ = scaledCompletedFamily A t j := by
  cases j with
  | none =>
      show (((t : ℂ)) • hermitianMatrixFamilyCommonKernelProjection A)ᴴ
        = ((t : ℂ)) • hermitianMatrixFamilyCommonKernelProjection A
      have hherm := hermitianMatrixFamilyCommonKernelProjection_conjTranspose A
      ext i k
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul]
      rw [star_mul', Complex.star_def, Complex.conj_ofReal]
      congr 1
      have hh := congrFun (congrFun hherm i) k
      rw [Matrix.conjTranspose_apply] at hh
      exact hh
  | some j => exact hsymm j

/-- The Casimir of the scaled completion adds the squared multiple of the kernel projector. -/
theorem scaledCompletedFamily_casimir (A : J → Matrix X X ℂ) (t : ℝ) :
    (∑ k : Option J, scaledCompletedFamily A t k * scaledCompletedFamily A t k) =
      ((t ^ 2 : ℝ) : ℂ) • hermitianMatrixFamilyCommonKernelProjection A + ∑ k : J, A k * A k := by
  rw [Fintype.sum_option]
  congr 1
  show (((t : ℂ)) • hermitianMatrixFamilyCommonKernelProjection A) *
      (((t : ℂ)) • hermitianMatrixFamilyCommonKernelProjection A) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hermitianMatrixFamilyCommonKernelProjection_mul_self]
  congr 1
  push_cast
  ring

/-- Scaling a matrix scales its action. -/
theorem smul_mulVec (c : ℂ) (M : Matrix X X ℂ) (v : X → ℂ) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- The Casimir of the scaled completion is central. -/
theorem scaledCompletedFamily_central (A : J → Matrix X X ℂ)
    (hsymm : ∀ j, (A j)ᴴ = A j)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k)) (t : ℝ) (j : Option J) :
    (∑ k : Option J, scaledCompletedFamily A t k * scaledCompletedFamily A t k) *
        scaledCompletedFamily A t j =
      scaledCompletedFamily A t j *
        ∑ k : Option J, scaledCompletedFamily A t k * scaledCompletedFamily A t k := by
  classical
  set P : Matrix X X ℂ := hermitianMatrixFamilyCommonKernelProjection A with hP
  have hPP : P * P = P := hermitianMatrixFamilyCommonKernelProjection_mul_self A
  have hAP : ∀ k, A k * P = 0 := hermitianMatrixFamily_mul_commonKernelProjection_eq_zero A
  have hPA : ∀ k, P * A k = 0 := hermitianMatrixFamily_commonKernelProjection_mul_eq_zero A hsymm
  have hKP : (∑ k : J, A k * A k) * P = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.mul_assoc, hAP k, Matrix.mul_zero]
  have hPK : P * (∑ k : J, A k * A k) = 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Matrix.mul_assoc, hPA k, Matrix.zero_mul]
  cases j with
  | none =>
      show (∑ k : Option J, scaledCompletedFamily A t k * scaledCompletedFamily A t k) *
          (((t : ℂ)) • P) =
        (((t : ℂ)) • P) * ∑ k : Option J, scaledCompletedFamily A t k * scaledCompletedFamily A t k
      rw [scaledCompletedFamily_casimir, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        hPP, hKP, hPK]
      simp only [smul_zero, add_zero, smul_smul]
      congr 1
      push_cast
      ring
  | some j =>
      show (∑ k : Option J, scaledCompletedFamily A t k * scaledCompletedFamily A t k) * A j =
        A j * ∑ k : Option J, scaledCompletedFamily A t k * scaledCompletedFamily A t k
      rw [scaledCompletedFamily_casimir, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
        Matrix.mul_smul, hPA j, hAP j]
      simp only [smul_zero, zero_add]
      exact hcentral j

/-- A nonzero multiple makes the simultaneous kernel of the completion trivial. -/
theorem scaledCompletedFamily_commonKernel_eq_bot (A : J → Matrix X X ℂ) {t : ℝ} (ht : t ≠ 0) :
    ∀ x : EuclideanSpace ℂ X,
      (∀ j, (scaledCompletedFamily A t j).toEuclideanLin x = 0) → x = 0 := by
  intro x hx
  have hxS : x ∈ hermitianMatrixFamilyCommonKernel A :=
    (Submodule.mem_iInf _).2 fun j => hx (some j)
  have hnone := hx none
  have hrew : scaledCompletedFamily A t none
      = ((t : ℂ)) • hermitianMatrixFamilyCommonKernelProjection A := rfl
  rw [hrew, map_smul, LinearMap.smul_apply] at hnone
  have htC : ((t : ℂ)) ≠ 0 := by
    simpa using ht
  have hPx : (hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin x = 0 := by
    rcases smul_eq_zero.mp hnone with h | h
    · exact absurd h htC
    · exact h
  rw [hermitianMatrixFamilyCommonKernelProjection_apply,
    Submodule.starProjection_eq_self_iff.mpr hxS] at hPx
  exact hPx

/-- The Casimir of the scaled completion is nonnegative and invertible. -/
theorem scaledCompletedFamily_casimir_nonneg_isUnit (A : J → Matrix X X ℂ)
    (hsymm : ∀ j, (A j)ᴴ = A j) {t : ℝ} (ht : t ≠ 0) :
    0 ≤ (∑ k : Option J, scaledCompletedFamily A t k * scaledCompletedFamily A t k) ∧
      IsUnit (∑ k : Option J, scaledCompletedFamily A t k * scaledCompletedFamily A t k) :=
  hermitianQuadraticCasimir_nonneg_and_isUnit_of_commonKernel _
    (scaledCompletedFamily_conjTranspose A hsymm t)
    (scaledCompletedFamily_commonKernel_eq_bot A ht)

/-- **Exact bi-tightness of the scaled completion.** -/
theorem scaledCompletedFamily_biTight (A : J → Matrix X X ℂ)
    (hsymm : ∀ j, (A j)ᴴ = A j)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k)) {t : ℝ} (ht : t ≠ 0) :
    (∑ j : Option J,
        (centralCasimirInvSqrtScaleRCLike (scaledCompletedFamily A t) *
            scaledCompletedFamily A t j)ᴴ *
          (centralCasimirInvSqrtScaleRCLike (scaledCompletedFamily A t) *
            scaledCompletedFamily A t j) = 1) ∧
    (∑ j : Option J,
        (centralCasimirInvSqrtScaleRCLike (scaledCompletedFamily A t) *
            scaledCompletedFamily A t j) *
          (centralCasimirInvSqrtScaleRCLike (scaledCompletedFamily A t) *
            scaledCompletedFamily A t j)ᴴ = 1) := by
  classical
  set B := scaledCompletedFamily A t with hB
  have hBsymm := scaledCompletedFamily_conjTranspose A hsymm t
  have hBcentral := scaledCompletedFamily_central A hsymm hcentral t
  obtain ⟨hnonneg, hunit⟩ := scaledCompletedFamily_casimir_nonneg_isUnit A hsymm ht
  have hfirst := centralCasimirRCLike_scaled_conjTranspose_mul_sum B hBsymm hnonneg hunit hBcentral
  refine ⟨hfirst, ?_⟩
  have hscaledsymm : ∀ j,
      (centralCasimirInvSqrtScaleRCLike B * B j)ᴴ =
        centralCasimirInvSqrtScaleRCLike B * B j := by
    intro j
    rw [Matrix.conjTranspose_mul, hBsymm j,
      centralCasimirInvSqrtScaleRCLike_conjTranspose,
      centralCasimirInvSqrtScaleRCLike_commutes B hnonneg hunit hBcentral]
  calc (∑ j : Option J, (centralCasimirInvSqrtScaleRCLike B * B j) *
        (centralCasimirInvSqrtScaleRCLike B * B j)ᴴ)
      = ∑ j : Option J, (centralCasimirInvSqrtScaleRCLike B * B j)ᴴ *
          (centralCasimirInvSqrtScaleRCLike B * B j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hscaledsymm j]
    _ = 1 := hfirst

/-- **The scaled completion inherits the gap on the whole space.** -/
theorem scaledCompletedFamily_form_ge (A : J → Matrix X X ℂ) (hsymm : ∀ j, (A j)ᴴ = A j)
    {g t : ℝ} (htg : t ^ 2 = g)
    (hgapform : ∀ z : X → ℂ,
      hermitianMatrixFamilyCommonKernelProjection A *ᵥ z = 0 →
        g * cnormSq z ≤ (cinner z ((∑ j, A j * A j) *ᵥ z)).re)
    (v : X → ℂ) :
    g * cnormSq v ≤ (cinner v ((∑ k : Option J,
      scaledCompletedFamily A t k * scaledCompletedFamily A t k) *ᵥ v)).re := by
  classical
  set P : Matrix X X ℂ := hermitianMatrixFamilyCommonKernelProjection A with hP
  have hPherm : Pᴴ = P := hermitianMatrixFamilyCommonKernelProjection_conjTranspose A
  have hPP : P * P = P := hermitianMatrixFamilyCommonKernelProjection_mul_self A
  have hAP : ∀ k, A k * P = 0 := hermitianMatrixFamily_mul_commonKernelProjection_eq_zero A
  set z : X → ℂ := v - P *ᵥ v with hzdef
  have hPz : P *ᵥ z = 0 := by
    rw [hzdef, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPP, sub_self]
  have hAz : ∀ k, A k *ᵥ z = A k *ᵥ v := by
    intro k
    rw [hzdef, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hAP k]
    simp
  have hsplit : cnormSq v = cnormSq (P *ᵥ v) + cnormSq z :=
    cnormSq_split_of_hermitian_idem hPherm hPP v
  have hgz := hgapform z hPz
  rw [cinner_casimir_re A hsymm z,
    Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => congrArg cnormSq (hAz k)] at hgz
  rw [scaledCompletedFamily_casimir, htg, Matrix.add_mulVec, smul_mulVec, cinner_add_right,
    cinner_smul_right, cinner_hermitian_idem hPherm hPP, Complex.add_re,
    cinner_casimir_re A hsymm]
  have hre1 : (((g : ℝ) : ℂ) * ((cnormSq (P *ᵥ v) : ℝ) : ℂ)).re = g * cnormSq (P *ᵥ v) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre1, hsplit, mul_add]
  linarith [hgz]

/-- **The normalization contracts by the gap.**  The inverse square root of the completed Casimir
shrinks every vector's square norm by the reciprocal of the gap. -/
theorem cnormSq_invSqrtScale_mulVec_le (A : J → Matrix X X ℂ) (hsymm : ∀ j, (A j)ᴴ = A j)
    {g t : ℝ} (hg : 0 < g) (ht : t ≠ 0) (htg : t ^ 2 = g)
    (hgapform : ∀ z : X → ℂ,
      hermitianMatrixFamilyCommonKernelProjection A *ᵥ z = 0 →
        g * cnormSq z ≤ (cinner z ((∑ j, A j * A j) *ᵥ z)).re)
    (v : X → ℂ) :
    cnormSq (centralCasimirInvSqrtScaleRCLike (scaledCompletedFamily A t) *ᵥ v)
      ≤ g⁻¹ * cnormSq v := by
  classical
  set B := scaledCompletedFamily A t with hB
  set Kc : Matrix X X ℂ := ∑ k : Option J, B k * B k with hKc
  obtain ⟨hnonneg, hunit⟩ := scaledCompletedFamily_casimir_nonneg_isUnit A hsymm ht
  set S : Matrix X X ℂ := CFC.sqrt Kc with hS
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff Kc hnonneg).mpr hunit
  letI : Invertible S := hSunit.nonempty_invertible.some
  have hSR : S * S⁻¹ = 1 := Matrix.mul_inv_of_invertible _
  have hS2 : S * S = Kc := CFC.sqrt_mul_sqrt_self _ hnonneg
  have hSherm : Sᴴ = S := by
    have hstar := (CFC.sqrt_nonneg Kc).isSelfAdjoint.star_eq
    rw [Matrix.star_eq_conjTranspose] at hstar
    exact hstar
  have hRdef : centralCasimirInvSqrtScaleRCLike B = S⁻¹ := rfl
  set w : X → ℂ := centralCasimirInvSqrtScaleRCLike B *ᵥ v with hw
  have hSw : S *ᵥ w = v := by
    rw [hw, hRdef, Matrix.mulVec_mulVec, hSR, Matrix.one_mulVec]
  have hform := scaledCompletedFamily_form_ge A hsymm htg hgapform w
  have hchain : (cinner w (Kc *ᵥ w)).re = cnormSq v := by
    rw [← hS2, ← Matrix.mulVec_mulVec, cinner_mulVec, hSherm, hSw, cinner_self_re]
  rw [hchain] at hform
  have hscaled := mul_le_mul_of_nonneg_left hform (le_of_lt (inv_pos.mpr hg))
  rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hg), one_mul] at hscaled

end

end GaloisForLFunctions.HTGeometry
