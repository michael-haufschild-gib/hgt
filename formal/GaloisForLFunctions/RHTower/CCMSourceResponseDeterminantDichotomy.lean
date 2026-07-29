import Mathlib
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.RHTower.CCMRadicalQuotientHermitian

/-!
# CCM source-response determinant dichotomy

## Corpus status

`CCMBoundaryChannelCompletion` already proves the arbitrary-radical source/response/neutral
trichotomy, active-channel exclusivity, and removal of the simple-even hypothesis.  Those facts are
prior project knowledge and are not new results of this module.

This module records one stricter residual statement.  For a positive-semidefinite finite CCM metric
with injective diagonal clock, rank-two displacement, and reflection grading, orthogonal Riesz
pinning selects a canonical radical correction whose **full** characteristic polynomial, not merely
the previously known positive quotient polynomial, has only real zeros.  The source/response
dichotomy below only connects that strengthening to existing CCM interfaces.

The exact determinant lemma identifies both branches as resolvent numerators.  The final theorem
connects locally uniform convergence of any such real-rooted completion family to `XiC`, hence RH.
-/

open Complex
open scoped Matrix ComplexOrder

namespace RHTower

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Rank-one clock completion selected by an active boundary vector `alpha`. -/
def ccmSourceCompletion (D : Matrix n n ℂ) (c alpha : n → ℂ) : Matrix n n ℂ :=
  D - Matrix.vecMulVec (D *ᵥ c) (star alpha)

/-- Continuous Euclidean operator represented by a complex matrix. -/
def ccmMatrixCLM (T : Matrix n n ℂ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  T.toEuclideanLin.toContinuousLinearMap

/-- Orthogonal projection of a boundary vector onto the metric radical. -/
def ccmRadicalProjection (T : Matrix n n ℂ) (alpha : n → ℂ) : n → ℂ :=
  ((ccmMatrixCLM T).ker.orthogonalProjection (WithLp.toLp 2 alpha) :
    EuclideanSpace ℂ n).ofLp

/-- Canonically normalized active radical projection. -/
def ccmNormalizedRadicalProjection (T : Matrix n n ℂ) (alpha : n → ℂ) : n → ℂ :=
  let p := ccmRadicalProjection T alpha
  (star p ⬝ᵥ p)⁻¹ • p

/-- Branch-free source-response clock completion.  Scalar inversion sends an inactive zero
projection to zero; the exclusion law later shows exactly one correction term survives. -/
def ccmCanonicalSourceResponseCompletion
    (T D : Matrix n n ℂ) (eta beta : n → ℂ) : Matrix n n ℂ :=
  D - Matrix.vecMulVec
      (D *ᵥ ccmNormalizedRadicalProjection T eta) (star eta) -
    Matrix.vecMulVec
      (D *ᵥ ccmNormalizedRadicalProjection T beta) (star beta)

theorem ccmRadicalProjection_mulVec_eq_zero (T : Matrix n n ℂ) (alpha : n → ℂ) :
    T *ᵥ ccmRadicalProjection T alpha = 0 := by
  have hp := ((ccmMatrixCLM T).ker.orthogonalProjection (WithLp.toLp 2 alpha)).property
  change ccmMatrixCLM T
      ((ccmMatrixCLM T).ker.orthogonalProjection (WithLp.toLp 2 alpha)) = 0 at hp
  change WithLp.toLp 2 (T *ᵥ ccmRadicalProjection T alpha) = 0 at hp
  exact WithLp.toLp_injective 2 hp

theorem ccmRadicalProjection_riesz (T : Matrix n n ℂ) (alpha v : n → ℂ)
    (hv : T *ᵥ v = 0) :
    star (ccmRadicalProjection T alpha) ⬝ᵥ v = star alpha ⬝ᵥ v := by
  let S := ccmMatrixCLM T
  let u : S.ker := ⟨WithLp.toLp 2 v, by
    change WithLp.toLp 2 (T *ᵥ v) = 0
    rw [hv]
    rfl⟩
  have hinner := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left u
    (WithLp.toLp 2 alpha)
  change ccmRadicalProjection T alpha ⬝ᵥ star v = alpha ⬝ᵥ star v at hinner
  have hs := congrArg star hinner
  simpa [dotProduct, mul_comm] using hs

theorem ccmNormalizedRadicalProjection_mulVec_eq_zero
    (T : Matrix n n ℂ) (alpha : n → ℂ) :
    T *ᵥ ccmNormalizedRadicalProjection T alpha = 0 := by
  rw [ccmNormalizedRadicalProjection, Matrix.mulVec_smul,
    ccmRadicalProjection_mulVec_eq_zero]
  simp

theorem ccmNormalizedRadicalProjection_pairing_eq_one
    (T : Matrix n n ℂ) (alpha : n → ℂ)
    (hp : ccmRadicalProjection T alpha ≠ 0) :
    star alpha ⬝ᵥ ccmNormalizedRadicalProjection T alpha = 1 := by
  let p := ccmRadicalProjection T alpha
  let q : ℂ := star p ⬝ᵥ p
  have hqne : q ≠ 0 := ne_of_gt (Matrix.dotProduct_star_self_pos_iff.mpr hp)
  have hqp : star alpha ⬝ᵥ p = q := by
    symm
    exact ccmRadicalProjection_riesz T alpha p
      (ccmRadicalProjection_mulVec_eq_zero T alpha)
  change star alpha ⬝ᵥ (q⁻¹ • p) = 1
  rw [dotProduct_smul, hqp]
  exact inv_mul_cancel₀ hqne

theorem ccmNormalizedRadicalProjection_opposite_pairing_eq_zero
    (T : Matrix n n ℂ) (alpha beta : n → ℂ)
    (hcross : star beta ⬝ᵥ ccmRadicalProjection T alpha = 0) :
    star beta ⬝ᵥ ccmNormalizedRadicalProjection T alpha = 0 := by
  rw [ccmNormalizedRadicalProjection, dotProduct_smul, hcross]
  simp

/-- The canonical normalized projection represents the boundary functional on the radical. -/
theorem ccmNormalizedRadicalProjection_riesz
    (T : Matrix n n ℂ) (alpha : n → ℂ)
    (hp : ccmRadicalProjection T alpha ≠ 0)
    (v : n → ℂ) (hv : T *ᵥ v = 0) :
    star (ccmNormalizedRadicalProjection T alpha) ⬝ᵥ v =
      (star (ccmNormalizedRadicalProjection T alpha) ⬝ᵥ
        ccmNormalizedRadicalProjection T alpha) * (star alpha ⬝ᵥ v) := by
  let p := ccmRadicalProjection T alpha
  let q : ℂ := star p ⬝ᵥ p
  have hqpos : 0 < q := Matrix.dotProduct_star_self_pos_iff.mpr hp
  have hpv : star p ⬝ᵥ v = star alpha ⬝ᵥ v := by
    simpa [p] using ccmRadicalProjection_riesz T alpha v hv
  change star (q⁻¹ • p) ⬝ᵥ v =
    (star (q⁻¹ • p) ⬝ᵥ (q⁻¹ • p)) * (star alpha ⬝ᵥ v)
  simp only [star_smul, smul_dotProduct, dotProduct_smul]
  rw [hpv, show star p ⬝ᵥ p = q by rfl]
  have hqstar : star q = q := by
    apply Complex.ext
    · simp
    · have hqim : q.im = 0 := (Complex.nonneg_iff.mp hqpos.le).2.symm
      simp [hqim]
  have hqinvstar : star (q⁻¹) = q⁻¹ := by simp [hqstar]
  rw [hqinvstar]
  simp only [smul_eq_mul]
  field_simp

/-- An inactive boundary channel contributes no canonical correction. -/
theorem ccmNormalizedRadicalProjection_eq_zero
    (T : Matrix n n ℂ) (alpha : n → ℂ)
    (hp : ccmRadicalProjection T alpha = 0) :
    ccmNormalizedRadicalProjection T alpha = 0 := by
  simp [ccmNormalizedRadicalProjection, hp]

/-- If the response channel is inactive, the branch-free completion is the source completion. -/
theorem ccmCanonicalSourceResponseCompletion_eq_source
    (T D : Matrix n n ℂ) (eta beta : n → ℂ)
    (hbeta : ccmRadicalProjection T beta = 0) :
    ccmCanonicalSourceResponseCompletion T D eta beta =
      ccmSourceCompletion D (ccmNormalizedRadicalProjection T eta) eta := by
  have hc := ccmNormalizedRadicalProjection_eq_zero T beta hbeta
  simp [ccmCanonicalSourceResponseCompletion, ccmSourceCompletion, hc]

/-- If the source channel is inactive, the branch-free completion is the response completion. -/
theorem ccmCanonicalSourceResponseCompletion_eq_response
    (T D : Matrix n n ℂ) (eta beta : n → ℂ)
    (heta : ccmRadicalProjection T eta = 0) :
    ccmCanonicalSourceResponseCompletion T D eta beta =
      ccmSourceCompletion D (ccmNormalizedRadicalProjection T beta) beta := by
  have hc := ccmNormalizedRadicalProjection_eq_zero T eta heta
  simp [ccmCanonicalSourceResponseCompletion, ccmSourceCompletion, hc]

theorem ccmPairing_eq_zero_of_radicalProjection_eq_zero
    (T : Matrix n n ℂ) (alpha v : n → ℂ)
    (hp : ccmRadicalProjection T alpha = 0)
    (hv : T *ᵥ v = 0) :
    star alpha ⬝ᵥ v = 0 := by
  have h := ccmRadicalProjection_riesz T alpha v hv
  simpa [hp] using h.symm

/-- A boundary vector orthogonal to the entire metric radical has zero radical projection. -/
theorem ccmRadicalProjection_eq_zero_of_pairing_eq_zero
    (T : Matrix n n ℂ) (alpha : n → ℂ)
    (horth : ∀ v : n → ℂ, T *ᵥ v = 0 → star alpha ⬝ᵥ v = 0) :
    ccmRadicalProjection T alpha = 0 := by
  let p := ccmRadicalProjection T alpha
  have hpT : T *ᵥ p = 0 := ccmRadicalProjection_mulVec_eq_zero T alpha
  have hpp : star p ⬝ᵥ p = 0 := by
    rw [ccmRadicalProjection_riesz T alpha p hpT, horth p hpT]
  by_contra hpne
  exact (ne_of_gt (Matrix.dotProduct_star_self_pos_iff.mpr hpne)) hpp

theorem exists_ccmNormalizedRadicalRieszVector
    (T : Matrix n n ℂ) (alpha : n → ℂ)
    (hp : ccmRadicalProjection T alpha ≠ 0) :
    ∃ c : n → ℂ,
      T *ᵥ c = 0 ∧
      star alpha ⬝ᵥ c = 1 ∧
      ∀ v : n → ℂ, T *ᵥ v = 0 →
        star c ⬝ᵥ v = (star c ⬝ᵥ c) * (star alpha ⬝ᵥ v) := by
  let p := ccmRadicalProjection T alpha
  let q : ℂ := star p ⬝ᵥ p
  have hqpos : 0 < q := Matrix.dotProduct_star_self_pos_iff.mpr hp
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hqp : star alpha ⬝ᵥ p = q := by
    symm
    exact ccmRadicalProjection_riesz T alpha p
      (ccmRadicalProjection_mulVec_eq_zero T alpha)
  let c : n → ℂ := q⁻¹ • p
  refine ⟨c, ?_, ?_, ?_⟩
  · change T *ᵥ (q⁻¹ • p) = 0
    rw [Matrix.mulVec_smul, ccmRadicalProjection_mulVec_eq_zero]
    simp
  · change star alpha ⬝ᵥ (q⁻¹ • p) = 1
    rw [dotProduct_smul, hqp]
    exact inv_mul_cancel₀ hqne
  · intro v hv
    have hpv := ccmRadicalProjection_riesz T alpha v hv
    have hpv' : star p ⬝ᵥ v = star alpha ⬝ᵥ v := by simpa [p] using hpv
    change star (q⁻¹ • p) ⬝ᵥ v =
      (star (q⁻¹ • p) ⬝ᵥ (q⁻¹ • p)) * (star alpha ⬝ᵥ v)
    simp only [star_smul, smul_dotProduct, dotProduct_smul]
    rw [hpv', show star p ⬝ᵥ p = q by rfl]
    have hqstar : star q = q := by
      apply Complex.ext
      · simp
      · have hqim : q.im = 0 := (Complex.nonneg_iff.mp hqpos.le).2.symm
        simp [hqim]
    have hqinvstar : star (q⁻¹) = q⁻¹ := by simp [hqstar]
    rw [hqinvstar]
    simp only [smul_eq_mul]
    field_simp


omit [DecidableEq n] in
theorem ccmSourceCompletion_mulVec_c (D : Matrix n n ℂ) (c alpha : n → ℂ)
    (hnorm : star alpha ⬝ᵥ c = 1) :
    ccmSourceCompletion D c alpha *ᵥ c = 0 := by
  rw [ccmSourceCompletion, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec]
  simp [hnorm]

theorem ccmSourceCompletion_shift_det
    (D : Matrix n n ℂ) (c alpha : n → ℂ) (z : ℂ)
    (hM : IsUnit (D - z • (1 : Matrix n n ℂ)).det) :
    (ccmSourceCompletion D c alpha - z • (1 : Matrix n n ℂ)).det =
      (D - z • (1 : Matrix n n ℂ)).det *
        (1 - star alpha ⬝ᵥ
          ((D - z • (1 : Matrix n n ℂ))⁻¹ *ᵥ (D *ᵥ c))) := by
  let M : Matrix n n ℂ := D - z • (1 : Matrix n n ℂ)
  have hmatrix : ccmSourceCompletion D c alpha - z • (1 : Matrix n n ℂ) =
      M + Matrix.vecMulVec (-(D *ᵥ c)) (star alpha) := by
    ext i j
    simp [ccmSourceCompletion, M, Matrix.vecMulVec_apply]
    ring
  have hscalar :
      (1 + Matrix.replicateRow Unit (star alpha) * M⁻¹ *
        Matrix.replicateCol Unit (-(D *ᵥ c))).det =
      1 - star alpha ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ c)) := by
    rw [← Matrix.replicateRow_vecMul M⁻¹ (star alpha), Matrix.det_unique]
    simp only [Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.replicateRow_mul_replicateCol_apply]
    rw [← Matrix.dotProduct_mulVec]
    rw [Matrix.mulVec_neg, dotProduct_neg]
    ring
  calc
    (ccmSourceCompletion D c alpha - z • (1 : Matrix n n ℂ)).det =
        (M + Matrix.replicateCol Unit (-(D *ᵥ c)) *
          Matrix.replicateRow Unit (star alpha)).det := by
            rw [hmatrix, ← Matrix.vecMulVec_eq Unit]
    _ = M.det *
        (1 + Matrix.replicateRow Unit (star alpha) * M⁻¹ *
          Matrix.replicateCol Unit (-(D *ᵥ c))).det :=
      Matrix.det_add_replicateCol_mul_replicateRow (by simpa [M] using hM) _ _
    _ = M.det * (1 - star alpha ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ c))) := by rw [hscalar]
    _ = (D - z • (1 : Matrix n n ℂ)).det *
        (1 - star alpha ⬝ᵥ
          ((D - z • (1 : Matrix n n ℂ))⁻¹ *ᵥ (D *ᵥ c))) := by rfl

theorem ccmSourceCompletion_shift_det_eq_neg_mul_resolvent
    (D : Matrix n n ℂ) (c alpha : n → ℂ) (z : ℂ)
    (hnorm : star alpha ⬝ᵥ c = 1)
    (hM : IsUnit (D - z • (1 : Matrix n n ℂ)).det) :
    (ccmSourceCompletion D c alpha - z • (1 : Matrix n n ℂ)).det =
      -z * (D - z • (1 : Matrix n n ℂ)).det *
        (star alpha ⬝ᵥ ((D - z • (1 : Matrix n n ℂ))⁻¹ *ᵥ c)) := by
  let M : Matrix n n ℂ := D - z • (1 : Matrix n n ℂ)
  have hDc : D *ᵥ c = M *ᵥ c + z • c := by
    simp [M, Matrix.sub_mulVec, Matrix.smul_mulVec]
  have hMinvMc : M⁻¹ *ᵥ (M *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (by simpa [M] using hM),
      Matrix.one_mulVec]
  have hinvDc : M⁻¹ *ᵥ (D *ᵥ c) = c + z • (M⁻¹ *ᵥ c) := by
    rw [hDc, Matrix.mulVec_add, Matrix.mulVec_smul, hMinvMc]
  have hscalar :
      1 - star alpha ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ c)) =
        -z * (star alpha ⬝ᵥ (M⁻¹ *ᵥ c)) := by
    rw [hinvDc, dotProduct_add, dotProduct_smul, hnorm]
    ring
  rw [ccmSourceCompletion_shift_det D c alpha z hM]
  change (D - z • (1 : Matrix n n ℂ)).det *
      (1 - star alpha ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ c))) = _
  rw [hscalar]
  ring

omit [DecidableEq n] in
theorem ccmActiveSource_boundary
    (T D : Matrix n n ℂ) (alpha beta c : n → ℂ)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta (star alpha) - Matrix.vecMulVec alpha (star beta))
    (hTc : T *ᵥ c = 0)
    (halpha : star alpha ⬝ᵥ c = 1)
    (hbeta : star beta ⬝ᵥ c = 0) :
    T *ᵥ (D *ᵥ c) = -beta := by
  have h := congrArg (fun M : Matrix n n ℂ => M *ᵥ c) hdisp
  change (D * T - T * D) *ᵥ c =
    (Matrix.vecMulVec beta (star alpha) -
      Matrix.vecMulVec alpha (star beta)) *ᵥ c at h
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTc,
    Matrix.mulVec_zero, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec, halpha, hbeta] at h
  simpa using congrArg Neg.neg h

omit [DecidableEq n] in
theorem ccmNeutralSource_clock_invariant
    (T D : Matrix n n ℂ) (alpha beta k : n → ℂ)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta (star alpha) - Matrix.vecMulVec alpha (star beta))
    (hTk : T *ᵥ k = 0)
    (halpha : star alpha ⬝ᵥ k = 0)
    (hbeta : star beta ⬝ᵥ k = 0) :
    T *ᵥ (D *ᵥ k) = 0 := by
  have h := congrArg (fun M : Matrix n n ℂ => M *ᵥ k) hdisp
  change (D * T - T * D) *ᵥ k =
    (Matrix.vecMulVec beta (star alpha) -
      Matrix.vecMulVec alpha (star beta)) *ᵥ k at h
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTk,
    Matrix.mulVec_zero, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec, halpha, hbeta] at h
  simpa using congrArg Neg.neg h

theorem ccmNeutralSource_radical_eq_zero
    {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (clock beta : Fin N → ℂ)
    (hclock : Function.Injective clock)
    (hdisp : Matrix.diagonal clock * T - T * Matrix.diagonal clock =
      Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
        Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta))
    (heta : ∀ k : Fin N → ℂ, T *ᵥ k = 0 →
      star (fun _ : Fin N => (1 : ℂ)) ⬝ᵥ k = 0)
    (hbeta : ∀ k : Fin N → ℂ, T *ᵥ k = 0 → star beta ⬝ᵥ k = 0) :
    ∀ k : Fin N → ℂ, T *ᵥ k = 0 → k = 0 := by
  intro k hk
  let D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal clock
  have hpow : ∀ m : ℕ, T *ᵥ (D ^ m *ᵥ k) = 0 := by
    intro m
    induction m with
    | zero => simpa [D] using hk
    | succ m ih =>
        rw [pow_succ']
        simpa only [Matrix.mulVec_mulVec] using ccmNeutralSource_clock_invariant T D
          (fun _ : Fin N => (1 : ℂ)) beta (D ^ m *ᵥ k)
          (by simpa [D] using hdisp) ih (heta _ ih) (hbeta _ ih)
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hclock
  intro i
  have hi := heta (D ^ (i : ℕ) *ᵥ k) (hpow i)
  change star (fun _ : Fin N => (1 : ℂ)) ⬝ᵥ
    (Matrix.diagonal clock ^ (i : ℕ) *ᵥ k) = 0 at hi
  rw [Matrix.diagonal_pow] at hi
  simpa [Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm] using hi

omit [DecidableEq n] in
theorem ccmSourceCompletion_metricAdjoint
    (T D : Matrix n n ℂ) (alpha beta c : n → ℂ)
    (hT : T.IsHermitian) (hD : D.IsHermitian)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta (star alpha) - Matrix.vecMulVec alpha (star beta))
    (hboundary : T *ᵥ (D *ᵥ c) = -beta) :
    T * ccmSourceCompletion D c alpha = (ccmSourceCompletion D c alpha)ᴴ * T := by
  have hrow : star (D *ᵥ c) ᵥ* T = star (-beta) := by
    calc
      star (D *ᵥ c) ᵥ* T = star (D *ᵥ c) ᵥ* Tᴴ := by rw [hT.eq]
      _ = star (T *ᵥ (D *ᵥ c)) := (Matrix.star_mulVec T (D *ᵥ c)).symm
      _ = star (-beta) := by rw [hboundary]
  rw [ccmSourceCompletion, Matrix.conjTranspose_sub, Matrix.conjTranspose_vecMulVec,
    hD.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, hboundary, hrow]
  rw [show star (star alpha) = alpha by simp, show star (-beta) = -star beta by simp]
  have hTD : T * D = D * T -
      (Matrix.vecMulVec beta (star alpha) - Matrix.vecMulVec alpha (star beta)) := by
    calc
      T * D = D * T - (D * T - T * D) := by abel
      _ = D * T -
          (Matrix.vecMulVec beta (star alpha) - Matrix.vecMulVec alpha (star beta)) := by
            rw [hdisp]
  rw [hTD]
  ext i j
  simp [Matrix.vecMulVec_apply]
  ring

omit [DecidableEq n] in
theorem ccmActiveSource_opposite_orthogonal
    (T D : Matrix n n ℂ) (beta c k : n → ℂ)
    (hT : T.IsHermitian)
    (hboundary : T *ᵥ (D *ᵥ c) = -beta)
    (hTk : T *ᵥ k = 0) :
    star beta ⬝ᵥ k = 0 := by
  have hbeta : beta = -(T *ᵥ (D *ᵥ c)) := by
    rw [hboundary]
    simp
  rw [hbeta, star_neg, neg_dotProduct]
  have hsymm : star (T *ᵥ (D *ᵥ c)) ⬝ᵥ k =
      star (D *ᵥ c) ⬝ᵥ (T *ᵥ k) := by
    calc
      star (T *ᵥ (D *ᵥ c)) ⬝ᵥ k =
          (star (D *ᵥ c) ᵥ* Tᴴ) ⬝ᵥ k := by rw [Matrix.star_mulVec]
      _ = (star (D *ᵥ c) ᵥ* T) ⬝ᵥ k := by rw [hT.eq]
      _ = star (D *ᵥ c) ⬝ᵥ (T *ᵥ k) := by rw [Matrix.dotProduct_mulVec]
  rw [hsymm, hTk]
  simp

omit [DecidableEq n] in
theorem ccmHermitian_mulVec_inner
    (G : Matrix n n ℂ) (x y : n → ℂ) (hG : G.IsHermitian) :
    star (G *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (G *ᵥ y) := by
  calc
    star (G *ᵥ x) ⬝ᵥ y = (star x ᵥ* Gᴴ) ⬝ᵥ y := by rw [Matrix.star_mulVec]
    _ = (star x ᵥ* G) ⬝ᵥ y := by rw [hG.eq]
    _ = star x ⬝ᵥ (G *ᵥ y) := by rw [Matrix.dotProduct_mulVec]

theorem ccmRadicalProjection_even_of_reflection
    (T G : Matrix n n ℂ) (eta : n → ℂ)
    (hG : G.IsHermitian) (hTG : T * G = G * T)
    (hetaG : G *ᵥ eta = eta) :
    G *ᵥ ccmRadicalProjection T eta = ccmRadicalProjection T eta := by
  let p := ccmRadicalProjection T eta
  let gp := G *ᵥ p
  have hpT : T *ᵥ p = 0 := ccmRadicalProjection_mulVec_eq_zero T eta
  have hgpT : T *ᵥ gp = 0 := by
    change T *ᵥ (G *ᵥ p) = 0
    calc
      T *ᵥ (G *ᵥ p) = (T * G) *ᵥ p := Matrix.mulVec_mulVec p T G
      _ = (G * T) *ᵥ p := by rw [hTG]
      _ = G *ᵥ (T *ᵥ p) := (Matrix.mulVec_mulVec p G T).symm
      _ = 0 := by rw [hpT, Matrix.mulVec_zero]
  have hgpRiesz : ∀ k : n → ℂ, T *ᵥ k = 0 →
      star gp ⬝ᵥ k = star eta ⬝ᵥ k := by
    intro k hk
    have hGk : T *ᵥ (G *ᵥ k) = 0 := by
      calc
        T *ᵥ (G *ᵥ k) = (T * G) *ᵥ k := Matrix.mulVec_mulVec k T G
        _ = (G * T) *ᵥ k := by rw [hTG]
        _ = G *ᵥ (T *ᵥ k) := (Matrix.mulVec_mulVec k G T).symm
        _ = 0 := by rw [hk, Matrix.mulVec_zero]
    calc
      star gp ⬝ᵥ k = star p ⬝ᵥ (G *ᵥ k) :=
        ccmHermitian_mulVec_inner G p k hG
      _ = star eta ⬝ᵥ (G *ᵥ k) := ccmRadicalProjection_riesz T eta _ hGk
      _ = star (G *ᵥ eta) ⬝ᵥ k := (ccmHermitian_mulVec_inner G eta k hG).symm
      _ = star eta ⬝ᵥ k := by rw [hetaG]
  let d := gp - p
  have hdT : T *ᵥ d = 0 := by
    change T *ᵥ (gp - p) = 0
    rw [Matrix.mulVec_sub, hgpT, hpT, sub_self]
  have hdd : star d ⬝ᵥ d = 0 := by
    change star (gp - p) ⬝ᵥ (gp - p) = 0
    rw [star_sub, sub_dotProduct, hgpRiesz d hdT,
      ccmRadicalProjection_riesz T eta d hdT, sub_self]
  have hd0 : d = 0 := by
    by_contra hdne
    exact (ne_of_gt (Matrix.dotProduct_star_self_pos_iff.mpr hdne)) hdd
  exact sub_eq_zero.mp hd0

theorem ccmRadicalProjection_source_response_cross_zero
    (T G : Matrix n n ℂ) (eta beta : n → ℂ)
    (hG : G.IsHermitian) (hG2 : G * G = 1)
    (hTG : T * G = G * T)
    (hetaG : G *ᵥ eta = eta) (hbetaG : G *ᵥ beta = -beta) :
    star beta ⬝ᵥ ccmRadicalProjection T eta = 0 := by
  let p := ccmRadicalProjection T eta
  have hpG : G *ᵥ p = p := ccmRadicalProjection_even_of_reflection T G eta hG hTG hetaG
  have hinv : star (G *ᵥ beta) ⬝ᵥ (G *ᵥ p) = star beta ⬝ᵥ p := by
    calc
      star (G *ᵥ beta) ⬝ᵥ (G *ᵥ p) =
          star beta ⬝ᵥ (G *ᵥ (G *ᵥ p)) := ccmHermitian_mulVec_inner G beta (G *ᵥ p) hG
      _ = star beta ⬝ᵥ ((G * G) *ᵥ p) := by rw [Matrix.mulVec_mulVec]
      _ = star beta ⬝ᵥ p := by rw [hG2, Matrix.one_mulVec]
  rw [hbetaG, hpG] at hinv
  have hneg : -(star beta ⬝ᵥ p) = star beta ⬝ᵥ p := by simpa using hinv
  have htwo : (2 : ℂ) * (star beta ⬝ᵥ p) = 0 := by
    calc
      (2 : ℂ) * (star beta ⬝ᵥ p) =
          (star beta ⬝ᵥ p) + (star beta ⬝ᵥ p) := by ring
      _ = -(star beta ⬝ᵥ p) + (star beta ⬝ᵥ p) := by rw [hneg]
      _ = 0 := by ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem ccmSourceCompletion_charpoly_zero_im_eq_zero
    (T D : Matrix n n ℂ) (c alpha : n → ℂ)
    (hT : T.PosSemidef) (hD : D.IsHermitian)
    (hnorm : star alpha ⬝ᵥ c = 1)
    (hriesz : ∀ v : n → ℂ, T *ᵥ v = 0 →
      star c ⬝ᵥ v = (star c ⬝ᵥ c) * (star alpha ⬝ᵥ v))
    (hmetric : T * ccmSourceCompletion D c alpha = (ccmSourceCompletion D c alpha)ᴴ * T)
    {z : ℂ} (hz : (ccmSourceCompletion D c alpha).charpoly.eval z = 0) :
    z.im = 0 := by
  have hroot : (ccmSourceCompletion D c alpha).charpoly.IsRoot z := hz
  have hspec : z ∈ spectrum ℂ (ccmSourceCompletion D c alpha) :=
    Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have hspeclin : z ∈ spectrum ℂ (ccmSourceCompletion D c alpha).toLin' := by
    simpa using hspec
  have heig : Module.End.HasEigenvalue (ccmSourceCompletion D c alpha).toLin' z :=
    Module.End.HasEigenvalue.of_mem_spectrum hspeclin
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hAv : ccmSourceCompletion D c alpha *ᵥ v = z • v := by
    simpa using hv.apply_eq_smul
  have hvne : v ≠ 0 := hv.2
  let q : ℂ := star v ⬝ᵥ (T *ᵥ v)
  have hqeq : z * q = star z * q := by
    calc
      z * q = star v ⬝ᵥ (T *ᵥ (z • v)) := by
        rw [Matrix.mulVec_smul, dotProduct_smul]
        rfl
      _ = star v ⬝ᵥ (T *ᵥ (ccmSourceCompletion D c alpha *ᵥ v)) := by rw [hAv]
      _ = star v ⬝ᵥ ((T * ccmSourceCompletion D c alpha) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec]
      _ = star v ⬝ᵥ (((ccmSourceCompletion D c alpha)ᴴ * T) *ᵥ v) := by rw [hmetric]
      _ = star v ⬝ᵥ ((ccmSourceCompletion D c alpha)ᴴ *ᵥ (T *ᵥ v)) := by
        rw [Matrix.mulVec_mulVec]
      _ = star (ccmSourceCompletion D c alpha *ᵥ v) ⬝ᵥ (T *ᵥ v) := by
        rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]
      _ = star (z • v) ⬝ᵥ (T *ᵥ v) := by rw [hAv]
      _ = star z * q := by simp [q]
  by_contra him
  have hzne : z - star z ≠ 0 := by
    intro hzstar
    have hzim := congrArg Complex.im (sub_eq_zero.mp hzstar)
    simp at hzim
    apply him
    linarith
  have hqzero : q = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hzne
    calc
      (z - star z) * q = z * q - star z * q := by ring
      _ = 0 := sub_eq_zero.mpr hqeq
  have hTv : T *ᵥ v = 0 :=
    (hT.dotProduct_mulVec_zero_iff v).mp (by simpa [q] using hqzero)
  let a : ℂ := star alpha ⬝ᵥ v
  let v0 : n → ℂ := v - a • c
  have hac : star alpha ⬝ᵥ c = 1 := hnorm
  have halpha0 : star alpha ⬝ᵥ v0 = 0 := by
    simp [v0, a, dotProduct_sub, dotProduct_smul, hac]
  have hcv0 : star c ⬝ᵥ v0 = 0 := by
    change star c ⬝ᵥ (v - a • c) = 0
    rw [dotProduct_sub, dotProduct_smul, hriesz v hTv]
    ring
  have hv0c : star v0 ⬝ᵥ c = 0 := by
    rw [Matrix.star_dotProduct]
    simp [hcv0]
  have hAc : ccmSourceCompletion D c alpha *ᵥ c = 0 :=
    ccmSourceCompletion_mulVec_c D c alpha hnorm
  have hAv0 : ccmSourceCompletion D c alpha *ᵥ v0 = z • v := by
    change ccmSourceCompletion D c alpha *ᵥ (v - a • c) = z • v
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hAv, hAc]
    simp
  have hDv0 : D *ᵥ v0 = z • v := by
    calc
      D *ᵥ v0 = ccmSourceCompletion D c alpha *ᵥ v0 := by
        rw [ccmSourceCompletion, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, halpha0]
        simp
      _ = z • v := hAv0
  by_cases hv0zero : v0 = 0
  · have hvac : v = a • c := sub_eq_zero.mp hv0zero
    have hzv : z • v = 0 := by simpa [hv0zero] using hDv0.symm
    have hz0 : z = 0 := by
      by_contra hz
      exact hvne (smul_eq_zero.mp hzv |>.resolve_left hz)
    exact him (by simp [hz0])
  · have hrpos : 0 < star v0 ⬝ᵥ v0 := Matrix.dotProduct_star_self_pos_iff.mpr hv0zero
    have hrne : star v0 ⬝ᵥ v0 ≠ 0 := ne_of_gt hrpos
    have hrim : (star v0 ⬝ᵥ v0).im = 0 := (Complex.nonneg_iff.mp hrpos.le).2.symm
    have hvdecomp : v = v0 + a • c := by
      simp [v0]
    have hv0v : star v0 ⬝ᵥ v = star v0 ⬝ᵥ v0 := by
      rw [hvdecomp, dotProduct_add, dotProduct_smul, hv0c]
      simp
    have hquad : star v0 ⬝ᵥ (D *ᵥ v0) = z * (star v0 ⬝ᵥ v0) := by
      rw [hDv0, dotProduct_smul, hv0v]
      rfl
    have hdim : (star v0 ⬝ᵥ (D *ᵥ v0)).im = 0 :=
      hD.im_star_dotProduct_mulVec_self v0
    have himprod : (z * (star v0 ⬝ᵥ v0)).im = 0 := by rw [← hquad]; exact hdim
    rw [Complex.mul_im, hrim, mul_zero, zero_add] at himprod
    have hrre : (star v0 ⬝ᵥ v0).re ≠ 0 := by
      intro hre
      apply hrne
      apply Complex.ext
      · simpa using hre
      · simpa using hrim
    exact him (mul_eq_zero.mp himprod |>.resolve_right hrre)

theorem exists_ccmActiveSourceCompletion_charpoly_zero_im_eq_zero
    (T D : Matrix n n ℂ) (alpha beta : n → ℂ)
    (hT : T.PosSemidef) (hD : D.IsHermitian)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta (star alpha) - Matrix.vecMulVec alpha (star beta))
    (hactive : ccmRadicalProjection T alpha ≠ 0)
    (hopposite : ∀ v : n → ℂ, T *ᵥ v = 0 → star beta ⬝ᵥ v = 0) :
    ∃ c : n → ℂ,
      T *ᵥ c = 0 ∧
      star alpha ⬝ᵥ c = 1 ∧
      T * ccmSourceCompletion D c alpha = (ccmSourceCompletion D c alpha)ᴴ * T ∧
      ∀ z : ℂ, (ccmSourceCompletion D c alpha).charpoly.eval z = 0 → z.im = 0 := by
  obtain ⟨c, hTc, hnorm, hriesz⟩ :=
    exists_ccmNormalizedRadicalRieszVector T alpha hactive
  have hbeta : star beta ⬝ᵥ c = 0 := hopposite c hTc
  have hboundary := ccmActiveSource_boundary T D alpha beta c hdisp hTc hnorm hbeta
  have hmetric := ccmSourceCompletion_metricAdjoint T D alpha beta c
    hT.isHermitian hD hdisp hboundary
  refine ⟨c, hTc, hnorm, hmetric, ?_⟩
  intro z hz
  exact ccmSourceCompletion_charpoly_zero_im_eq_zero T D c alpha hT hD hnorm hriesz hmetric hz

/-- **Source-response exclusion law.**  For an injective diagonal clock with CCM displacement and
a nonzero radical, the constant-source and odd-response projections cannot coexist and cannot both
vanish.  Exactly one boundary channel meets the radical. -/
theorem ccmSourceResponse_radicalProjection_exclusive
    {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (clock beta : Fin N → ℂ)
    (hT : T.PosSemidef)
    (hclock : Function.Injective clock)
    (hdisp : Matrix.diagonal clock * T - T * Matrix.diagonal clock =
      Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
        Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta))
    (hkernel : ∃ k : Fin N → ℂ, T *ᵥ k = 0 ∧ k ≠ 0)
    (hcross : star beta ⬝ᵥ
      ccmRadicalProjection T (fun _ : Fin N => (1 : ℂ)) = 0) :
    (ccmRadicalProjection T (fun _ : Fin N => (1 : ℂ)) ≠ 0 ∧
      ccmRadicalProjection T beta = 0) ∨
    (ccmRadicalProjection T (fun _ : Fin N => (1 : ℂ)) = 0 ∧
      ccmRadicalProjection T beta ≠ 0) := by
  let eta : Fin N → ℂ := fun _ => 1
  by_cases hetaActive : ccmRadicalProjection T eta ≠ 0
  · let c0 := ccmNormalizedRadicalProjection T eta
    have hTc0 : T *ᵥ c0 = 0 := ccmNormalizedRadicalProjection_mulVec_eq_zero T eta
    have hetaC0 : star eta ⬝ᵥ c0 = 1 :=
      ccmNormalizedRadicalProjection_pairing_eq_one T eta hetaActive
    have hbetaC0 : star beta ⬝ᵥ c0 = 0 :=
      ccmNormalizedRadicalProjection_opposite_pairing_eq_zero T eta beta hcross
    have hboundary := ccmActiveSource_boundary T (Matrix.diagonal clock) eta beta c0
      (by simpa [eta] using hdisp) hTc0 hetaC0 hbetaC0
    have hbetaAll : ∀ v : Fin N → ℂ, T *ᵥ v = 0 → star beta ⬝ᵥ v = 0 :=
      fun v hv => ccmActiveSource_opposite_orthogonal T (Matrix.diagonal clock)
        beta c0 v hT.isHermitian hboundary hv
    exact Or.inl ⟨by simpa [eta] using hetaActive,
      ccmRadicalProjection_eq_zero_of_pairing_eq_zero T beta hbetaAll⟩
  · have hetaZero : ccmRadicalProjection T eta = 0 := not_ne_iff.mp hetaActive
    have hetaAll : ∀ v : Fin N → ℂ, T *ᵥ v = 0 → star eta ⬝ᵥ v = 0 :=
      fun v hv => ccmPairing_eq_zero_of_radicalProjection_eq_zero T eta v hetaZero hv
    have hbetaActive : ccmRadicalProjection T beta ≠ 0 := by
      intro hbetaZero
      have hbetaAll : ∀ v : Fin N → ℂ, T *ᵥ v = 0 → star beta ⬝ᵥ v = 0 :=
        fun v hv => ccmPairing_eq_zero_of_radicalProjection_eq_zero T beta v hbetaZero hv
      obtain ⟨k, hk, hkne⟩ := hkernel
      exact hkne (ccmNeutralSource_radical_eq_zero T clock beta hclock
        (by simpa [eta] using hdisp)
        (by simpa [eta] using hetaAll) hbetaAll k hk)
    exact Or.inr ⟨by simpa [eta] using hetaZero, hbetaActive⟩

/-- **Canonical full-spectrum law.**  Under the CCM source-response hypotheses, the branch-free
orthogonal-Riesz completion is metric-adjoint and every zero of its full characteristic polynomial
is real.  Unlike the generic semimetric quotient theorem, this also controls the residual radical
block. -/
theorem ccmCanonicalSourceResponseCompletion_metricAdjoint_and_realRooted
    {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (clock beta : Fin N → ℂ)
    (hT : T.PosSemidef)
    (hD : (Matrix.diagonal clock).IsHermitian)
    (hclock : Function.Injective clock)
    (hdisp : Matrix.diagonal clock * T - T * Matrix.diagonal clock =
      Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
        Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta))
    (hkernel : ∃ k : Fin N → ℂ, T *ᵥ k = 0 ∧ k ≠ 0)
    (hcross : star beta ⬝ᵥ
      ccmRadicalProjection T (fun _ : Fin N => (1 : ℂ)) = 0) :
    let A := ccmCanonicalSourceResponseCompletion T (Matrix.diagonal clock)
      (fun _ : Fin N => (1 : ℂ)) beta
    T * A = Aᴴ * T ∧
      ∀ z : ℂ, A.charpoly.eval z = 0 → z.im = 0 := by
  let eta : Fin N → ℂ := fun _ => 1
  rcases ccmSourceResponse_radicalProjection_exclusive T clock beta hT hclock hdisp
    hkernel hcross with ⟨hetaActive, hbetaZero⟩ | ⟨hetaZero, hbetaActive⟩
  · let c := ccmNormalizedRadicalProjection T eta
    have hTc : T *ᵥ c = 0 := ccmNormalizedRadicalProjection_mulVec_eq_zero T eta
    have hnorm : star eta ⬝ᵥ c = 1 :=
      ccmNormalizedRadicalProjection_pairing_eq_one T eta hetaActive
    have hbetaC : star beta ⬝ᵥ c = 0 :=
      ccmPairing_eq_zero_of_radicalProjection_eq_zero T beta c hbetaZero hTc
    have hboundary := ccmActiveSource_boundary T (Matrix.diagonal clock) eta beta c
      (by simpa [eta] using hdisp) hTc hnorm hbetaC
    have hmetric := ccmSourceCompletion_metricAdjoint T (Matrix.diagonal clock) eta beta c
      hT.isHermitian hD (by simpa [eta] using hdisp) hboundary
    have hriesz : ∀ v : Fin N → ℂ, T *ᵥ v = 0 →
        star c ⬝ᵥ v = (star c ⬝ᵥ c) * (star eta ⬝ᵥ v) :=
      fun v hv => ccmNormalizedRadicalProjection_riesz T eta hetaActive v hv
    have heq := ccmCanonicalSourceResponseCompletion_eq_source T
      (Matrix.diagonal clock) eta beta hbetaZero
    dsimp only
    have heq' : ccmCanonicalSourceResponseCompletion T (Matrix.diagonal clock)
        (fun _ : Fin N => (1 : ℂ)) beta =
        ccmSourceCompletion (Matrix.diagonal clock) c (fun _ : Fin N => (1 : ℂ)) := by
      simpa [eta, c] using heq
    constructor
    · rw [heq']
      simpa [eta, c] using hmetric
    · intro z hz
      rw [heq'] at hz
      have hz' : (ccmSourceCompletion (Matrix.diagonal clock) c eta).charpoly.eval z = 0 := by
        simpa [eta, c] using hz
      exact ccmSourceCompletion_charpoly_zero_im_eq_zero T (Matrix.diagonal clock)
        c eta hT hD hnorm hriesz hmetric hz'
  · let c := ccmNormalizedRadicalProjection T beta
    have hTc : T *ᵥ c = 0 := ccmNormalizedRadicalProjection_mulVec_eq_zero T beta
    have hnorm : star beta ⬝ᵥ c = 1 :=
      ccmNormalizedRadicalProjection_pairing_eq_one T beta hbetaActive
    have hetaC : star eta ⬝ᵥ c = 0 :=
      ccmPairing_eq_zero_of_radicalProjection_eq_zero T eta c hetaZero hTc
    have hdispOdd : Matrix.diagonal clock * T - T * Matrix.diagonal clock =
        Matrix.vecMulVec (-eta) (star beta) - Matrix.vecMulVec beta (star (-eta)) := by
      rw [show Matrix.diagonal clock * T - T * Matrix.diagonal clock =
        Matrix.vecMulVec beta (star eta) - Matrix.vecMulVec eta (star beta) by
          simpa [eta] using hdisp]
      ext i j
      simp [Matrix.vecMulVec_apply]
      ring
    have hopposite : star (-eta) ⬝ᵥ c = 0 := by simp [hetaC]
    have hboundary := ccmActiveSource_boundary T (Matrix.diagonal clock) beta (-eta) c
      hdispOdd hTc hnorm hopposite
    have hmetric := ccmSourceCompletion_metricAdjoint T (Matrix.diagonal clock) beta (-eta) c
      hT.isHermitian hD hdispOdd hboundary
    have hriesz : ∀ v : Fin N → ℂ, T *ᵥ v = 0 →
        star c ⬝ᵥ v = (star c ⬝ᵥ c) * (star beta ⬝ᵥ v) :=
      fun v hv => ccmNormalizedRadicalProjection_riesz T beta hbetaActive v hv
    have heq := ccmCanonicalSourceResponseCompletion_eq_response T
      (Matrix.diagonal clock) eta beta hetaZero
    dsimp only
    have heq' : ccmCanonicalSourceResponseCompletion T (Matrix.diagonal clock)
        (fun _ : Fin N => (1 : ℂ)) beta =
        ccmSourceCompletion (Matrix.diagonal clock) c beta := by
      simpa [eta, c] using heq
    constructor
    · rw [heq']
      simpa [c] using hmetric
    · intro z hz
      rw [heq'] at hz
      have hz' : (ccmSourceCompletion (Matrix.diagonal clock) c beta).charpoly.eval z = 0 := by
        simpa [c] using hz
      exact ccmSourceCompletion_charpoly_zero_im_eq_zero T (Matrix.diagonal clock)
        c beta hT hD hnorm hriesz hmetric hz'

theorem ccmSourceResponseCompletion_dichotomy
    {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (clock beta : Fin N → ℂ)
    (hT : T.PosSemidef)
    (hD : (Matrix.diagonal clock).IsHermitian)
    (hclock : Function.Injective clock)
    (hdisp : Matrix.diagonal clock * T - T * Matrix.diagonal clock =
      Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
        Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta))
    (hkernel : ∃ k : Fin N → ℂ, T *ᵥ k = 0 ∧ k ≠ 0)
    (hcross : star beta ⬝ᵥ
      ccmRadicalProjection T (fun _ : Fin N => (1 : ℂ)) = 0) :
    (∃ c : Fin N → ℂ,
      T *ᵥ c = 0 ∧
      star (fun _ : Fin N => (1 : ℂ)) ⬝ᵥ c = 1 ∧
      T * ccmSourceCompletion (Matrix.diagonal clock) c (fun _ : Fin N => (1 : ℂ)) =
        (ccmSourceCompletion (Matrix.diagonal clock) c (fun _ : Fin N => (1 : ℂ)))ᴴ * T ∧
      ∀ z : ℂ,
        (ccmSourceCompletion (Matrix.diagonal clock) c (fun _ : Fin N => (1 : ℂ))).charpoly.eval z = 0 →
          z.im = 0) ∨
    (∃ c : Fin N → ℂ,
      T *ᵥ c = 0 ∧
      star beta ⬝ᵥ c = 1 ∧
      T * ccmSourceCompletion (Matrix.diagonal clock) c beta =
        (ccmSourceCompletion (Matrix.diagonal clock) c beta)ᴴ * T ∧
      ∀ z : ℂ,
        (ccmSourceCompletion (Matrix.diagonal clock) c beta).charpoly.eval z = 0 → z.im = 0) := by
  let eta : Fin N → ℂ := fun _ => 1
  rcases ccmSourceResponse_radicalProjection_exclusive T clock beta hT hclock hdisp
    hkernel hcross with ⟨hetaActive, hbetaZero⟩ | ⟨hetaZero, hbetaActive⟩
  · have hbetaAll : ∀ v : Fin N → ℂ, T *ᵥ v = 0 → star beta ⬝ᵥ v = 0 :=
      fun v hv => ccmPairing_eq_zero_of_radicalProjection_eq_zero T beta v hbetaZero hv
    exact Or.inl (by
      simpa [eta] using exists_ccmActiveSourceCompletion_charpoly_zero_im_eq_zero
        T (Matrix.diagonal clock) eta beta hT hD (by simpa [eta] using hdisp)
          hetaActive hbetaAll)
  · have hetaAll : ∀ v : Fin N → ℂ, T *ᵥ v = 0 → star eta ⬝ᵥ v = 0 :=
      fun v hv => ccmPairing_eq_zero_of_radicalProjection_eq_zero T eta v hetaZero hv
    have hdispOdd : Matrix.diagonal clock * T - T * Matrix.diagonal clock =
        Matrix.vecMulVec (-eta) (star beta) - Matrix.vecMulVec beta (star (-eta)) := by
      rw [show Matrix.diagonal clock * T - T * Matrix.diagonal clock =
        Matrix.vecMulVec beta (star eta) - Matrix.vecMulVec eta (star beta) by
          simpa [eta] using hdisp]
      ext i j
      simp [Matrix.vecMulVec_apply]
      ring
    have hopposite : ∀ v : Fin N → ℂ, T *ᵥ v = 0 →
        star (-eta) ⬝ᵥ v = 0 := by
      intro v hv
      simp [hetaAll v hv]
    exact Or.inr (by
      simpa [eta] using exists_ccmActiveSourceCompletion_charpoly_zero_im_eq_zero
        T (Matrix.diagonal clock) beta (-eta) hT hD hdispOdd hbetaActive hopposite)

theorem ccmSourceResponseCompletion_dichotomy_of_reflection
    {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (clock beta : Fin N → ℂ) (G : Matrix (Fin N) (Fin N) ℂ)
    (hT : T.PosSemidef)
    (hD : (Matrix.diagonal clock).IsHermitian)
    (hclock : Function.Injective clock)
    (hdisp : Matrix.diagonal clock * T - T * Matrix.diagonal clock =
      Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
        Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta))
    (hkernel : ∃ k : Fin N → ℂ, T *ᵥ k = 0 ∧ k ≠ 0)
    (hG : G.IsHermitian) (hG2 : G * G = 1)
    (hTG : T * G = G * T)
    (hetaG : G *ᵥ (fun _ : Fin N => (1 : ℂ)) = fun _ => 1)
    (hbetaG : G *ᵥ beta = -beta) :
    (∃ c : Fin N → ℂ,
      T *ᵥ c = 0 ∧
      star (fun _ : Fin N => (1 : ℂ)) ⬝ᵥ c = 1 ∧
      T * ccmSourceCompletion (Matrix.diagonal clock) c (fun _ : Fin N => (1 : ℂ)) =
        (ccmSourceCompletion (Matrix.diagonal clock) c (fun _ : Fin N => (1 : ℂ)))ᴴ * T ∧
      ∀ z : ℂ,
        (ccmSourceCompletion (Matrix.diagonal clock) c (fun _ : Fin N => (1 : ℂ))).charpoly.eval z = 0 →
          z.im = 0) ∨
    (∃ c : Fin N → ℂ,
      T *ᵥ c = 0 ∧
      star beta ⬝ᵥ c = 1 ∧
      T * ccmSourceCompletion (Matrix.diagonal clock) c beta =
        (ccmSourceCompletion (Matrix.diagonal clock) c beta)ᴴ * T ∧
      ∀ z : ℂ,
        (ccmSourceCompletion (Matrix.diagonal clock) c beta).charpoly.eval z = 0 → z.im = 0) := by
  apply ccmSourceResponseCompletion_dichotomy T clock beta hT hD hclock hdisp hkernel
  exact ccmRadicalProjection_source_response_cross_zero T G
    (fun _ : Fin N => (1 : ℂ)) beta hG hG2 hTG hetaG hbetaG

/-- Certificate that one of the two reflection-selected boundary channels supplies a normalized
radical completion with a fully real characteristic zero set. -/
def HasCCMSourceResponseCompletion
    {N : ℕ} (T D : Matrix (Fin N) (Fin N) ℂ) (beta : Fin N → ℂ) : Prop :=
  ∃ alpha c : Fin N → ℂ,
    (alpha = (fun _ : Fin N => (1 : ℂ)) ∨ alpha = beta) ∧
    T *ᵥ c = 0 ∧
    star alpha ⬝ᵥ c = 1 ∧
    T * ccmSourceCompletion D c alpha = (ccmSourceCompletion D c alpha)ᴴ * T ∧
    ∀ z : ℂ, (ccmSourceCompletion D c alpha).charpoly.eval z = 0 → z.im = 0

/-- Existing reflection/channel data produce a source-or-response completion certificate carrying
the additional full-characteristic-polynomial conclusion proved in this module.  Channel selection
itself is prior corpus knowledge. -/
theorem hasCCMSourceResponseCompletion_of_reflection
    {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (clock beta : Fin N → ℂ) (G : Matrix (Fin N) (Fin N) ℂ)
    (hT : T.PosSemidef)
    (hD : (Matrix.diagonal clock).IsHermitian)
    (hclock : Function.Injective clock)
    (hdisp : Matrix.diagonal clock * T - T * Matrix.diagonal clock =
      Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
        Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta))
    (hkernel : ∃ k : Fin N → ℂ, T *ᵥ k = 0 ∧ k ≠ 0)
    (hG : G.IsHermitian) (hG2 : G * G = 1)
    (hTG : T * G = G * T)
    (hetaG : G *ᵥ (fun _ : Fin N => (1 : ℂ)) = fun _ => 1)
    (hbetaG : G *ᵥ beta = -beta) :
    HasCCMSourceResponseCompletion T (Matrix.diagonal clock) beta := by
  rcases ccmSourceResponseCompletion_dichotomy_of_reflection T clock beta G
    hT hD hclock hdisp hkernel hG hG2 hTG hetaG hbetaG with hsource | hresponse
  · obtain ⟨c, hTc, hnorm, hmetric, hreal⟩ := hsource
    exact ⟨fun _ => 1, c, Or.inl rfl, hTc, hnorm, hmetric, hreal⟩
  · obtain ⟨c, hTc, hnorm, hmetric, hreal⟩ := hresponse
    exact ⟨beta, c, Or.inr rfl, hTc, hnorm, hmetric, hreal⟩

/-- Concrete connector for scalar-shifted CCM divided-difference matrices.  All displacement and
reflection interfaces are discharged from the underlying odd clock/source and even diagonal data;
only positive semidefiniteness and existence of a nonzero radical remain spectral inputs. -/
theorem ccmDividedDifferenceShift_hasSourceResponseCompletion
    {N : ℕ} (rho : Fin N ≃ Fin N) (hrho : ∀ i, rho (rho i) = i)
    (clock source diagonal : Fin N → ℝ) (mu : ℝ)
    (hclockInjective : Function.Injective clock)
    (hclockOdd : ∀ i, clock (rho i) = -clock i)
    (hsourceOdd : ∀ i, source (rho i) = -source i)
    (hdiagonalEven : ∀ i, diagonal (rho i) = diagonal i)
    (hT : ((ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu).map
      (algebraMap ℝ ℂ)).PosSemidef)
    (hkernel : ∃ k : Fin N → ℂ,
      (ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu).map
        (algebraMap ℝ ℂ) *ᵥ k = 0 ∧ k ≠ 0) :
    HasCCMSourceResponseCompletion
      ((ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu).map
        (algebraMap ℝ ℂ))
      (Matrix.diagonal (fun i => (clock i : ℂ)))
      (fun i => (source i : ℂ)) := by
  let Q := ccmDividedDifferenceMatrix clock source diagonal
  let T := (ccmScalarShift Q mu).map (algebraMap ℝ ℂ)
  let clockC : Fin N → ℂ := fun i => clock i
  let beta : Fin N → ℂ := fun i => source i
  let G := (ccmReflectionMatrix rho).map (algebraMap ℝ ℂ)
  apply hasCCMSourceResponseCompletion_of_reflection T clockC beta G
  · simpa [T, Q] using hT
  · simpa [clockC, ccmDiagonalClock] using
      (realSymmetric_complexification_isHermitian (ccmDiagonalClock clock)
        (ccmDiagonalClock_transpose clock))
  · intro i j hij
    apply hclockInjective
    change (clock i : ℂ) = (clock j : ℂ) at hij
    exact_mod_cast hij
  · have hreal := ccmScalarShift_displacement Q (ccmDiagonalClock clock)
        (Matrix.vecMulVec source ccmConstantBoundary -
          Matrix.vecMulVec ccmConstantBoundary source) mu
        (ccmDividedDifference_displacement clock source diagonal hclockInjective)
    have hmap := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ =>
      M.map (algebraMap ℝ ℂ)) hreal
    have hDmap : (ccmDiagonalClock clock).map (algebraMap ℝ ℂ) =
        Matrix.diagonal clockC := by
      ext i j
      by_cases hij : i = j <;>
        simp [ccmDiagonalClock, clockC, Matrix.diagonal, hij]
    have hRmap :
        (Matrix.vecMulVec source ccmConstantBoundary -
          Matrix.vecMulVec ccmConstantBoundary source).map (algebraMap ℝ ℂ) =
        Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
          Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta) := by
      ext i j
      simp [Matrix.vecMulVec_apply, ccmConstantBoundary, beta]
    change
      (ccmDiagonalClock clock * ccmScalarShift Q mu -
        ccmScalarShift Q mu * ccmDiagonalClock clock).map (algebraMap ℝ ℂ) =
      (Matrix.vecMulVec source ccmConstantBoundary -
        Matrix.vecMulVec ccmConstantBoundary source).map (algebraMap ℝ ℂ) at hmap
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul,
      hDmap, hRmap] at hmap
    simpa [T, Q] using hmap
  · simpa [T, Q] using hkernel
  · exact realSymmetric_complexification_isHermitian _
      (ccmReflectionMatrix_transpose rho hrho)
  · ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (rho i)]
    · by_cases hij : i = j
      · subst j
        simp [G, ccmReflectionMatrix, hrho]
      · have hji : j ≠ i := Ne.symm hij
        simp [G, ccmReflectionMatrix, hrho, hij, hji]
    · intro b hb hne
      simp [G, ccmReflectionMatrix, hne]
    · simp
  · have hreal := ccmScalarShift_commutes Q (ccmReflectionMatrix rho) mu
        (ccmReflectionMatrix_commutes_dividedDifference rho hrho clock source diagonal
          hclockOdd hsourceOdd hdiagonalEven)
    have hmap := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ =>
      M.map (algebraMap ℝ ℂ)) hreal
    change (ccmScalarShift Q mu * ccmReflectionMatrix rho).map (algebraMap ℝ ℂ) =
      (ccmReflectionMatrix rho * ccmScalarShift Q mu).map (algebraMap ℝ ℂ) at hmap
    rw [Matrix.map_mul, Matrix.map_mul] at hmap
    simpa [T, G, Q] using hmap
  · change (ccmReflectionMatrix rho).map (algebraMap ℝ ℂ) *ᵥ
        ((algebraMap ℝ ℂ) ∘ ccmConstantBoundary) =
      (algebraMap ℝ ℂ) ∘ ccmConstantBoundary
    funext i
    rw [← RingHom.map_mulVec]
    exact congrArg (algebraMap ℝ ℂ)
      (congr_fun (ccmReflectionMatrix_constantBoundary_even rho) i)
  · change (ccmReflectionMatrix rho).map (algebraMap ℝ ℂ) *ᵥ
        ((algebraMap ℝ ℂ) ∘ source) = -((algebraMap ℝ ℂ) ∘ source)
    funext i
    rw [← RingHom.map_mulVec]
    have hi := congr_fun (ccmReflectionMatrix_source_odd rho source hsourceOdd) i
    rw [hi]
    simp

noncomputable def normalizedCCMSourceResponseCompletionCharpoly
    (d : ℕ → ℕ) (A : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (u : ℕ → ℂ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  u k z * (A k).charpoly.eval z

theorem riemannHypothesis_of_normalizedCCMSourceResponseCompletionCharpoly_tendstoLocallyUniformly
    {d : ℕ → ℕ} {A : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ}
    {u : ℕ → ℂ → ℂ}
    (hreal : ∀ k z, (A k).charpoly.eval z = 0 → z.im = 0)
    (hu : ∀ k, Differentiable ℂ (u k))
    (hu0 : ∀ k z, u k z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (normalizedCCMSourceResponseCompletionCharpoly d A u) RHTower.XiC Filter.atTop) :
    RiemannHypothesis := by
  apply RHTower.riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconv
  · exact Filter.Eventually.of_forall fun k =>
      (hu k).mul (A k).charpoly.differentiable
  · apply Filter.Eventually.of_forall
    intro k z hz
    exact hreal k z ((mul_eq_zero.mp hz).resolve_left (hu0 k z))

end
end RHTower
