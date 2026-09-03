import GaloisForLFunctions.HTGeometry.HermitianGeodesicRay
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery
import GaloisForLFunctions.HTGeometry.OperatorNormLoewner
import GaloisForLFunctions.HTGeometry.MatrixQuadraticFormDetermination
import GaloisForLFunctions.HTGeometry.BuresWasserstein.OperatorGeometricMean
import GaloisForLFunctions.HTGeometry.StarOrderedConjugation
import GaloisForLFunctions.HTGeometry.EntrywiseQuadraticBound
import GaloisForLFunctions.HTGeometry.DiagonalNegativeMargin
import GaloisForLFunctions.HTGeometry.PencilCauchySchwarz
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.HermitianInertia
import GaloisForLFunctions.HTGeometry.MatrixSemicircleWardIdentity
import GaloisForLFunctions.HTGeometry.CompoundKyFan

/-!
# Uniform Stieltjes bound for finite matrix semicircles

This module proves the balanced-polar form of the finite-dimensional Dyson estimate
`‖G(z)‖₂ ≤ 2 * sqrt d / ‖z‖`.  The estimate is then combined with the exact Stieltjes atom
boundary law to exclude every atom away from zero.  Together with Hall exclusion at zero, this
supplies the full atomlessness input needed by matrix-valued Riemann--Lebesgue decay.
-/

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators Topology
open Matrix
open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

variable {I : Type*} [Fintype I] [DecidableEq I]

private def matrixSemicircleStieltjesAuxMatrixToHS (X : Matrix I I ℂ) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (fun ij => X ij.1 ij.2)

private def matrixSemicircleStieltjesAuxHSToMatrix (x : EuclideanSpace ℂ (I × I)) : Matrix I I ℂ :=
  fun i j => x (i, j)

@[simp] private theorem matrixSemicircleStieltjesAuxHSToMatrix_matrixSemicircleStieltjesAuxMatrixToHS (X : Matrix I I ℂ) :
    matrixSemicircleStieltjesAuxHSToMatrix (matrixSemicircleStieltjesAuxMatrixToHS X) = X := by
  ext i j
  rfl

@[simp] private theorem matrixSemicircleStieltjesAuxMatrixToHS_matrixSemicircleStieltjesAuxHSToMatrix (x : EuclideanSpace ℂ (I × I)) :
    matrixSemicircleStieltjesAuxMatrixToHS (matrixSemicircleStieltjesAuxHSToMatrix x) = x := by
  ext ij
  rfl

private theorem matrixSemicircleStieltjesAux_inner_eq_trace (x y : EuclideanSpace ℂ (I × I)) :
    inner ℂ x y = Matrix.trace ((matrixSemicircleStieltjesAuxHSToMatrix x)ᴴ * matrixSemicircleStieltjesAuxHSToMatrix y) := by
  change (∑ ij : I × I, y ij * star (x ij)) = _
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    matrixSemicircleStieltjesAuxHSToMatrix]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

private def matrixSemicircleStieltjesAuxMatrixMapHS
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) :
    EuclideanSpace ℂ (I × I) →ₗ[ℂ] EuclideanSpace ℂ (I × I) where
  toFun x := matrixSemicircleStieltjesAuxMatrixToHS (Phi (matrixSemicircleStieltjesAuxHSToMatrix x))
  map_add' x y := by
    ext ij
    change Phi (matrixSemicircleStieltjesAuxHSToMatrix (x + y)) ij.1 ij.2 =
      (Phi (matrixSemicircleStieltjesAuxHSToMatrix x) + Phi (matrixSemicircleStieltjesAuxHSToMatrix y)) ij.1 ij.2
    rw [show matrixSemicircleStieltjesAuxHSToMatrix (x + y) = matrixSemicircleStieltjesAuxHSToMatrix x + matrixSemicircleStieltjesAuxHSToMatrix y by ext <;> rfl]
    rw [Phi.map_add]
  map_smul' c x := by
    ext ij
    change Phi (matrixSemicircleStieltjesAuxHSToMatrix (c • x)) ij.1 ij.2 =
      (c • Phi (matrixSemicircleStieltjesAuxHSToMatrix x)) ij.1 ij.2
    rw [show matrixSemicircleStieltjesAuxHSToMatrix (c • x) = c • matrixSemicircleStieltjesAuxHSToMatrix x by ext <;> rfl]
    rw [Phi.map_smul]

private theorem matrixSemicircleStieltjesAuxMatrixMapHS_isSymmetric
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)
    (hsym : ∀ X Y, Matrix.trace (Xᴴ * Phi Y) =
      Matrix.trace ((Phi X)ᴴ * Y)) :
    (matrixSemicircleStieltjesAuxMatrixMapHS Phi).IsSymmetric := by
  intro x y
  rw [matrixSemicircleStieltjesAux_inner_eq_trace, matrixSemicircleStieltjesAux_inner_eq_trace]
  simpa [matrixSemicircleStieltjesAuxMatrixMapHS] using (hsym (matrixSemicircleStieltjesAuxHSToMatrix x) (matrixSemicircleStieltjesAuxHSToMatrix y)).symm

private theorem matrixSemicircleStieltjesAux_matrixMap_monotone
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)
    (hpos : ∀ X, X.PosSemidef → (Phi X).PosSemidef) :
    Monotone Phi := by
  intro X Y hXY
  rw [← sub_nonneg, ← Phi.map_sub]
  exact Matrix.nonneg_iff_posSemidef.mpr
    (hpos (Y - X) (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hXY)))

private theorem matrixSemicircleStieltjesAux_norm_quadForm_le_of_entries
    (E : Matrix I I ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hE : ∀ j k, ‖E j k‖ ≤ M) (x : I → ℂ) :
    ‖star x ⬝ᵥ E.mulVec x‖ ≤
      M * (Fintype.card I : ℝ) ^ 2 * ‖x‖ ^ 2 := by
  have hexp : star x ⬝ᵥ E.mulVec x =
      ∑ j, ∑ k, (starRingEnd ℂ) (x j) * (E j k * x k) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rfl
  rw [hexp]
  have hxle : ∀ j, ‖x j‖ ≤ ‖x‖ := fun j => norm_le_pi_norm x j
  have hnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  calc
    ‖∑ j, ∑ k, (starRingEnd ℂ) (x j) * (E j k * x k)‖
        ≤ ∑ j, ‖∑ k, (starRingEnd ℂ) (x j) * (E j k * x k)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _j : I, ∑ _k : I, M * ‖x‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        have h1 : ‖x j‖ * (‖E j k‖ * ‖x k‖) ≤
            ‖x‖ * (M * ‖x‖) := by
          apply mul_le_mul (hxle j) _ (by positivity) hnn
          exact mul_le_mul (hE j k) (hxle k) (norm_nonneg _) hM
        calc
          ‖x j‖ * (‖E j k‖ * ‖x k‖) ≤ ‖x‖ * (M * ‖x‖) := h1
          _ = M * ‖x‖ ^ 2 := by ring
    _ = M * (Fintype.card I : ℝ) ^ 2 * ‖x‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

private theorem matrixSemicircleStieltjesAux_sq_pi_norm_le_sum_sq (x : I → ℂ) :
    ‖x‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 := by
  have hnn : (0 : ℝ) ≤ ∑ j, ‖x j‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have hle : ‖x‖ ≤ Real.sqrt (∑ j, ‖x j‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
    intro j
    have hj : ‖x j‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2)
        (fun k _ => by positivity) (Finset.mem_univ j)
    calc
      ‖x j‖ = Real.sqrt (‖x j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ k, ‖x k‖ ^ 2) := Real.sqrt_le_sqrt hj
  calc
    ‖x‖ ^ 2 ≤ (Real.sqrt (∑ j, ‖x j‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg x) hle 2
    _ = ∑ j, ‖x j‖ ^ 2 := Real.sq_sqrt hnn

private theorem matrixSemicircleStieltjesAux_quadForm_one (x : I → ℂ) :
    star x ⬝ᵥ ((1 : Matrix I I ℂ).mulVec x) =
      ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
  have h := quadForm_conjTranspose_mul_self (1 : Matrix I I ℂ) x
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_mulVec] at h
  rw [Matrix.one_mulVec]
  exact h

private theorem matrixSemicircleStieltjesAux_dotProduct_mulVec_im_eq_zero
    {A : Matrix I I ℂ} (hA : A.IsHermitian) (x : I → ℂ) :
    (star x ⬝ᵥ A.mulVec x).im = 0 := by
  apply Complex.conj_eq_iff_im.1
  change star (star x ⬝ᵥ A.mulVec x) = star x ⬝ᵥ A.mulVec x
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hA.eq,
    ← Matrix.dotProduct_mulVec]

private theorem matrixSemicircleStieltjesAux_exists_posDef_order_bound
    (H Y : Matrix I I ℂ) (hH : H.PosDef) (hY : Y.IsHermitian) :
    ∃ c : ℝ, 0 ≤ c ∧ -(c • H) ≤ Y ∧ Y ≤ c • H := by
  let S : Matrix I I ℂ := CFC.sqrt H
  let W : Matrix I I ℂ := S⁻¹ * Y * S⁻¹
  let M : ℝ := ∑ i : I, ∑ j : I, ‖W i j‖
  let c : ℝ := M * (Fintype.card I : ℝ) ^ 2
  have hS : S.PosDef := positiveMatrixSqrt_posDef hH
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hSinvH : (S⁻¹).IsHermitian := hS.inv.isHermitian
  have hW : W.IsHermitian := by
    change (S⁻¹ * Y * S⁻¹)ᴴ = S⁻¹ * Y * S⁻¹
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hSinvH.eq, hY.eq]
    noncomm_ring
  have hsq : S * S = H := positiveMatrixSqrt_mul_self hH
  have hrecover : S * W * S = Y := by
    dsimp only [W]
    calc
      S * (S⁻¹ * Y * S⁻¹) * S = (S * S⁻¹) * Y * (S⁻¹ * S) := by
        noncomm_ring
      _ = Y := by rw [Matrix.mul_nonsing_inv S hSdet,
        Matrix.nonsing_inv_mul S hSdet, Matrix.one_mul, Matrix.mul_one]
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hentry : ∀ i j, ‖W i j‖ ≤ M := by
    intro i j
    dsimp only [M]
    have hrow : ‖W i j‖ ≤ ∑ k : I, ‖W i k‖ :=
      Finset.single_le_sum (fun k _ => norm_nonneg (W i k))
        (Finset.mem_univ j)
    have htotal : (∑ k : I, ‖W i k‖) ≤ ∑ a : I, ∑ k : I, ‖W a k‖ :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun k _ => norm_nonneg (W a k))
        (Finset.mem_univ i)
    exact hrow.trans htotal
  have hbound (x : I → ℂ) :
      ‖star x ⬝ᵥ W.mulVec x‖ ≤ c * ‖x‖ ^ 2 := by
    simpa [c] using matrixSemicircleStieltjesAux_norm_quadForm_le_of_entries W hM hentry x
  have hsum_nonneg (x : I → ℂ) :
      0 ≤ (star x ⬝ᵥ ((c • (1 : Matrix I I ℂ)) - W).mulVec x) := by
    rw [Complex.le_def]
    constructor
    · have hc : 0 ≤ c := mul_nonneg hM (sq_nonneg _)
      have hreal :
          (star x ⬝ᵥ W.mulVec x).re ≤ c * ‖x‖ ^ 2 :=
        le_trans (Complex.re_le_norm _) (hbound x)
      have hreal' :
          (star x ⬝ᵥ W.mulVec x).re ≤ c * ∑ i, ‖x i‖ ^ 2 :=
        hreal.trans (mul_le_mul_of_nonneg_left (matrixSemicircleStieltjesAux_sq_pi_norm_le_sum_sq x) hc)
      have hquad :
          (star x ⬝ᵥ ((c • (1 : Matrix I I ℂ)) - W).mulVec x).re =
            c * ∑ i, ‖x i‖ ^ 2 - (star x ⬝ᵥ W.mulVec x).re := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
          dotProduct_smul, matrixSemicircleStieltjesAux_quadForm_one]
        simp only [Complex.sub_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
      rw [hquad]
      simpa only [Complex.zero_re] using sub_nonneg.mpr hreal'
    · have hcI : (c • (1 : Matrix I I ℂ)).IsHermitian := by
        show (c • (1 : Matrix I I ℂ))ᴴ = c • (1 : Matrix I I ℂ)
        rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
        simp
      simpa using (matrixSemicircleStieltjesAux_dotProduct_mulVec_im_eq_zero (hcI.sub hW) x).symm
  have hupperW : W ≤ c • (1 : Matrix I I ℂ) := by
    rw [← sub_nonneg]
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (by
          have hcI : (c • (1 : Matrix I I ℂ)).IsHermitian := by
            show (c • (1 : Matrix I I ℂ))ᴴ = c • (1 : Matrix I I ℂ)
            rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
            simp
          exact hcI.sub hW)
        hsum_nonneg)
  have hsum_nonneg_neg (x : I → ℂ) :
      0 ≤ (star x ⬝ᵥ (W - (-(c • (1 : Matrix I I ℂ)))).mulVec x) := by
    rw [Complex.le_def]
    constructor
    · have hc : 0 ≤ c := mul_nonneg hM (sq_nonneg _)
      have hreal :
          -(c * ‖x‖ ^ 2) ≤ (star x ⬝ᵥ W.mulVec x).re := by
        have hneg : -(star x ⬝ᵥ W.mulVec x).re ≤ c * ‖x‖ ^ 2 := by
          calc
            -(star x ⬝ᵥ W.mulVec x).re =
                (- (star x ⬝ᵥ W.mulVec x)).re := by simp
            _ ≤ ‖-(star x ⬝ᵥ W.mulVec x)‖ := Complex.re_le_norm _
            _ = ‖star x ⬝ᵥ W.mulVec x‖ := norm_neg _
            _ ≤ c * ‖x‖ ^ 2 := hbound x
        linarith
      have hreal' :
          -(c * ∑ i, ‖x i‖ ^ 2) ≤ (star x ⬝ᵥ W.mulVec x).re := by
        have hs := mul_le_mul_of_nonneg_left (matrixSemicircleStieltjesAux_sq_pi_norm_le_sum_sq x) hc
        linarith
      have hquad :
          (star x ⬝ᵥ (W - (-(c • (1 : Matrix I I ℂ)))).mulVec x).re =
            (star x ⬝ᵥ W.mulVec x).re + c * ∑ i, ‖x i‖ ^ 2 := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.neg_mulVec,
          dotProduct_neg, Matrix.smul_mulVec, dotProduct_smul, matrixSemicircleStieltjesAux_quadForm_one]
        simp only [Complex.sub_re, Complex.neg_re, Complex.smul_re,
          Complex.ofReal_re]
        ring
      rw [hquad]
      change (0 : ℝ) ≤
        (star x ⬝ᵥ W.mulVec x).re + c * ∑ i, ‖x i‖ ^ 2
      linarith
    · have hcI : (c • (1 : Matrix I I ℂ)).IsHermitian := by
        show (c • (1 : Matrix I I ℂ))ᴴ = c • (1 : Matrix I I ℂ)
        rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
        simp
      simpa using (matrixSemicircleStieltjesAux_dotProduct_mulVec_im_eq_zero (hW.sub hcI.neg) x).symm
  have hlowerW : -(c • (1 : Matrix I I ℂ)) ≤ W := by
    rw [← sub_nonneg]
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (by
          have hcI : (c • (1 : Matrix I I ℂ)).IsHermitian := by
            show (c • (1 : Matrix I I ℂ))ᴴ = c • (1 : Matrix I I ℂ)
            rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
            simp
          exact hW.sub hcI.neg)
        hsum_nonneg_neg)
  refine ⟨c, mul_nonneg hM (sq_nonneg _), ?_, ?_⟩
  · have hnonneg : 0 ≤ S * (W + c • (1 : Matrix I I ℂ)) * S :=
      by
        simpa [star_eq_conjTranspose, hS.isHermitian.eq] using
          (star_conjugate_nonneg_of_nonneg
            (neg_le_iff_add_nonneg.mp hlowerW) S)
    simp only [Matrix.mul_add, Matrix.add_mul, hrecover, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hsq] at hnonneg
    exact neg_le_iff_add_nonneg.mpr (by simpa [add_comm] using hnonneg)
  · have hnonneg : 0 ≤ S * (c • (1 : Matrix I I ℂ) - W) * S :=
      by
        simpa [star_eq_conjTranspose, hS.isHermitian.eq] using
          (star_conjugate_nonneg_of_nonneg (sub_nonneg.mpr hupperW) S)
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hsq, hrecover] at hnonneg
    exact sub_nonneg.mp hnonneg

private theorem matrixSemicircleStieltjesAux_abs_quadratic_re_le_of_order_bound
    (H Z : Matrix I I ℂ) (c : ℝ)
    (hlower : -(c • H) ≤ Z) (hupper : Z ≤ c • H) (x : I → ℂ) :
    |(star x ⬝ᵥ Z.mulVec x).re| ≤
      c * (star x ⬝ᵥ H.mulVec x).re := by
  rw [abs_le]
  constructor
  · have hpsd : (Z - (-(c • H))).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hlower)
    have hq := hpsd.dotProduct_mulVec_nonneg x
    have hre := (Complex.le_def.mp hq).1
    have hcalc :
        (star x ⬝ᵥ (Z - (-(c • H))).mulVec x).re =
          (star x ⬝ᵥ Z.mulVec x).re +
            c * (star x ⬝ᵥ H.mulVec x).re := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.neg_mulVec, dotProduct_neg,
        Matrix.smul_mulVec, dotProduct_smul]
      simp only [Complex.sub_re, Complex.neg_re, Complex.smul_re, smul_eq_mul]
      ring
    rw [hcalc] at hre
    change (0 : ℝ) ≤ _ at hre
    linarith
  · have hpsd : ((c • H) - Z).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hupper)
    have hq := hpsd.dotProduct_mulVec_nonneg x
    have hre := (Complex.le_def.mp hq).1
    have hcalc :
        (star x ⬝ᵥ ((c • H) - Z).mulVec x).re =
          c * (star x ⬝ᵥ H.mulVec x).re -
            (star x ⬝ᵥ Z.mulVec x).re := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul]
      simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul]
    rw [hcalc] at hre
    change (0 : ℝ) ≤ _ at hre
    linarith

private theorem matrixSemicircleStieltjesAux_abs_eigenvalue_le_one_of_hermitian
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)
    (hpos : ∀ X, X.PosSemidef → (Phi X).PosSemidef)
    {H : Matrix I I ℂ} (hH : H.PosDef) (hsub : Phi H ≤ H)
    {mu : ℝ} {Y : Matrix I I ℂ} (hY : Y.IsHermitian) (hYne : Y ≠ 0)
    (heig : Phi Y = (mu : ℂ) • Y) :
    |mu| ≤ 1 := by
  by_contra hnot
  have hmu : 1 < |mu| := lt_of_not_ge hnot
  have hmono : Monotone Phi := matrixSemicircleStieltjesAux_matrixMap_monotone Phi hpos
  obtain ⟨c, hc, hlower, hupper⟩ :=
    matrixSemicircleStieltjesAux_exists_posDef_order_bound H Y hH hY
  have hscale : c • Phi H ≤ c • H :=
    smul_le_smul_of_nonneg_left hsub hc
  have hiterOrder : ∀ n : ℕ,
      -(c • H) ≤ (Phi^[n]) Y ∧ (Phi^[n]) Y ≤ c • H := by
    intro n
    induction n with
    | zero => simpa using And.intro hlower hupper
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        constructor
        · calc
            -(c • H) ≤ -(c • Phi H) := neg_le_neg hscale
            _ = Phi (-(c • H)) := by
              rw [Phi.map_neg]
              simpa using (Phi.map_smul (c : ℂ) H).symm
            _ ≤ Phi ((Phi^[n]) Y) := hmono ih.1
        · calc
            Phi ((Phi^[n]) Y) ≤ Phi (c • H) := hmono ih.2
            _ = c • Phi H := by
              simpa using Phi.map_smul (c : ℂ) H
            _ ≤ c • H := hscale
  have heigIter : ∀ n : ℕ,
      (Phi^[n]) Y = ((mu ^ n : ℝ) : ℂ) • Y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, Phi.map_smul, heig, smul_smul]
        push_cast
        ring
  obtain ⟨x, hx⟩ : ∃ x : I → ℂ, star x ⬝ᵥ Y.mulVec x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hYne
    apply matrix_eq_of_quadraticForm_eq Y 0
    intro x
    simpa using hcon x
  have hxre : (star x ⬝ᵥ Y.mulVec x).re ≠ 0 := by
    intro hre
    apply hx
    apply Complex.ext
    · simpa using hre
    · simpa using matrixSemicircleStieltjesAux_dotProduct_mulVec_im_eq_zero hY x
  have hxabs : 0 < |(star x ⬝ᵥ Y.mulVec x).re| := abs_pos.mpr hxre
  have hxzero : x ≠ 0 := by
    intro hzero
    subst x
    simp at hx
  have hHquad : 0 < (star x ⬝ᵥ H.mulVec x).re := by
    have hq := hH.dotProduct_mulVec_pos hxzero
    exact (Complex.lt_def.mp hq).1
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (c * (star x ⬝ᵥ H.mulVec x).re /
      |(star x ⬝ᵥ Y.mulVec x).re|) hmu
  have hstrict :
      c * (star x ⬝ᵥ H.mulVec x).re <
        |mu| ^ n * |(star x ⬝ᵥ Y.mulVec x).re| := by
    exact (div_lt_iff₀ hxabs).mp hn
  have hbound := matrixSemicircleStieltjesAux_abs_quadratic_re_le_of_order_bound H ((Phi^[n]) Y) c
    (hiterOrder n).1 (hiterOrder n).2 x
  rw [heigIter n, Matrix.smul_mulVec, dotProduct_smul] at hbound
  have hrealY := matrixSemicircleStieltjesAux_dotProduct_mulVec_im_eq_zero hY x
  have hrewrite :
      |(((mu ^ n : ℝ) : ℂ) • (star x ⬝ᵥ Y.mulVec x)).re| =
        |mu| ^ n * |(star x ⬝ᵥ Y.mulVec x).re| := by
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [abs_mul, abs_pow]
  rw [hrewrite] at hbound
  linarith

private theorem matrixSemicircleStieltjesAux_abs_eigenvalue_le_one
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)
    (hpos : ∀ X, X.PosSemidef → (Phi X).PosSemidef)
    (hstar : ∀ X, Phi Xᴴ = (Phi X)ᴴ)
    {H : Matrix I I ℂ} (hH : H.PosDef) (hsub : Phi H ≤ H)
    {mu : ℝ} {X : Matrix I I ℂ} (hXne : X ≠ 0)
    (heig : Phi X = (mu : ℂ) • X) :
    |mu| ≤ 1 := by
  by_cases hRne : X + Xᴴ ≠ 0
  · have hRherm : (X + Xᴴ).IsHermitian := by
      change (X + Xᴴ)ᴴ = X + Xᴴ
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
      exact add_comm _ _
    have hReig : Phi (X + Xᴴ) = (mu : ℂ) • (X + Xᴴ) := by
      rw [Phi.map_add, hstar, heig, Matrix.conjTranspose_smul]
      simp
    exact matrixSemicircleStieltjesAux_abs_eigenvalue_le_one_of_hermitian Phi hpos hH hsub
      hRherm hRne hReig
  · have hJne : Complex.I • (X - Xᴴ) ≠ 0 := by
      intro hJzero
      have hdiff : X - Xᴴ = 0 :=
        (smul_eq_zero.mp hJzero).resolve_left (by norm_num)
      have hxstar : Xᴴ = X := by
        exact (sub_eq_zero.mp hdiff).symm
      apply hXne
      rw [hxstar] at hRne
      have htwo : (2 : ℂ) • X = 0 := by
        simpa [two_smul] using not_ne_iff.mp hRne
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hJherm : (Complex.I • (X - Xᴴ)).IsHermitian := by
      change (Complex.I • (X - Xᴴ))ᴴ = Complex.I • (X - Xᴴ)
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose]
      have hstarI : star Complex.I = -Complex.I := by
        simpa only [Complex.star_def] using Complex.conj_I
      rw [hstarI]
      module
    have hJeig :
        Phi (Complex.I • (X - Xᴴ)) =
          (mu : ℂ) • (Complex.I • (X - Xᴴ)) := by
      rw [Phi.map_smul, Phi.map_sub, hstar, heig, Matrix.conjTranspose_smul]
      simp
      module
    exact matrixSemicircleStieltjesAux_abs_eigenvalue_le_one_of_hermitian Phi hpos hH hsub
      hJherm hJne hJeig

private theorem matrixSemicircleStieltjesAux_norm_matrixMapHS_apply_le
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)
    (hpos : ∀ X, X.PosSemidef → (Phi X).PosSemidef)
    (hstar : ∀ X, Phi Xᴴ = (Phi X)ᴴ)
    (hsym : ∀ X Y, Matrix.trace (Xᴴ * Phi Y) =
      Matrix.trace ((Phi X)ᴴ * Y))
    {H : Matrix I I ℂ} (hH : H.PosDef) (hsub : Phi H ≤ H)
    (x : EuclideanSpace ℂ (I × I)) :
    ‖matrixSemicircleStieltjesAuxMatrixMapHS Phi x‖ ≤ ‖x‖ := by
  let T := matrixSemicircleStieltjesAuxMatrixMapHS Phi
  have hT : T.IsSymmetric := matrixSemicircleStieltjesAuxMatrixMapHS_isSymmetric Phi hsym
  let n := Module.finrank ℂ (EuclideanSpace ℂ (I × I))
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (I × I)) = n := rfl
  let b := hT.eigenvectorBasis hn
  have hbasisEig (i : Fin n) :
      T (b i) = ((hT.eigenvalues hn i : ℝ) : ℂ) • b i := by
    exact hT.apply_eigenvectorBasis hn i
  have heigenAbs (i : Fin n) : |hT.eigenvalues hn i| ≤ 1 := by
    let X := matrixSemicircleStieltjesAuxHSToMatrix (b i)
    have hXne : X ≠ 0 := by
      intro hX
      have hbzero : b i = 0 := by
        rw [← matrixSemicircleStieltjesAuxMatrixToHS_matrixSemicircleStieltjesAuxHSToMatrix (b i)]
        change matrixSemicircleStieltjesAuxMatrixToHS X = 0
        rw [hX]
        rfl
      exact b.toBasis.ne_zero i (by
        simpa [OrthonormalBasis.coe_toBasis] using hbzero)
    have hXeig :
        Phi X = ((hT.eigenvalues hn i : ℝ) : ℂ) • X := by
      have hmatrix := congrArg matrixSemicircleStieltjesAuxHSToMatrix (hbasisEig i)
      calc
        Phi X = matrixSemicircleStieltjesAuxHSToMatrix
            (((hT.eigenvalues hn i : ℝ) : ℂ) • b i) := by
          simpa [T, matrixSemicircleStieltjesAuxMatrixMapHS, X] using hmatrix
        _ = ((hT.eigenvalues hn i : ℝ) : ℂ) • X := by
          ext a c
          rfl
    exact matrixSemicircleStieltjesAux_abs_eigenvalue_le_one Phi hpos hstar hH hsub hXne hXeig
  have hnormSq (v : EuclideanSpace ℂ (I × I)) :
      ‖v‖ ^ 2 = ∑ i : Fin n, ‖b.repr v i‖ ^ 2 := by
    rw [← b.repr.norm_map v]
    exact EuclideanSpace.norm_sq_eq _
  have hcoord (i : Fin n) :
      ‖b.repr (T x) i‖ ^ 2 ≤ ‖b.repr x i‖ ^ 2 := by
    rw [repr_of_diagonal b hbasisEig x i, norm_mul]
    have habs := heigenAbs i
    have hsquare : |hT.eigenvalues hn i| ^ 2 ≤ 1 := by
      have hmul := mul_self_le_mul_self
        (abs_nonneg (hT.eigenvalues hn i)) habs
      simpa [pow_two] using hmul
    have hnormReal :
        ‖((hT.eigenvalues hn i : ℝ) : ℂ)‖ = |hT.eigenvalues hn i| := by
      simp [Real.norm_eq_abs]
    rw [hnormReal]
    calc
      (|hT.eigenvalues hn i| * ‖b.repr x i‖) ^ 2 =
          |hT.eigenvalues hn i| ^ 2 * ‖b.repr x i‖ ^ 2 := by ring
      _ ≤ 1 * ‖b.repr x i‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
      _ = ‖b.repr x i‖ ^ 2 := one_mul _
  have hsquare : ‖T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hnormSq, hnormSq]
    exact Finset.sum_le_sum fun i _ => hcoord i
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

private def matrixSemicircleStieltjesAuxBalancedRadius (t : ℝ) : ℝ := Real.sqrt (t ^ 2 + 1)

private def matrixSemicircleStieltjesAuxBalancedPhase (t : ℝ) : ℂ :=
  ((t : ℂ) + Complex.I) / (matrixSemicircleStieltjesAuxBalancedRadius t : ℂ)

private theorem matrixSemicircleStieltjesAuxBalancedRadius_pos (t : ℝ) : 0 < matrixSemicircleStieltjesAuxBalancedRadius t := by
  exact Real.sqrt_pos.2 (by
    nlinarith [sq_nonneg t])

private theorem matrixSemicircleStieltjesAuxBalancedRadius_sq (t : ℝ) : matrixSemicircleStieltjesAuxBalancedRadius t ^ 2 = t ^ 2 + 1 := by
  rw [matrixSemicircleStieltjesAuxBalancedRadius, Real.sq_sqrt]
  nlinarith [sq_nonneg t]

private theorem matrixSemicircleStieltjesAuxBalancedPhase_star_mul_self (t : ℝ) :
    star (matrixSemicircleStieltjesAuxBalancedPhase t) * matrixSemicircleStieltjesAuxBalancedPhase t = 1 := by
  have hstar (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [show star z * z = ((starRingEnd ℂ) z) * z from rfl, RCLike.conj_mul]
    norm_cast
  rw [hstar]
  norm_cast
  have hnum : ‖(t : ℂ) + Complex.I‖ ^ 2 = t ^ 2 + 1 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hden : ‖(matrixSemicircleStieltjesAuxBalancedRadius t : ℂ)‖ = matrixSemicircleStieltjesAuxBalancedRadius t := by
    simpa [abs_of_pos (matrixSemicircleStieltjesAuxBalancedRadius_pos t)]
  rw [matrixSemicircleStieltjesAuxBalancedPhase, norm_div, div_pow, hnum, hden,
    matrixSemicircleStieltjesAuxBalancedRadius_sq]
  exact div_self (by nlinarith [sq_nonneg t])

private theorem matrixSemicircleStieltjesAuxBalancedPhase_mul_star (t : ℝ) :
    matrixSemicircleStieltjesAuxBalancedPhase t * star (matrixSemicircleStieltjesAuxBalancedPhase t) = 1 := by
  rw [mul_comm, matrixSemicircleStieltjesAuxBalancedPhase_star_mul_self]

private theorem matrixSemicircleStieltjesAuxBalancedPhase_mul_radius (t : ℝ) :
    matrixSemicircleStieltjesAuxBalancedPhase t * (matrixSemicircleStieltjesAuxBalancedRadius t : ℂ) = (t : ℂ) + Complex.I := by
  have hr0 : (matrixSemicircleStieltjesAuxBalancedRadius t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (matrixSemicircleStieltjesAuxBalancedRadius_pos t))
  rw [matrixSemicircleStieltjesAuxBalancedPhase, div_mul_cancel₀ _ hr0]

private theorem matrixSemicircleStieltjesAuxBalancedPhase_im (t : ℝ) :
    (matrixSemicircleStieltjesAuxBalancedPhase t).im = (matrixSemicircleStieltjesAuxBalancedRadius t)⁻¹ := by
  have hr0 : matrixSemicircleStieltjesAuxBalancedRadius t ≠ 0 := ne_of_gt (matrixSemicircleStieltjesAuxBalancedRadius_pos t)
  rw [matrixSemicircleStieltjesAuxBalancedPhase]
  simp [Complex.div_im]

private theorem matrixSemicircleStieltjesAux_quadForm_diagonal_ofReal_eq (r : I → ℝ) (x : I → ℂ) :
    star x ⬝ᵥ (Matrix.diagonal fun i => (r i : ℂ)).mulVec x =
      ((∑ i, r i * ‖x i‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  have hstar : (star x) i = (starRingEnd ℂ) (x i) := rfl
  rw [hstar]
  rw [show (r i : ℂ) * x i = x i * (r i : ℂ) from mul_comm _ _]
  rw [← mul_assoc]
  rw [mul_comm ((starRingEnd ℂ) (x i)) (x i)]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

private theorem matrixSemicircleStieltjesAux_diagonal_ofReal_posDef (r : I → ℝ) (hr : ∀ i, 0 < r i) :
    (Matrix.diagonal fun i => (r i : ℂ)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · refine Matrix.isHermitian_diagonal_iff.mpr fun i => ?_
    change star (r i : ℂ) = (r i : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
  · intro x hx
    rw [matrixSemicircleStieltjesAux_quadForm_diagonal_ofReal_eq]
    apply Complex.zero_lt_real.mpr
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (funext hcon)
    have hterm : 0 < r i * ‖x i‖ ^ 2 := by
      exact mul_pos (hr i) (sq_pos_of_pos (norm_pos_iff.mpr hi))
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum
        (f := fun j => r j * ‖x j‖ ^ 2)
        (fun j _ => mul_nonneg (le_of_lt (hr j)) (sq_nonneg _))
        (Finset.mem_univ i))

private theorem matrixSemicircleStieltjesAux_complex_hermitianImaginaryPart (z : ℂ) :
    (-Complex.I / 2) * (z - star z) = (z.im : ℂ) := by
  apply Complex.ext <;> simp <;> ring

set_option maxHeartbeats 1000000 in
private theorem matrixSemicircleStieltjesAux_exists_balanced_polar (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    ∃ P U : Matrix I I ℂ,
      P.PosDef ∧ Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (matrixHermitianImaginaryPart U).PosDef ∧
      A + Complex.I • (1 : Matrix I I ℂ) = P * U * P := by
  let V : Matrix I I ℂ := hA.eigenvectorUnitary
  let lam : I → ℝ := hA.eigenvalues
  let D : Matrix I I ℂ := Matrix.diagonal (fun i => matrixSemicircleStieltjesAuxBalancedPhase (lam i))
  let E : Matrix I I ℂ :=
    Matrix.diagonal (fun i => ((Real.sqrt (matrixSemicircleStieltjesAuxBalancedRadius (lam i)) : ℝ) : ℂ))
  let Rinv : Matrix I I ℂ :=
    Matrix.diagonal (fun i => (((matrixSemicircleStieltjesAuxBalancedRadius (lam i))⁻¹ : ℝ) : ℂ))
  let P : Matrix I I ℂ := V * E * Vᴴ
  let U : Matrix I I ℂ := V * D * Vᴴ
  have hVstarV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hVVstar : V * Vᴴ = 1 := by
    dsimp only [V]
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self _
  have hEpos : E.PosDef := by
    dsimp only [E]
    exact matrixSemicircleStieltjesAux_diagonal_ofReal_posDef _ fun i =>
      Real.sqrt_pos.2 (matrixSemicircleStieltjesAuxBalancedRadius_pos (lam i))
  have hPpos : P.PosDef := by
    dsimp only [P]
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · exact isHermitian_congruence hEpos.isHermitian.eq V
    · intro x hx
      have hy : Vᴴ *ᵥ x ≠ 0 := by
        intro hy0
        apply hx
        have h := congrArg V.mulVec hy0
        simpa [Matrix.mulVec_mulVec, hVVstar] using h
      have hpos := hEpos.dotProduct_mulVec_pos hy
      change matQuadForm (V * E * Vᴴ) x > 0
      have hq := matQuadForm_congr E Vᴴ x
      rw [Matrix.conjTranspose_conjTranspose] at hq
      rw [hq]
      simpa [matQuadForm] using hpos
  have hDstar : Dᴴ =
      Matrix.diagonal (fun i => star (matrixSemicircleStieltjesAuxBalancedPhase (lam i))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.conjTranspose_apply]
    · simp [D, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  have hDstarD : Dᴴ * D = 1 := by
    rw [hDstar]
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact matrixSemicircleStieltjesAuxBalancedPhase_star_mul_self _
    · simp [hij]
  have hDDstar : D * Dᴴ = 1 := by
    rw [hDstar]
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact matrixSemicircleStieltjesAuxBalancedPhase_mul_star _
    · simp [hij]
  have hUstar : Uᴴ = V * Dᴴ * Vᴴ := by
    dsimp only [U]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  have hUstarU : Uᴴ * U = 1 := by
    rw [hUstar]
    dsimp only [U]
    calc
      (V * Dᴴ * Vᴴ) * (V * D * Vᴴ) =
          V * Dᴴ * (Vᴴ * V) * D * Vᴴ := by noncomm_ring
      _ = V * (Dᴴ * D) * Vᴴ := by rw [hVstarV]; noncomm_ring
      _ = V * Vᴴ := by rw [hDstarD]; simp
      _ = 1 := hVVstar
  have hUUstar : U * Uᴴ = 1 := by
    rw [hUstar]
    dsimp only [U]
    calc
      (V * D * Vᴴ) * (V * Dᴴ * Vᴴ) =
          V * D * (Vᴴ * V) * Dᴴ * Vᴴ := by noncomm_ring
      _ = V * (D * Dᴴ) * Vᴴ := by rw [hVstarV]; noncomm_ring
      _ = V * Vᴴ := by rw [hDDstar]; simp
      _ = 1 := hVVstar
  have hImDiag : (-Complex.I / 2) • (D - Dᴴ) = Rinv := by
    ext i j
    dsimp only [D, Rinv]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.smul_apply, Matrix.sub_apply,
        Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
      rw [matrixSemicircleStieltjesAux_complex_hermitianImaginaryPart, matrixSemicircleStieltjesAuxBalancedPhase_im]
    · simp [hij]
  have hImU : matrixHermitianImaginaryPart U = V * Rinv * Vᴴ := by
    rw [matrixHermitianImaginaryPart, hUstar]
    dsimp only [U]
    calc
      (-Complex.I / 2) • (V * D * Vᴴ - V * Dᴴ * Vᴴ) =
          V * ((-Complex.I / 2) • (D - Dᴴ)) * Vᴴ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul,
          Matrix.mul_smul]
      _ = V * Rinv * Vᴴ := by rw [hImDiag]
  have hRinvPos : Rinv.PosDef := by
    dsimp only [Rinv]
    exact matrixSemicircleStieltjesAux_diagonal_ofReal_posDef _ fun i => inv_pos.mpr
      (matrixSemicircleStieltjesAuxBalancedRadius_pos (lam i))
  have hImPos : (matrixHermitianImaginaryPart U).PosDef := by
    rw [hImU]
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · exact isHermitian_congruence hRinvPos.isHermitian.eq V
    · intro x hx
      have hy : Vᴴ *ᵥ x ≠ 0 := by
        intro hy0
        apply hx
        have h := congrArg V.mulVec hy0
        simpa [Matrix.mulVec_mulVec, hVVstar] using h
      have hpos := hRinvPos.dotProduct_mulVec_pos hy
      change matQuadForm (V * Rinv * Vᴴ) x > 0
      have hq := matQuadForm_congr Rinv Vᴴ x
      rw [Matrix.conjTranspose_conjTranspose] at hq
      rw [hq]
      simpa [matQuadForm] using hpos
  have hEDE : E * D * E =
      Matrix.diagonal (fun i => ((lam i : ℂ) + Complex.I)) := by
    dsimp only [D, E]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hp : Real.sqrt (matrixSemicircleStieltjesAuxBalancedRadius (lam i)) ^ 2 =
        matrixSemicircleStieltjesAuxBalancedRadius (lam i) :=
      Real.sq_sqrt (le_of_lt (matrixSemicircleStieltjesAuxBalancedRadius_pos (lam i)))
    have hpC : (Real.sqrt (matrixSemicircleStieltjesAuxBalancedRadius (lam i)) : ℂ) *
        (Real.sqrt (matrixSemicircleStieltjesAuxBalancedRadius (lam i)) : ℂ) =
        (matrixSemicircleStieltjesAuxBalancedRadius (lam i) : ℂ) := by
      exact_mod_cast (show Real.sqrt (matrixSemicircleStieltjesAuxBalancedRadius (lam i)) *
        Real.sqrt (matrixSemicircleStieltjesAuxBalancedRadius (lam i)) =
          matrixSemicircleStieltjesAuxBalancedRadius (lam i) by simpa [pow_two] using hp)
    calc
      (Real.sqrt (matrixSemicircleStieltjesAuxBalancedRadius (lam i)) : ℂ) *
          matrixSemicircleStieltjesAuxBalancedPhase (lam i) *
          (Real.sqrt (matrixSemicircleStieltjesAuxBalancedRadius (lam i)) : ℂ) =
          matrixSemicircleStieltjesAuxBalancedPhase (lam i) * (matrixSemicircleStieltjesAuxBalancedRadius (lam i) : ℂ) := by
        rw [mul_comm (Real.sqrt (matrixSemicircleStieltjesAuxBalancedRadius (lam i)) : ℂ),
          mul_assoc, hpC]
      _ = (lam i : ℂ) + Complex.I := matrixSemicircleStieltjesAuxBalancedPhase_mul_radius _
  have hAeq : A = V * Matrix.diagonal (fun i => (lam i : ℂ)) * Vᴴ := by
    dsimp only [V, lam]
    simpa [Matrix.star_eq_conjTranspose] using isHermitian_eq_conj_diagonal hA
  have hfactor : A + Complex.I • (1 : Matrix I I ℂ) = P * U * P := by
    rw [hAeq]
    dsimp only [U, P]
    have hdiag : Matrix.diagonal (fun i => ((lam i : ℂ) + Complex.I)) =
        Matrix.diagonal (fun i => (lam i : ℂ)) +
          Complex.I • (1 : Matrix I I ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    have hleft : V * Matrix.diagonal (fun i => (lam i : ℂ)) * Vᴴ +
          Complex.I • (1 : Matrix I I ℂ) =
          V * Matrix.diagonal (fun i => ((lam i : ℂ) + Complex.I)) * Vᴴ := by
      rw [hdiag, Matrix.mul_add, Matrix.add_mul]
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hVVstar]
    rw [hleft]
    calc
      V * Matrix.diagonal (fun i => ((lam i : ℂ) + Complex.I)) * Vᴴ =
          V * (E * D * E) * Vᴴ := by rw [hEDE]
      _ = (V * E * Vᴴ) * (V * D * Vᴴ) * (V * E * Vᴴ) := by
        calc
          V * (E * D * E) * Vᴴ =
              V * E * (Vᴴ * V) * D * (Vᴴ * V) * E * Vᴴ := by
            rw [hVstarV]
            simp
            noncomm_ring
          _ = (V * E * Vᴴ) * (V * D * Vᴴ) * (V * E * Vᴴ) := by
            noncomm_ring
  exact ⟨P, U, hPpos, hUstarU, hUUstar, hImPos, hfactor⟩

private def matrixSemicircleStieltjesAuxCongruenceTransform
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) (q : Matrix I I ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun X := q * Phi (qᴴ * X * q) * qᴴ
  map_add' X Y := by
    rw [Matrix.mul_add, Matrix.add_mul, Phi.map_add,
      Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Phi.map_smul,
      Matrix.mul_smul, Matrix.smul_mul]
    rfl

private theorem matrixSemicircleStieltjesAuxCongruenceTransform_posSemidef
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) (q : Matrix I I ℂ)
    (hpos : ∀ X, X.PosSemidef → (Phi X).PosSemidef)
    (X : Matrix I I ℂ) (hX : X.PosSemidef) :
    (matrixSemicircleStieltjesAuxCongruenceTransform Phi q X).PosSemidef := by
  exact (hpos _ (hX.conjTranspose_mul_mul_same q)).mul_mul_conjTranspose_same q

private theorem matrixSemicircleStieltjesAuxCongruenceTransform_conjTranspose
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) (q : Matrix I I ℂ)
    (hstar : ∀ X, Phi Xᴴ = (Phi X)ᴴ) (X : Matrix I I ℂ) :
    matrixSemicircleStieltjesAuxCongruenceTransform Phi q Xᴴ = (matrixSemicircleStieltjesAuxCongruenceTransform Phi q X)ᴴ := by
  change q * Phi (qᴴ * Xᴴ * q) * qᴴ =
    (q * Phi (qᴴ * X * q) * qᴴ)ᴴ
  rw [show qᴴ * Xᴴ * q = (qᴴ * X * q)ᴴ by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    noncomm_ring]
  rw [hstar]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  noncomm_ring

private theorem matrixSemicircleStieltjesAuxCongruenceTransform_trace_symmetric
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) (q : Matrix I I ℂ)
    (hsym : ∀ X Y, Matrix.trace (Xᴴ * Phi Y) =
      Matrix.trace ((Phi X)ᴴ * Y)) (X Y : Matrix I I ℂ) :
    Matrix.trace (Xᴴ * matrixSemicircleStieltjesAuxCongruenceTransform Phi q Y) =
      Matrix.trace ((matrixSemicircleStieltjesAuxCongruenceTransform Phi q X)ᴴ * Y) := by
  have hleft : Matrix.trace
      (Xᴴ * (q * Phi (qᴴ * Y * q) * qᴴ)) =
      Matrix.trace ((qᴴ * X * q)ᴴ * Phi (qᴴ * Y * q)) := by
    calc
      Matrix.trace (Xᴴ * (q * Phi (qᴴ * Y * q) * qᴴ)) =
          Matrix.trace ((Xᴴ * q * Phi (qᴴ * Y * q)) * qᴴ) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (qᴴ * (Xᴴ * q * Phi (qᴴ * Y * q))) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((qᴴ * X * q)ᴴ * Phi (qᴴ * Y * q)) := by
        congr 1
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
        noncomm_ring
  have hright : Matrix.trace
      ((Phi (qᴴ * X * q))ᴴ * (qᴴ * Y * q)) =
      Matrix.trace ((q * Phi (qᴴ * X * q) * qᴴ)ᴴ * Y) := by
    calc
      Matrix.trace ((Phi (qᴴ * X * q))ᴴ * (qᴴ * Y * q)) =
          Matrix.trace (((Phi (qᴴ * X * q))ᴴ * qᴴ * Y) * q) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (q * ((Phi (qᴴ * X * q))ᴴ * qᴴ * Y)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((q * Phi (qᴴ * X * q) * qᴴ)ᴴ * Y) := by
        congr 1
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
        noncomm_ring
  change Matrix.trace (Xᴴ * (q * Phi (qᴴ * Y * q) * qᴴ)) =
    Matrix.trace ((q * Phi (qᴴ * X * q) * qᴴ)ᴴ * Y)
  exact hleft.trans ((hsym (qᴴ * X * q) (qᴴ * Y * q)).trans hright)

private theorem matrixSemicircleStieltjesAux_matrixHermitianImaginaryPart_add (X Y : Matrix I I ℂ) :
    matrixHermitianImaginaryPart (X + Y) =
      matrixHermitianImaginaryPart X + matrixHermitianImaginaryPart Y := by
  ext i j
  simp [matrixHermitianImaginaryPart, Matrix.conjTranspose_apply]
  ring

private theorem matrixSemicircleStieltjesAux_matrixHermitianImaginaryPart_smul_of_isHermitian
    (z : ℂ) (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    matrixHermitianImaginaryPart (z • X) = (z.im : ℂ) • X := by
  ext i j
  simp only [matrixHermitianImaginaryPart, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul]
  rw [star_mul]
  rw [show star (X j i) = X i j by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hX.eq i) j]
  apply Complex.ext <;> simp [Complex.star_def] <;> ring

private theorem matrixSemicircleStieltjesAux_matrixHermitianImaginaryPart_map
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)
    (hstar : ∀ X, Phi Xᴴ = (Phi X)ᴴ) (X : Matrix I I ℂ) :
    matrixHermitianImaginaryPart (Phi X) =
      Phi (matrixHermitianImaginaryPart X) := by
  rw [matrixHermitianImaginaryPart, matrixHermitianImaginaryPart,
    ← hstar, ← Phi.map_sub]
  simpa using (Phi.map_smul (-Complex.I / 2) (X - Xᴴ)).symm

private theorem matrixSemicircleStieltjesAux_matrixHermitianImaginaryPart_neg_conjTranspose
    (X : Matrix I I ℂ) :
    matrixHermitianImaginaryPart (-Xᴴ) = matrixHermitianImaginaryPart X := by
  ext i j
  simp [matrixHermitianImaginaryPart, Matrix.conjTranspose_apply]
  ring

private theorem matrixSemicircleStieltjesAux_norm_matrixToHS_sq_eq_trace (X : Matrix I I ℂ) :
    ‖matrixSemicircleStieltjesAuxMatrixToHS X‖ ^ 2 = (Matrix.trace (Xᴴ * X)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  exact congrArg Complex.re (by
    simpa using matrixSemicircleStieltjesAux_inner_eq_trace (matrixSemicircleStieltjesAuxMatrixToHS X) (matrixSemicircleStieltjesAuxMatrixToHS X))

private theorem matrixSemicircleStieltjesAux_norm_matrixToHS_unitary
    (U : Matrix I I ℂ) (hU : Uᴴ * U = 1) :
    ‖matrixSemicircleStieltjesAuxMatrixToHS U‖ = Real.sqrt (Fintype.card I : ℝ) := by
  have hsquare : ‖matrixSemicircleStieltjesAuxMatrixToHS U‖ ^ 2 = (Fintype.card I : ℝ) := by
    rw [matrixSemicircleStieltjesAux_norm_matrixToHS_sq_eq_trace, hU, Matrix.trace_one]
    simp
  rw [← Real.sqrt_sq (norm_nonneg _), hsquare]

private theorem matrixSemicircleStieltjesAux_norm_matrixToHS_unitaryConjugate
    (U X : Matrix I I ℂ) (hUUstar : U * Uᴴ = 1) :
    ‖matrixSemicircleStieltjesAuxMatrixToHS (Uᴴ * X * U)‖ = ‖matrixSemicircleStieltjesAuxMatrixToHS X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [matrixSemicircleStieltjesAux_norm_matrixToHS_sq_eq_trace, matrixSemicircleStieltjesAux_norm_matrixToHS_sq_eq_trace]
  congr 1
  calc
    Matrix.trace ((Uᴴ * X * U)ᴴ * (Uᴴ * X * U)) =
        Matrix.trace (Uᴴ * (Xᴴ * X) * U) := by
      congr 1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      calc
        Uᴴ * (Xᴴ * U) * (Uᴴ * X * U) =
            Uᴴ * Xᴴ * (U * Uᴴ) * X * U := by noncomm_ring
        _ = Uᴴ * (Xᴴ * X) * U := by rw [hUUstar]; noncomm_ring
    _ = Matrix.trace ((Xᴴ * X) * (U * Uᴴ)) := by
      calc
        Matrix.trace (Uᴴ * (Xᴴ * X) * U) =
            Matrix.trace (Uᴴ * ((Xᴴ * X) * U)) := by congr 1; noncomm_ring
        _ = Matrix.trace (((Xᴴ * X) * U) * Uᴴ) :=
          Matrix.trace_mul_comm _ _
        _ = Matrix.trace ((Xᴴ * X) * (U * Uᴴ)) := by congr 1; noncomm_ring
    _ = Matrix.trace (Xᴴ * X) := by rw [hUUstar, Matrix.mul_one]

private theorem matrixSemicircleStieltjesAux_norm_balanced_factor_le
    (q U : Matrix I I ℂ) (hUUstar : U * Uᴴ = 1) :
    ‖matrixSemicircleStieltjesAuxMatrixToHS (qᴴ * U * q)‖ ≤
      ‖matrixSemicircleStieltjesAuxMatrixToHS (q * qᴴ)‖ := by
  let Q : Matrix I I ℂ := q * qᴴ
  let B : Matrix I I ℂ := Uᴴ * Q * U
  have hQ : Q.IsHermitian := by
    dsimp only [Q]
    change (q * qᴴ)ᴴ = q * qᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hBnorm : ‖matrixSemicircleStieltjesAuxMatrixToHS B‖ = ‖matrixSemicircleStieltjesAuxMatrixToHS Q‖ := by
    exact matrixSemicircleStieltjesAux_norm_matrixToHS_unitaryConjugate U Q hUUstar
  have htrace : Matrix.trace ((qᴴ * U * q)ᴴ * (qᴴ * U * q)) =
      Matrix.trace (Bᴴ * Q) := by
    have hBherm : B.IsHermitian := by
      dsimp only [B]
      change (Uᴴ * Q * U)ᴴ = Uᴴ * Q * U
      simpa only [Matrix.conjTranspose_conjTranspose] using
        isHermitian_congruence hQ.eq Uᴴ
    rw [hBherm.eq]
    dsimp only [B, Q]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      Matrix.trace ((qᴴ * (Uᴴ * q)) * (qᴴ * U * q)) =
          Matrix.trace (qᴴ * ((Uᴴ * (q * qᴴ) * U) * q)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (((Uᴴ * (q * qᴴ) * U) * q) * qᴴ) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((Uᴴ * (q * qᴴ) * U) * (q * qᴴ)) := by
        congr 1
        noncomm_ring
  have hsquare : ‖matrixSemicircleStieltjesAuxMatrixToHS (qᴴ * U * q)‖ ^ 2 ≤
      ‖matrixSemicircleStieltjesAuxMatrixToHS Q‖ ^ 2 := by
    rw [matrixSemicircleStieltjesAux_norm_matrixToHS_sq_eq_trace, htrace]
    have hinner := norm_inner_le_norm
      (𝕜 := ℂ) (matrixSemicircleStieltjesAuxMatrixToHS B) (matrixSemicircleStieltjesAuxMatrixToHS Q)
    rw [matrixSemicircleStieltjesAux_inner_eq_trace] at hinner
    calc
      (Matrix.trace (Bᴴ * Q)).re ≤ ‖Matrix.trace (Bᴴ * Q)‖ :=
        Complex.re_le_norm _
      _ ≤ ‖matrixSemicircleStieltjesAuxMatrixToHS B‖ * ‖matrixSemicircleStieltjesAuxMatrixToHS Q‖ := hinner
      _ = ‖matrixSemicircleStieltjesAuxMatrixToHS Q‖ ^ 2 := by rw [hBnorm]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

private def matrixSemicircleStieltjesAuxMatrixHermitianRealPart (X : Matrix I I ℂ) : Matrix I I ℂ :=
  (2 : ℂ)⁻¹ • (X + Xᴴ)

private theorem matrixSemicircleStieltjesAuxMatrixHermitianRealPart_isHermitian (X : Matrix I I ℂ) :
    (matrixSemicircleStieltjesAuxMatrixHermitianRealPart X).IsHermitian := by
  change ((2 : ℂ)⁻¹ • (X + Xᴴ))ᴴ = (2 : ℂ)⁻¹ • (X + Xᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  simp
  abel

private theorem matrixSemicircleStieltjesAux_matrix_decompose_real_imaginary (X : Matrix I I ℂ) :
    X = matrixSemicircleStieltjesAuxMatrixHermitianRealPart X +
      Complex.I • matrixHermitianImaginaryPart X := by
  ext i j
  simp [matrixSemicircleStieltjesAuxMatrixHermitianRealPart, matrixHermitianImaginaryPart,
    Matrix.conjTranspose_apply]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
  ring_nf
  rw [hI]
  ring

set_option maxHeartbeats 1000000 in
private theorem matrixSemicircleStieltjesAux_dyson_hilbertSchmidt_bound
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)
    (hpos : ∀ X, X.PosSemidef → (Phi X).PosSemidef)
    (hstar : ∀ X, Phi Xᴴ = (Phi X)ᴴ)
    (hsym : ∀ X Y, Matrix.trace (Xᴴ * Phi Y) =
      Matrix.trace ((Phi X)ᴴ * Y))
    (G : Matrix I I ℂ) (z : ℂ) (hz : 0 < z.im)
    (hGim : (matrixHermitianImaginaryPart G).PosDef)
    (hdyson : (z • (1 : Matrix I I ℂ) + Phi G) * G = -1) :
    ‖matrixSemicircleStieltjesAuxMatrixToHS G‖ ≤
      (2 * Real.sqrt (Fintype.card I : ℝ)) / ‖z‖ := by
  let H : Matrix I I ℂ := matrixHermitianImaginaryPart G
  let R : Matrix I I ℂ := matrixSemicircleStieltjesAuxMatrixHermitianRealPart G
  let S : Matrix I I ℂ := CFC.sqrt H
  let A : Matrix I I ℂ := S⁻¹ * R * S⁻¹
  have hHpos : H.PosDef := hGim
  have hSpos : S.PosDef := positiveMatrixSqrt_posDef hHpos
  have hSstar : Sᴴ = S := hSpos.isHermitian.eq
  have hSinvStar : (S⁻¹)ᴴ = S⁻¹ := hSpos.inv.isHermitian.eq
  have hSdet : IsUnit S.det :=
    (Matrix.isUnit_iff_isUnit_det S).mp hSpos.isUnit
  have hSinvS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hSSinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
  have hSsq : S * S = H := positiveMatrixSqrt_mul_self hHpos
  have hRherm : R.IsHermitian := matrixSemicircleStieltjesAuxMatrixHermitianRealPart_isHermitian G
  have hAherm : A.IsHermitian := by
    dsimp only [A]
    change (S⁻¹ * R * S⁻¹)ᴴ = S⁻¹ * R * S⁻¹
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hSinvStar, hRherm.eq]
    noncomm_ring
  obtain ⟨P, U, hPpos, hUstarU, hUUstar, hUimPos, hpolar⟩ :=
    matrixSemicircleStieltjesAux_exists_balanced_polar A hAherm
  let q : Matrix I I ℂ := P * S
  let F : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ :=
    matrixSemicircleStieltjesAuxCongruenceTransform Phi q
  let Q : Matrix I I ℂ := q * qᴴ
  have hPstar : Pᴴ = P := hPpos.isHermitian.eq
  have hPrecover : S * A * S = R := by
    dsimp only [A]
    calc
      S * (S⁻¹ * R * S⁻¹) * S =
          (S * S⁻¹) * R * (S⁻¹ * S) := by noncomm_ring
      _ = R := by rw [hSSinv, hSinvS, Matrix.one_mul, Matrix.mul_one]
  have hGfactor : G = qᴴ * U * q := by
    rw [matrixSemicircleStieltjesAux_matrix_decompose_real_imaginary G]
    change R + Complex.I • H = qᴴ * U * q
    rw [← hPrecover, ← hSsq]
    calc
      S * A * S + Complex.I • (S * S) =
          S * (A + Complex.I • (1 : Matrix I I ℂ)) * S := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one]
      _ = S * (P * U * P) * S := by rw [hpolar]
      _ = qᴴ * U * q := by
        dsimp only [q]
        rw [Matrix.conjTranspose_mul, hPstar, hSstar]
        noncomm_ring
  have hQherm : Q.IsHermitian := by
    dsimp only [Q]
    change (q * qᴴ)ᴴ = q * qᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hQpsd : Q.PosSemidef := by
    dsimp only [Q]
    simpa using Matrix.PosSemidef.one.mul_mul_conjTranspose_same q
  have hqunit : IsUnit q := hPpos.isUnit.mul hSpos.isUnit
  have hUunit : IsUnit U :=
    ⟨⟨U, Uᴴ, hUUstar, hUstarU⟩, rfl⟩
  have hFpos : ∀ X, X.PosSemidef → (F X).PosSemidef := by
    intro X hX
    exact matrixSemicircleStieltjesAuxCongruenceTransform_posSemidef Phi q hpos X hX
  have hFstar : ∀ X, F Xᴴ = (F X)ᴴ := by
    intro X
    exact matrixSemicircleStieltjesAuxCongruenceTransform_conjTranspose Phi q hstar X
  have hFsym : ∀ X Y, Matrix.trace (Xᴴ * F Y) =
      Matrix.trace ((F X)ᴴ * Y) := by
    intro X Y
    exact matrixSemicircleStieltjesAuxCongruenceTransform_trace_symmetric Phi q hsym X Y
  have htransLeft : q * (z • (1 : Matrix I I ℂ) + Phi G) * qᴴ =
      z • Q + F U := by
    rw [hGfactor]
    dsimp only [F, Q]
    change q * (z • (1 : Matrix I I ℂ) + Phi (qᴴ * U * q)) * qᴴ =
      z • (q * qᴴ) + q * Phi (qᴴ * U * q) * qᴴ
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]
  have htrans : z • Q + F U = -Uᴴ := by
    rw [← htransLeft]
    apply (hUunit.mul hqunit).mul_right_cancel
    calc
      (q * (z • (1 : Matrix I I ℂ) + Phi G) * qᴴ) * (U * q) =
          q * (((z • (1 : Matrix I I ℂ) + Phi G) * G)) := by
        rw [hGfactor]
        noncomm_ring
      _ = -q := by rw [hdyson]; simp
      _ = (-Uᴴ) * (U * q) := by
        calc
          -q = -(1 * q) := by simp
          _ = -((Uᴴ * U) * q) := by rw [hUstarU]
          _ = (-Uᴴ) * (U * q) := by noncomm_ring
  have hImEq : matrixHermitianImaginaryPart U =
      (z.im : ℂ) • Q + F (matrixHermitianImaginaryPart U) := by
    calc
      matrixHermitianImaginaryPart U =
          matrixHermitianImaginaryPart (-Uᴴ) :=
        (matrixSemicircleStieltjesAux_matrixHermitianImaginaryPart_neg_conjTranspose U).symm
      _ = matrixHermitianImaginaryPart (z • Q + F U) := by rw [htrans]
      _ = matrixHermitianImaginaryPart (z • Q) +
          matrixHermitianImaginaryPart (F U) :=
        matrixSemicircleStieltjesAux_matrixHermitianImaginaryPart_add _ _
      _ = (z.im : ℂ) • Q + F (matrixHermitianImaginaryPart U) := by
        rw [matrixSemicircleStieltjesAux_matrixHermitianImaginaryPart_smul_of_isHermitian z Q hQherm,
          matrixSemicircleStieltjesAux_matrixHermitianImaginaryPart_map F hFstar U]
  have hyQnonneg : 0 ≤ (z.im : ℂ) • Q := by
    exact Matrix.nonneg_iff_posSemidef.mpr
      (hQpsd.smul (a := (z.im : ℂ)) (Complex.zero_le_real.mpr (le_of_lt hz)))
  have hFsub : F (matrixHermitianImaginaryPart U) ≤
      matrixHermitianImaginaryPart U := by
    have hle : F (matrixHermitianImaginaryPart U) ≤
        (z.im : ℂ) • Q + F (matrixHermitianImaginaryPart U) := by
      rw [← sub_nonneg]
      simpa only [add_sub_cancel_right] using hyQnonneg
    exact hle.trans_eq hImEq.symm
  have hcontract : ‖matrixSemicircleStieltjesAuxMatrixToHS (F U)‖ ≤ ‖matrixSemicircleStieltjesAuxMatrixToHS U‖ := by
    simpa [matrixSemicircleStieltjesAuxMatrixMapHS] using
      matrixSemicircleStieltjesAux_norm_matrixMapHS_apply_le F hFpos hFstar hFsym hUimPos hFsub
        (matrixSemicircleStieltjesAuxMatrixToHS U)
  have hQeq : z • Q = -Uᴴ - F U := by
    apply add_right_cancel (b := F U)
    simpa [sub_add_cancel] using htrans
  have hvec : z • matrixSemicircleStieltjesAuxMatrixToHS Q =
      -matrixSemicircleStieltjesAuxMatrixToHS Uᴴ - matrixSemicircleStieltjesAuxMatrixToHS (F U) := by
    ext ij
    change z * Q ij.1 ij.2 = -(Uᴴ) ij.1 ij.2 - F U ij.1 ij.2
    exact congrFun (congrFun hQeq ij.1) ij.2
  have hUnorm : ‖matrixSemicircleStieltjesAuxMatrixToHS U‖ =
      Real.sqrt (Fintype.card I : ℝ) :=
    matrixSemicircleStieltjesAux_norm_matrixToHS_unitary U hUstarU
  have hUstarNorm : ‖matrixSemicircleStieltjesAuxMatrixToHS Uᴴ‖ =
      Real.sqrt (Fintype.card I : ℝ) := by
    apply matrixSemicircleStieltjesAux_norm_matrixToHS_unitary
    simpa using hUUstar
  have hQmul : ‖z‖ * ‖matrixSemicircleStieltjesAuxMatrixToHS Q‖ ≤
      2 * Real.sqrt (Fintype.card I : ℝ) := by
    calc
      ‖z‖ * ‖matrixSemicircleStieltjesAuxMatrixToHS Q‖ = ‖z • matrixSemicircleStieltjesAuxMatrixToHS Q‖ :=
        (norm_smul z (matrixSemicircleStieltjesAuxMatrixToHS Q)).symm
      _ = ‖-matrixSemicircleStieltjesAuxMatrixToHS Uᴴ - matrixSemicircleStieltjesAuxMatrixToHS (F U)‖ := by rw [hvec]
      _ ≤ ‖-matrixSemicircleStieltjesAuxMatrixToHS Uᴴ‖ + ‖matrixSemicircleStieltjesAuxMatrixToHS (F U)‖ :=
        norm_sub_le _ _
      _ ≤ ‖matrixSemicircleStieltjesAuxMatrixToHS Uᴴ‖ + ‖matrixSemicircleStieltjesAuxMatrixToHS U‖ := by
        simpa using add_le_add_left hcontract ‖matrixSemicircleStieltjesAuxMatrixToHS Uᴴ‖
      _ = 2 * Real.sqrt (Fintype.card I : ℝ) := by
        rw [hUnorm, hUstarNorm]
        ring
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero] at hz
    simpa using hz
  have hQbound : ‖matrixSemicircleStieltjesAuxMatrixToHS Q‖ ≤
      (2 * Real.sqrt (Fintype.card I : ℝ)) / ‖z‖ := by
    exact (le_div_iff₀ (norm_pos_iff.mpr hz0)).2 (by
      simpa [mul_comm] using hQmul)
  rw [hGfactor]
  exact (matrixSemicircleStieltjesAux_norm_balanced_factor_le q U hUUstar).trans hQbound

private def matrixSemicircleStieltjesAuxMatrixSemicircleCovarianceLinearMap
    {K : Type*} [Fintype K] (A : K → Matrix I I ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun := matrixSemicircleCovariance A
  map_add' X Y := by
    simp [matrixSemicircleCovariance, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib]
  map_smul' c X := matrixSemicircleCovariance_smul A c X

/-- Finite matrix-semicircle Stieltjes transforms satisfy the uniform Hilbert--Schmidt bound
`‖G(z)‖₂ ≤ 2 * sqrt d / ‖z‖` throughout the upper half-plane. -/
theorem freeFockMatrixStieltjes_hilbertSchmidt_bound
    {K : Type*} [Fintype K] [DecidableEq K]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (z : ℂ) (hz : 0 < z.im) :
    ‖matrixSemicircleStieltjesAuxMatrixToHS (freeFockMatrixStieltjes A hA hker z)‖ ≤
      (2 * Real.sqrt (Fintype.card I : ℝ)) / ‖z‖ := by
  let Phi := matrixSemicircleStieltjesAuxMatrixSemicircleCovarianceLinearMap A
  let G := freeFockMatrixStieltjes A hA hker z
  have hpos : ∀ X, X.PosSemidef → (Phi X).PosSemidef := by
    intro X hX
    exact matrixSemicircleCovariance_posSemidef A hX
  have hstar : ∀ X, Phi Xᴴ = (Phi X)ᴴ := by
    intro X
    exact (matrixSemicircleCovariance_conjTranspose A X).symm
  have hsym : ∀ X Y, Matrix.trace (Xᴴ * Phi Y) =
      Matrix.trace ((Phi X)ᴴ * Y) := by
    intro X Y
    have h := matrixSemicircleCovariance_trace_duality A
      (fun k => hA k) Xᴴ Y
    calc
      Matrix.trace (Xᴴ * Phi Y) =
          Matrix.trace (Phi Xᴴ * Y) := h.symm
      _ = Matrix.trace ((Phi X)ᴴ * Y) := by rw [hstar X]
  have hGim : (matrixHermitianImaginaryPart G).PosDef :=
    freeFockMatrixStieltjes_hermitianImaginaryPart_posDef A hA hker z hz
  have hres := freeFockMatrixDysonResidual_upperHalfPlane A hA hker z hz
  have hdyson : (z • (1 : Matrix I I ℂ) + Phi G) * G = -1 := by
    change 1 + (z • (1 : Matrix I I ℂ) + Phi G) * G = 0 at hres
    exact eq_neg_of_add_eq_zero_right hres
  exact matrixSemicircleStieltjesAux_dyson_hilbertSchmidt_bound Phi hpos hstar hsym G z hz hGim hdyson

private theorem matrixSemicircleStieltjesAux_norm_matrixEntry_le_matrixToHS (X : Matrix I I ℂ) (i j : I) :
    ‖X i j‖ ≤ ‖matrixSemicircleStieltjesAuxMatrixToHS X‖ := by
  have hsq : ‖X i j‖ ^ 2 ≤ ‖matrixSemicircleStieltjesAuxMatrixToHS X‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum
      (f := fun p : I × I => ‖matrixSemicircleStieltjesAuxMatrixToHS X p‖ ^ 2)
      (fun p _ => sq_nonneg _) (Finset.mem_univ (i, j))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Every nonzero real energy has zero matrix atom for a full finite matrix semicircle. -/
theorem freeFockMatrixAtomMass_eq_zero_of_ne_zero
    {K : Type*} [Fintype K] [DecidableEq K]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) (ha : a ≠ 0) :
    freeFockMatrixAtomMass A hA hker a = 0 := by
  let z : ℝ → ℂ := fun y => (a : ℂ) + (y : ℂ) * Complex.I
  let C : ℝ := 2 * Real.sqrt (Fintype.card I : ℝ)
  have hright_le : 𝓝[>] (0 : ℝ) ≤ nhdsWithin 0 {0}ᶜ := by
    apply nhdsWithin_mono
    intro y hy
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_gt hy)
  have hyT : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hyCT : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left inf_le_left
  have hzT : Tendsto z (𝓝[>] 0) (𝓝 (a : ℂ)) := by
    dsimp only [z]
    simpa using tendsto_const_nhds.add (hyCT.mul_const Complex.I)
  have hnormzT : Tendsto (fun y => ‖z y‖) (𝓝[>] 0) (𝓝 ‖(a : ℂ)‖) :=
    tendsto_norm.comp hzT
  have hnorma : ‖(a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (by exact_mod_cast ha)
  have henv : Tendsto (fun y : ℝ => y * C / ‖z y‖)
      (𝓝[>] 0) (𝓝 0) := by
    have h := (hyT.mul_const C).div hnormzT hnorma
    change Tendsto ((fun y : ℝ => y * C) / fun y => ‖z y‖)
      (𝓝[>] 0) (𝓝 0)
    simpa using h
  ext i j
  have hzero : Tendsto
      (fun y : ℝ => (y : ℂ) * freeFockMatrixStieltjes A hA hker (z y) i j)
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
      henv
    · exact Filter.Eventually.of_forall fun y => norm_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hypos : 0 < y := hy
      have hzim : 0 < (z y).im := by
        dsimp only [z]
        simpa using hypos
      have hbound := freeFockMatrixStieltjes_hilbertSchmidt_bound
        A hA hker (z y) hzim
      have hentry := matrixSemicircleStieltjesAux_norm_matrixEntry_le_matrixToHS
        (freeFockMatrixStieltjes A hA hker (z y)) i j
      calc
        ‖(y : ℂ) * freeFockMatrixStieltjes A hA hker (z y) i j‖ =
            y * ‖freeFockMatrixStieltjes A hA hker (z y) i j‖ := by
          rw [norm_mul]
          simp [abs_of_pos hypos]
        _ ≤ y * ‖matrixSemicircleStieltjesAuxMatrixToHS
            (freeFockMatrixStieltjes A hA hker (z y))‖ :=
          mul_le_mul_of_nonneg_left hentry (le_of_lt hypos)
        _ ≤ y * (C / ‖z y‖) :=
          mul_le_mul_of_nonneg_left hbound (le_of_lt hypos)
        _ = y * C / ‖z y‖ := by ring
  have hboundary :=
    (freeFockMatrixStieltjes_atom_boundary A hA hker a i j).mono_left hright_le
  have heq : Complex.I * freeFockMatrixAtomMass A hA hker a i j = 0 :=
    tendsto_nhds_unique hboundary hzero
  exact (mul_eq_zero.mp heq).resolve_left (by norm_num)

end

end GaloisForLFunctions.HTGeometry
