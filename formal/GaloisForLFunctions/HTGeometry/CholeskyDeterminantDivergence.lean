import GaloisForLFunctions.HTGeometry.CofinalCholeskyFiniteFrame
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Determinant escape of a canonical inverse-Cholesky tower

This module isolates the asymptotic implication used in the singular repair law. Once the
normalized Gram determinants tend to zero, the exact finite inverse-Cholesky determinant identity
forces the normalized determinants of every canonical repair to escape to infinity. No OPUC or
Szegő theorem is assumed inside this implication; those theories supply its vanishing premise.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Filter
open scoped ComplexOrder Topology BigOperators NNReal InnerProduct

noncomputable section

/-- The positive normalized determinant root of a positive-definite Gram tower. -/
def normalizedGramDetRoot
    (G : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (N : ℕ) : ℝ :=
  (G N).det.re ^ (((N + 1 : ℕ) : ℝ)⁻¹)

/-- The positive normalized determinant root of a canonical inverse-Cholesky tower. -/
def normalizedFrameDetRoot
    (C : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (N : ℕ) : ℝ :=
  (C N).det.re ^ (((N + 1 : ℕ) : ℝ)⁻¹)

/-- At every finite level, the normalized frame determinant is the negative-half power of the
normalized Gram determinant. -/
theorem normalizedFrameDetRoot_eq_rpow_neg_half
    (G C : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hG : ∀ N, (G N).PosDef)
    (hC : ∀ N, IsCanonicalInverseCholeskyFrame (C N) (G N)) (N : ℕ) :
    normalizedFrameDetRoot C N = normalizedGramDetRoot G N ^ (-(1 : ℝ) / 2) := by
  let g : ℝ := (G N).det.re
  let r : ℝ := (((N + 1 : ℕ) : ℝ)⁻¹)
  have hg : 0 < g := by
    have hp := (hG N).det_pos
    simp only [Complex.lt_def, Complex.zero_re, Complex.zero_im] at hp
    exact hp.1
  have hc : (C N).det.re = g⁻¹.sqrt := by
    simpa [g] using canonicalInverseCholesky_det_eq_inv_sqrt (C N) (G N) (hG N) (hC N)
  have heq : g⁻¹.sqrt ^ r = (g ^ r) ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (g⁻¹ ^ (1 / (2 : ℝ))) ^ r = g⁻¹ ^ ((1 / (2 : ℝ)) * r) := by
        rw [Real.rpow_mul (inv_nonneg.mpr hg.le)]
      _ = (g⁻¹ ^ r) ^ (1 / (2 : ℝ)) := by
        rw [← Real.rpow_mul (inv_nonneg.mpr hg.le)]
        congr 1
        ring
      _ = (g ^ r)⁻¹ ^ (1 / (2 : ℝ)) := by rw [Real.inv_rpow hg.le]
      _ = (g ^ r) ^ (-(1 : ℝ) / 2) := by
        rw [← Real.rpow_neg_eq_inv_rpow]
        congr 1
        norm_num
  simpa only [normalizedFrameDetRoot, normalizedGramDetRoot, g, r, hc] using heq

/-- **Determinant escape law.** Vanishing normalized Gram determinants force the normalized
determinants of the canonical inverse-Cholesky repair to tend to infinity. -/
theorem normalizedFrameDetRoot_tendsto_atTop_of_gram_tendsto_zero
    (G C : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hG : ∀ N, (G N).PosDef)
    (hC : ∀ N, IsCanonicalInverseCholeskyFrame (C N) (G N))
    (hzero : Tendsto (normalizedGramDetRoot G) atTop (𝓝 0)) :
    Tendsto (normalizedFrameDetRoot C) atTop atTop := by
  have hpos : ∀ N, 0 < normalizedGramDetRoot G N := by
    intro N
    apply Real.rpow_pos_of_pos
    have hp := (hG N).det_pos
    simp only [Complex.lt_def, Complex.zero_re, Complex.zero_im] at hp
    exact hp.1
  have hzeroGT : Tendsto (normalizedGramDetRoot G) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzero, Filter.Eventually.of_forall hpos⟩
  have hescape := (tendsto_rpow_neg_nhdsGT_zero
    (by norm_num : (-(1 : ℝ) / 2) < 0)).comp hzeroGT
  exact hescape.congr' (Filter.Eventually.of_forall fun N =>
    (normalizedFrameDetRoot_eq_rpow_neg_half G C hG hC N).symm)

/-- Least eigenvalue of a finite positive-definite Hermitian matrix. -/
def leastEigenvalue {N : ℕ} (G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hG : G.PosDef) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hG.isHermitian.eigenvalues

theorem leastEigenvalue_pos {N : ℕ}
    (G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (hG : G.PosDef) :
    0 < leastEigenvalue G hG := by
  unfold leastEigenvalue
  rw [Finset.lt_inf'_iff]
  intro i hi
  exact hG.eigenvalues_pos i

theorem leastEigenvalue_le_eigenvalue {N : ℕ}
    (G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (hG : G.PosDef)
    (i : Fin (N + 1)) :
    leastEigenvalue G hG ≤ hG.isHermitian.eigenvalues i := by
  unfold leastEigenvalue
  exact Finset.inf'_le hG.isHermitian.eigenvalues (Finset.mem_univ i)

/-- The least eigenvalue to the matrix dimension is bounded by the determinant. -/
theorem leastEigenvalue_pow_card_le_det_re {N : ℕ}
    (G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (hG : G.PosDef) :
    leastEigenvalue G hG ^ (N + 1) ≤ G.det.re := by
  have hprod :
      (∏ _i : Fin (N + 1), leastEigenvalue G hG) ≤
        ∏ i : Fin (N + 1), hG.isHermitian.eigenvalues i := by
    apply Finset.prod_le_prod
    · intro i hi
      exact (leastEigenvalue_pos G hG).le
    · intro i hi
      exact leastEigenvalue_le_eigenvalue G hG i
  have hdet := hG.isHermitian.det_eq_prod_eigenvalues
  have hre := congrArg Complex.re hdet
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hre' : G.det.re = ∏ i : Fin (N + 1), hG.isHermitian.eigenvalues i := by
    calc
      G.det.re = (∏ i : Fin (N + 1),
          (hG.isHermitian.eigenvalues i : ℂ)).re := hre
      _ = ∏ i : Fin (N + 1), hG.isHermitian.eigenvalues i := by
        norm_cast
  exact hprod.trans_eq hre'.symm

/-- The least eigenvalue lies below the normalized determinant root. -/
theorem leastEigenvalue_le_normalizedGramDetRoot
    (G : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hG : ∀ N, (G N).PosDef) (N : ℕ) :
    leastEigenvalue (G N) (hG N) ≤ normalizedGramDetRoot G N := by
  unfold normalizedGramDetRoot
  rw [Real.le_rpow_inv_iff_of_pos]
  · rw [Real.rpow_natCast]
    exact leastEigenvalue_pow_card_le_det_re (G N) (hG N)
  · exact (leastEigenvalue_pos (G N) (hG N)).le
  · have hp := (hG N).det_pos
    simp only [Complex.lt_def, Complex.zero_re, Complex.zero_im] at hp
    exact hp.1.le
  · positivity

/-- Vanishing normalized Gram determinants force the least Gram eigenvalue to zero. -/
theorem leastEigenvalue_tendsto_zero_of_normalizedGramDetRoot_tendsto_zero
    (G : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hG : ∀ N, (G N).PosDef)
    (hzero : Tendsto (normalizedGramDetRoot G) atTop (𝓝 0)) :
    Tendsto (fun N => leastEigenvalue (G N) (hG N)) atTop (𝓝 0) := by
  exact squeeze_zero
    (fun N => (leastEigenvalue_pos (G N) (hG N)).le)
    (fun N => leastEigenvalue_le_normalizedGramDetRoot G hG N)
    hzero

/-- Euclidean operator norm of a finite complex matrix. This is the `ℓ²` norm used in the
inverse-Cholesky repair law, rather than the unrelated entrywise or row-sum matrix norms. -/
def euclideanMatrixOpNorm {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap C.toEuclideanLin‖

/-- A positive-definite eigenvector remains an eigenvector of the nonsingular inverse with
reciprocal eigenvalue. -/
theorem nonsingInv_mulVec_eq_inv_smul_of_mulVec_eq_smul
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef)
    (v : Fin N → ℂ) (lambda : ℝ) (hlam : 0 < lambda)
    (heig : G *ᵥ v = (lambda : ℂ) • v) :
    G⁻¹ *ᵥ v = (lambda⁻¹ : ℂ) • v := by
  have hdet : IsUnit G.det := by
    apply isUnit_iff_ne_zero.mpr
    exact ne_of_gt hG.det_pos
  have hinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have heq : (lambda : ℂ) • (G⁻¹ *ᵥ v) = v := by
    calc
      (lambda : ℂ) • (G⁻¹ *ᵥ v) = G⁻¹ *ᵥ ((lambda : ℂ) • v) := by
        rw [mulVec_smul]
      _ = G⁻¹ *ᵥ (G *ᵥ v) := by rw [heig]
      _ = (G⁻¹ * G) *ᵥ v := by rw [mulVec_mulVec]
      _ = v := by rw [hinv, one_mulVec]
  ext j
  have hj := congrFun heq j
  simp only [Pi.smul_apply, smul_eq_mul] at hj ⊢
  apply mul_left_cancel₀ (show (lambda : ℂ) ≠ 0 by exact_mod_cast hlam.ne')
  rw [hj]
  field_simp

/-- An inverse-Cholesky frame has Euclidean operator norm at least the reciprocal square root of
each Gram eigenvalue represented by a unit eigenvector. -/
theorem euclideanMatrixOpNorm_ge_inv_sqrt_of_eigenvector
    {N : ℕ} (C G : Matrix (Fin N) (Fin N) ℂ)
    (hG : G.PosDef) (hC : IsInverseCholeskyFrame C G)
    (x : EuclideanSpace ℂ (Fin N)) (lambda : ℝ)
    (hlambda : 0 < lambda) (hxnorm : ‖x‖ = 1)
    (heig : G *ᵥ x.ofLp = (lambda : ℂ) • x.ofLp) :
    lambda⁻¹.sqrt ≤ euclideanMatrixOpNorm C := by
  let L : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
    LinearMap.toContinuousLinearMap C.toEuclideanLin
  let K : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
    LinearMap.toContinuousLinearMap (G⁻¹).toEuclideanLin
  have hcomp : L† ∘L L = K := by
    apply ContinuousLinearMap.ext
    intro y
    change (L†) (L y) = K y
    rw [show (L†) = LinearMap.toContinuousLinearMap C.toEuclideanLin.adjoint by
      exact (LinearMap.adjoint_toContinuousLinearMap C.toEuclideanLin).symm]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change WithLp.toLp 2 (Cᴴ *ᵥ (C *ᵥ y.ofLp)) =
      WithLp.toLp 2 (G⁻¹ *ᵥ y.ofLp)
    rw [mulVec_mulVec, ← inverse_eq_conjTranspose_mul_of_inverseCholesky C G hC]
  have hinveig : G⁻¹ *ᵥ x.ofLp = (lambda⁻¹ : ℂ) • x.ofLp :=
    nonsingInv_mulVec_eq_inv_smul_of_mulVec_eq_smul G hG x.ofLp lambda hlambda heig
  have hnormsq : ‖L x‖ ^ 2 = lambda⁻¹ := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left, hcomp]
    change Complex.re (inner ℂ (WithLp.toLp 2 (G⁻¹ *ᵥ x.ofLp)) x) = lambda⁻¹
    rw [hinveig]
    change Complex.re (inner ℂ ((lambda⁻¹ : ℂ) • x) x) = lambda⁻¹
    rw [inner_smul_left]
    simp [hxnorm]
  have hnorm : ‖L x‖ = lambda⁻¹.sqrt := by
    rw [← Real.sq_sqrt (inv_nonneg.mpr hlambda.le)] at hnormsq
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hnormsq
  have hop := L.le_opNorm x
  rw [hxnorm, mul_one, hnorm] at hop
  exact hop

/-- The canonical repair norm is bounded below by the reciprocal square root of the least Gram
eigenvalue. -/
theorem euclideanMatrixOpNorm_ge_leastEigenvalue_inv_sqrt
    {N : ℕ} (C G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hG : G.PosDef) (hC : IsCanonicalInverseCholeskyFrame C G) :
    (leastEigenvalue G hG)⁻¹.sqrt ≤ euclideanMatrixOpNorm C := by
  obtain ⟨i, hi_mem, hi⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Fin (N + 1)))) Finset.univ_nonempty
      hG.isHermitian.eigenvalues
  let x : EuclideanSpace ℂ (Fin (N + 1)) := hG.isHermitian.eigenvectorBasis i
  have hxnorm : ‖x‖ = 1 := by
    exact (hG.isHermitian.eigenvectorBasis).orthonormal.norm_eq_one i
  have heig : G *ᵥ x.ofLp = (hG.isHermitian.eigenvalues i : ℂ) • x.ofLp := by
    exact hG.isHermitian.mulVec_eigenvectorBasis i
  have hbound := euclideanMatrixOpNorm_ge_inv_sqrt_of_eigenvector C G hG hC.1 x
    (hG.isHermitian.eigenvalues i) (hG.eigenvalues_pos i) hxnorm heig
  rwa [show leastEigenvalue G hG = hG.isHermitian.eigenvalues i by exact hi]

/-- Euclidean operator norm of a finite canonical frame tower. -/
def euclideanFrameOpNorm
    (C : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (N : ℕ) : ℝ :=
  euclideanMatrixOpNorm (C N)

/-- **Operator-norm escape law.** Vanishing normalized Gram determinants force the Euclidean
operator norms of the canonical repairs to tend to infinity. -/
theorem euclideanFrameOpNorm_tendsto_atTop_of_normalizedGramDetRoot_tendsto_zero
    (G C : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hG : ∀ N, (G N).PosDef)
    (hC : ∀ N, IsCanonicalInverseCholeskyFrame (C N) (G N))
    (hzero : Tendsto (normalizedGramDetRoot G) atTop (𝓝 0)) :
    Tendsto (euclideanFrameOpNorm C) atTop atTop := by
  let ell : ℕ → ℝ := fun N => leastEigenvalue (G N) (hG N)
  have hellZero : Tendsto ell atTop (𝓝 0) :=
    leastEigenvalue_tendsto_zero_of_normalizedGramDetRoot_tendsto_zero G hG hzero
  have hellPos : ∀ N, 0 < ell N := fun N => leastEigenvalue_pos (G N) (hG N)
  have hellGT : Tendsto ell atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hellZero, Filter.Eventually.of_forall hellPos⟩
  have hrpow : Tendsto (fun N => ell N ^ (-(1 : ℝ) / 2)) atTop atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-(1 : ℝ) / 2) < 0)).comp hellGT
  have hsqrt : Tendsto (fun N => (ell N)⁻¹.sqrt) atTop atTop := by
    apply hrpow.congr'
    apply Filter.Eventually.of_forall
    intro N
    simp only
    rw [Real.sqrt_eq_rpow, Real.inv_rpow (hellPos N).le,
      ← Real.rpow_neg (hellPos N).le]
    norm_num
  apply tendsto_atTop_mono (fun N => ?_) hsqrt
  exact euclideanMatrixOpNorm_ge_leastEigenvalue_inv_sqrt (C N) (G N) (hG N) (hC N)

end

end GaloisForLFunctions.HTGeometry
