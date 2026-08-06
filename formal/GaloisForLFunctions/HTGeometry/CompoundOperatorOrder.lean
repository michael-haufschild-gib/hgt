import GaloisForLFunctions.HTGeometry.CompoundKyFan
import GaloisForLFunctions.HTGeometry.CordesGeneralExponent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The quadratic form of a matrix and the operator order

The comparison of Hermitian forms used for the compound estimates,

```text
∀ x, (matQuadForm M x).re ≤ (matQuadForm N x).re,
```

is the order of the C⋆-algebra of operators on `EuclideanSpace ℂ κ`, transported along the star
algebra equivalence that sends a matrix to the operator it defines.  This is what lets the
operator-order inequalities — where the functional calculus lives — be read as statements about
subset products of a pencil spectrum, where the compound estimates live.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-! ## The form of a matrix is an inner product -/

theorem matQuadForm_eq_inner (M : Matrix κ κ ℂ) (x : EuclideanSpace ℂ κ) :
    matQuadForm M (WithLp.ofLp x) = inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) M x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, matQuadForm,
    dotProduct_comm]

/-! ## Hermitian matrices give self-adjoint operators -/

theorem isSelfAdjoint_toEuclideanCLM {M : Matrix κ κ ℂ} (hM : M.IsHermitian) :
    IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) M) := by
  show star (Matrix.toEuclideanCLM (𝕜 := ℂ) M) = Matrix.toEuclideanCLM (𝕜 := ℂ) M
  rw [← map_star, Matrix.star_eq_conjTranspose, hM.eq]

/-! ## The dictionary -/

omit [DecidableEq κ] in
theorem re_inner_swap (T : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ)
    (x : EuclideanSpace ℂ κ) :
    (inner ℂ (T x) x : ℂ).re = (inner ℂ x (T x) : ℂ).re := by
  have h : (starRingEnd ℂ) (inner ℂ (T x) x : ℂ) = (inner ℂ x (T x) : ℂ) :=
    inner_conj_symm _ _
  rw [← h, Complex.conj_re]

omit [DecidableEq κ] in
theorem matQuadForm_sub (M N : Matrix κ κ ℂ) (x : κ → ℂ) :
    matQuadForm (N - M) x = matQuadForm N x - matQuadForm M x := by
  simp only [matQuadForm, Matrix.sub_mulVec, dotProduct_sub]

/-- **The comparison of Hermitian forms is the operator order.** -/
theorem toEuclideanCLM_le_iff {M N : Matrix κ κ ℂ} (hM : M.IsHermitian) (hN : N.IsHermitian) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) M ≤ Matrix.toEuclideanCLM (𝕜 := ℂ) N
      ↔ ∀ x : κ → ℂ, (matQuadForm M x).re ≤ (matQuadForm N x).re := by
  have hdiff : Matrix.toEuclideanCLM (𝕜 := ℂ) N - Matrix.toEuclideanCLM (𝕜 := ℂ) M
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (N - M) := (map_sub _ _ _).symm
  have hre : ∀ x : EuclideanSpace ℂ κ,
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (N - M)).reApplyInnerSelf x
        = (matQuadForm N (WithLp.ofLp x)).re - (matQuadForm M (WithLp.ofLp x)).re := by
    intro x
    rw [ContinuousLinearMap.reApplyInnerSelf]
    have h1 : (inner ℂ ((Matrix.toEuclideanCLM (𝕜 := ℂ) (N - M)) x) x : ℂ).re
        = (matQuadForm (N - M) (WithLp.ofLp x)).re := by
      rw [re_inner_swap, ← matQuadForm_eq_inner]
    rw [show RCLike.re (inner ℂ ((Matrix.toEuclideanCLM (𝕜 := ℂ) (N - M)) x) x)
        = (inner ℂ ((Matrix.toEuclideanCLM (𝕜 := ℂ) (N - M)) x) x : ℂ).re from rfl, h1,
      matQuadForm_sub, Complex.sub_re]
  rw [ContinuousLinearMap.le_def, hdiff]
  constructor
  · rintro ⟨-, hpos⟩ x
    have h := hpos (WithLp.toLp 2 x)
    rw [hre] at h
    have hx : (WithLp.ofLp (WithLp.toLp 2 x) : κ → ℂ) = x := rfl
    rw [hx] at h
    linarith
  · intro h
    refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_toEuclideanCLM (hN.sub hM)), fun x => ?_⟩
    rw [hre]
    linarith [h (WithLp.ofLp x)]


/-! ## Scaled comparison -/

omit [DecidableEq κ] in
theorem coe_smul_clm (r : ℝ) (T : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ) :
    ((r : ℂ)) • T = r • T :=
  Complex.coe_smul r T

omit [Fintype κ] [DecidableEq κ] in
theorem isHermitian_smul_real (c : ℝ) {M : Matrix κ κ ℂ} (h : M.IsHermitian) :
    (((c : ℂ)) • M).IsHermitian := by
  show ((c : ℂ) • M)ᴴ = (c : ℂ) • M
  rw [Matrix.conjTranspose_smul, h.eq]
  congr 1
  simp

omit [DecidableEq κ] in
theorem matQuadForm_smul (c : ℝ) (M : Matrix κ κ ℂ) (x : κ → ℂ) :
    (matQuadForm ((c : ℂ) • M) x).re = c * (matQuadForm M x).re := by
  have h : matQuadForm ((c : ℂ) • M) x = (c : ℂ) * matQuadForm M x := by
    rw [matQuadForm, matQuadForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [h, Complex.re_ofReal_mul]

/-- **The scaled comparison of Hermitian forms is the scaled operator order.** -/
theorem toEuclideanCLM_smul_le_iff {M N : Matrix κ κ ℂ} (hM : M.IsHermitian) (hN : N.IsHermitian)
    (c : ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) M ≤ c • Matrix.toEuclideanCLM (𝕜 := ℂ) N
      ↔ ∀ x : κ → ℂ, (matQuadForm M x).re ≤ c * (matQuadForm N x).re := by
  have hsmul : c • Matrix.toEuclideanCLM (𝕜 := ℂ) N
      = Matrix.toEuclideanCLM (𝕜 := ℂ) ((c : ℂ) • N) := by
    rw [map_smul, coe_smul_clm]
  rw [hsmul, toEuclideanCLM_le_iff hM (isHermitian_smul_real c hN)]
  constructor
  · intro h x
    rw [← matQuadForm_smul]
    exact h x
  · intro h x
    rw [matQuadForm_smul]
    exact h x


/-! ## The contraction, specialised to operators on a Euclidean space -/

/-- The homothety contraction of the operator order, in the algebra of operators on a Euclidean
space. -/
theorem exp_smul_le_of_exp_le_clm
    {x y : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) {c : ℝ} (hc : 0 < c)
    (h : NormedSpace.exp y ≤ c • NormedSpace.exp x) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    NormedSpace.exp (s • y) ≤ (c ^ s) • NormedSpace.exp (s • x) :=
  exp_smul_le_of_exp_le hx hy hc h hs0 hs1

end GaloisForLFunctions.HTGeometry
