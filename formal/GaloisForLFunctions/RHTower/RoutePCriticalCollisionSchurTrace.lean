import GaloisForLFunctions.RHTower.RoutePCriticalCollisionScaleKernel
import GaloisForLFunctions.HTGeometry.FisherOneCornerCoareaTransform
import Mathlib.Analysis.Matrix.Order

/-!
# Route P: collision kernel as a positive Schur-cube compression

P-G172 found the exact non-diagonal kernel that survives when ordinate gaps close at the critical
clock scale.  This module identifies its hidden universal structure.  Double every radial node by
adjoining its aperture-dilated partner, take the third Hadamard power of the Hardy Cauchy Gram, and
compress by the signed first difference between the two scales.  The resulting matrix is exactly
the P-G172 collision kernel.

Schur positivity and compression therefore prove unconditional positive semidefiniteness for
arbitrary collision frequencies, including repeated frequencies.  No zero-spacing hypothesis is
needed.  Its diagonal is the exact scale-free mass `115 / (864 a^3)`, independent of boundary
clock `R` and collision ordinate.  Thus mesoscopic clustering is not a positivity obstruction:
the remaining height-local problem is purely a trace/source-mass problem weighted by `a^{-3}`.
-/

open Complex Matrix MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Two Hardy nodes per collision column: original and doubled radial aperture. -/
def routePCollisionDoubledNode {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) : Fin N ⊕ Fin N → ℂ :=
  Sum.elim
    (fun i => ((R * a i : ℝ) : ℂ) - (kappa i : ℂ) * I)
    (fun i => ((R * (2 * a i) : ℝ) : ℂ) - (kappa i : ℂ) * I)

/-- Cauchy Gram on the doubled collision packet. -/
def routePCollisionDoubledCauchyGram {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  fun x y => 1 /
    (routePCollisionDoubledNode R a kappa x +
      star (routePCollisionDoubledNode R a kappa y))

theorem routePCollisionDoubledNode_re_pos
    {N : ℕ} {R : ℝ} {a kappa : Fin N → ℝ}
    (hR : 0 < R) (ha : ∀ i, 0 < a i) :
    ∀ x, 0 < (routePCollisionDoubledNode R a kappa x).re := by
  intro x
  rcases x with i | i
  · simp only [routePCollisionDoubledNode, Sum.elim_inl, sub_re, ofReal_re,
      mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero]
    exact mul_pos hR (ha i)
  · simp only [routePCollisionDoubledNode, Sum.elim_inr, sub_re, ofReal_re,
      mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero]
    exact mul_pos hR (mul_pos (by norm_num) (ha i))

theorem routePCollisionDoubledCauchyGram_posSemidef
    {N : ℕ} {R : ℝ} {a kappa : Fin N → ℝ}
    (hR : 0 < R) (ha : ∀ i, 0 < a i) :
    (routePCollisionDoubledCauchyGram R a kappa).PosSemidef := by
  let hnode : ∀ x : Fin N ⊕ Fin N,
      0 < (routePCollisionDoubledNode R a kappa x).re :=
    routePCollisionDoubledNode_re_pos hR ha
  let v : (Fin N ⊕ Fin N) →
      Lp ℂ 2 GaloisForLFunctions.HTGeometry.halfLineLaplaceMeasure :=
    fun x => GaloisForLFunctions.HTGeometry.halfLineLaplaceFeature
      (routePCollisionDoubledNode R a kappa x) (hnode x)
  have hEq : routePCollisionDoubledCauchyGram R a kappa = Matrix.gram ℂ v := by
    ext x y
    rw [Matrix.gram_apply,
      GaloisForLFunctions.HTGeometry.inner_halfLineLaplaceFeature]
    rfl
  rw [hEq]
  exact Matrix.posSemidef_gram ℂ v

/-- Third Schur power of the doubled Hardy Cauchy Gram, with residue normalization. -/
def routePCollisionDoubledCubicGram {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  let G := routePCollisionDoubledCauchyGram R a kappa
  (((2 * R ^ 3 : ℝ) : ℂ)) • ((G ⊙ G) ⊙ G)

theorem routePCollisionDoubledCubicGram_posSemidef
    {N : ℕ} {R : ℝ} {a kappa : Fin N → ℝ}
    (hR : 0 < R) (ha : ∀ i, 0 < a i) :
    (routePCollisionDoubledCubicGram R a kappa).PosSemidef := by
  let G := routePCollisionDoubledCauchyGram R a kappa
  have hG : G.PosSemidef := routePCollisionDoubledCauchyGram_posSemidef hR ha
  exact ((hG.hadamard hG).hadamard hG).smul (by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) (pow_pos hR 3)).le)

theorem routePCollisionDoubledCubicGram_apply
    {N : ℕ} (R : ℝ) (a kappa : Fin N → ℝ) (x y : Fin N ⊕ Fin N) :
    routePCollisionDoubledCubicGram R a kappa x y =
      2 * (R : ℂ) ^ 3 /
        (routePCollisionDoubledNode R a kappa x +
          star (routePCollisionDoubledNode R a kappa y)) ^ 3 := by
  simp only [routePCollisionDoubledCubicGram, Matrix.smul_apply, smul_eq_mul,
    Matrix.hadamard_apply, routePCollisionDoubledCauchyGram]
  push_cast
  simp only [div_eq_mul_inv]
  rw [← inv_pow]
  ring

/-- Signed first-difference compression from doubled scales to collision columns. -/
def routePCollisionDifferenceMatrix {N : ℕ} :
    Matrix (Fin N) (Fin N ⊕ Fin N) ℂ :=
  fun i x => Sum.elim
    (fun j => if i = j then 1 else 0)
    (fun j => if i = j then -1 else 0) x

/-- Collision kernel matrix on a finite moving-ordinate packet. -/
def routePCollisionCubicKernelMatrix {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => routePCollisionCubicKernel R (a i) (a j) (kappa j - kappa i)

theorem routePCollisionDoubledNode_pair_ll {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) (i j : Fin N) :
    routePCollisionDoubledNode R a kappa (Sum.inl i) +
        star (routePCollisionDoubledNode R a kappa (Sum.inl j)) =
      routePCollisionPairFrequency R (a i) (a j) (kappa j - kappa i) := by
  simp only [routePCollisionDoubledNode, Sum.elim_inl, map_sub, map_mul,
    RCLike.star_def, Complex.conj_ofReal, Complex.conj_I,
    routePCollisionPairFrequency]
  push_cast
  ring

theorem routePCollisionDoubledNode_pair_lr {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) (i j : Fin N) :
    routePCollisionDoubledNode R a kappa (Sum.inl i) +
        star (routePCollisionDoubledNode R a kappa (Sum.inr j)) =
      routePCollisionPairFrequency R (a i) (2 * a j) (kappa j - kappa i) := by
  simp only [routePCollisionDoubledNode, Sum.elim_inl, Sum.elim_inr, map_sub, map_mul,
    RCLike.star_def, Complex.conj_ofReal, Complex.conj_I,
    routePCollisionPairFrequency]
  push_cast
  ring

theorem routePCollisionDoubledNode_pair_rl {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) (i j : Fin N) :
    routePCollisionDoubledNode R a kappa (Sum.inr i) +
        star (routePCollisionDoubledNode R a kappa (Sum.inl j)) =
      routePCollisionPairFrequency R (2 * a i) (a j) (kappa j - kappa i) := by
  simp only [routePCollisionDoubledNode, Sum.elim_inl, Sum.elim_inr, map_sub, map_mul,
    RCLike.star_def, Complex.conj_ofReal, Complex.conj_I,
    routePCollisionPairFrequency]
  push_cast
  ring

theorem routePCollisionDoubledNode_pair_rr {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) (i j : Fin N) :
    routePCollisionDoubledNode R a kappa (Sum.inr i) +
        star (routePCollisionDoubledNode R a kappa (Sum.inr j)) =
      routePCollisionPairFrequency R (2 * a i) (2 * a j) (kappa j - kappa i) := by
  simp only [routePCollisionDoubledNode, Sum.elim_inr, map_sub, map_mul,
    RCLike.star_def, Complex.conj_ofReal, Complex.conj_I,
    routePCollisionPairFrequency]
  push_cast
  ring

/-- Exact Schur-cube compression formula for the collision kernel. -/
theorem routePCollisionCubicKernelMatrix_eq_compression {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) :
    routePCollisionCubicKernelMatrix R a kappa =
      routePCollisionDifferenceMatrix (N := N) *
        routePCollisionDoubledCubicGram R a kappa *
          (routePCollisionDifferenceMatrix (N := N))ᴴ := by
  ext i j
  change routePCollisionCubicKernel R (a i) (a j) (kappa j - kappa i) = _
  have hstar (x : Fin N) :
      (starRingEnd ℂ) (if j = x then (-1 : ℂ) else 0) =
        if j = x then -1 else 0 := by
    by_cases h : j = x <;> simp [h]
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    routePCollisionDifferenceMatrix, hstar]
  rw [routePCollisionDoubledCubicGram_apply,
    routePCollisionDoubledCubicGram_apply,
    routePCollisionDoubledCubicGram_apply,
    routePCollisionDoubledCubicGram_apply,
    routePCollisionDoubledNode_pair_ll,
    routePCollisionDoubledNode_pair_lr,
    routePCollisionDoubledNode_pair_rl,
    routePCollisionDoubledNode_pair_rr]
  unfold routePCollisionCubicKernel
  ring

/-- Every finite mesoscopic collision kernel is positive semidefinite, with no gap hypothesis. -/
theorem routePCollisionCubicKernelMatrix_posSemidef
    {N : ℕ} {R : ℝ} {a kappa : Fin N → ℝ}
    (hR : 0 < R) (ha : ∀ i, 0 < a i) :
    (routePCollisionCubicKernelMatrix R a kappa).PosSemidef := by
  rw [routePCollisionCubicKernelMatrix_eq_compression]
  exact (routePCollisionDoubledCubicGram_posSemidef hR ha).mul_mul_conjTranspose_same
    (routePCollisionDifferenceMatrix (N := N))

/-- Exact diagonal mass: collision frequency and boundary clock disappear. -/
theorem routePCollisionCubicKernel_diagonal
    {R a : ℝ} (hR : 0 < R) (ha : 0 < a) :
    routePCollisionCubicKernel R a a 0 =
      (((115 : ℝ) / (864 * a ^ 3) : ℝ) : ℂ) := by
  simp only [routePCollisionCubicKernel, routePCollisionPairFrequency]
  push_cast
  field_simp [hR.ne', ha.ne']
  ring

/-- Exact spacing-free trace law for every finite collision packet. -/
theorem trace_routePCollisionCubicKernelMatrix
    {N : ℕ} {R : ℝ} {a kappa : Fin N → ℝ}
    (hR : 0 < R) (ha : ∀ i, 0 < a i) :
    (routePCollisionCubicKernelMatrix R a kappa).trace =
      ∑ i : Fin N, (((115 : ℝ) / (864 * (a i) ^ 3) : ℝ) : ℂ) := by
  apply Finset.sum_congr rfl
  intro i hi
  change routePCollisionCubicKernel R (a i) (a i) (kappa i - kappa i) = _
  rw [sub_self]
  exact routePCollisionCubicKernel_diagonal hR (ha i)

theorem routePCollisionCubicKernelMatrix_quadratic_nonneg
    {N : ℕ} {R : ℝ} {a kappa : Fin N → ℝ}
    (hR : 0 < R) (ha : ∀ i, 0 < a i) (c : Fin N → ℂ) :
    0 ≤ star c ⬝ᵥ (routePCollisionCubicKernelMatrix R a kappa).mulVec c :=
  (routePCollisionCubicKernelMatrix_posSemidef hR ha).dotProduct_mulVec_nonneg c

/-- The exact finite collision-packet limit from P-G172 is nonnegative. -/
theorem routePFiniteCollisionCubicLimit_nonneg
    {N : ℕ} {R : ℝ} {a kappa : Fin N → ℝ}
    (hR : 0 < R) (ha : ∀ i, 0 < a i) (c : Fin N → ℂ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      (c j * star (c i)) *
        routePCollisionCubicKernel R (a i) (a j) (kappa j - kappa i) := by
  have h := routePCollisionCubicKernelMatrix_quadratic_nonneg
    (kappa := kappa) hR ha c
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (c j * star (c i)) *
      routePCollisionCubicKernel R (a i) (a j) (kappa j - kappa i) =
    star (c i) *
      (routePCollisionCubicKernel R (a i) (a j) (kappa j - kappa i) * c j)
  ring

end

end RHTower
