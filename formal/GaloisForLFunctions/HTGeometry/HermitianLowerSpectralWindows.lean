import GaloisForLFunctions.HTGeometry.HermitianSpectralWindowBounds

/-!
# Lower spectral windows of a Hermitian matrix

Parseval and finite-dimensional rank control the multiplicity of a lower
spectral window from detecting trial coordinates. An upper trial energy has
small overlap with that window whenever its actual residual is small.
-/

noncomputable section

open Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℝ}

private theorem apply_eigenbasis (hA : A.IsHermitian) (i : I) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  ext j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

private theorem inner_apply_eigenbasis (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ I) (i : I) :
    ⟪Matrix.toEuclideanLin A x, hA.eigenvectorBasis i⟫ =
      hA.eigenvalues i * ⟪x, hA.eigenvectorBasis i⟫ := by
  rw [(Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) x (hA.eigenvectorBasis i),
    apply_eigenbasis, real_inner_smul_right]

/-- A Hermitian quadratic form is the eigenvalue-weighted coordinate sum. -/
theorem hermitianEnergy_eq_sum (hA : A.IsHermitian) (x : EuclideanSpace ℝ I) :
    ⟪Matrix.toEuclideanLin A x, x⟫ =
      ∑ i, hA.eigenvalues i * ⟪x, hA.eigenvectorBasis i⟫ ^ 2 := by
  have h := shiftedHermitianEnergy_eq_sum hA 0 x
  simpa only [zero_mul, zero_sub, neg_mul, sum_neg_distrib, neg_inj] using h

/-- A vector supported below a spectral threshold has the corresponding
quadratic-form upper bound. -/
theorem hermitianEnergy_le_of_support (hA : A.IsHermitian) (T : ℝ)
    (x : EuclideanSpace ℝ I)
    (hlo : ∀ i, T ≤ hA.eigenvalues i → ⟪x, hA.eigenvectorBasis i⟫ = 0) :
    ⟪Matrix.toEuclideanLin A x, x⟫ ≤ T * ‖x‖ ^ 2 := by
  rw [hermitianEnergy_eq_sum, ← hA.eigenvectorBasis.sum_sq_inner_left x, mul_sum]
  refine sum_le_sum fun i _ => ?_
  by_cases hi : hA.eigenvalues i < T
  · exact mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)
  · rw [hlo i (le_of_not_gt hi), zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, mul_zero]

/-- A trial vector above a low spectral window has small overlap with every
unit vector in that window, bounded by its actual residual and the energy gap. -/
theorem inner_sq_le_residual_sq_div_upper_gap_sq (hA : A.IsHermitian) (T E : ℝ)
    (hTE : T < E) (x v : EuclideanSpace ℝ I) (hx : ‖x‖ = 1)
    (hlo : ∀ i, T ≤ hA.eigenvalues i → ⟪x, hA.eigenvectorBasis i⟫ = 0) :
    ⟪x, v⟫ ^ 2 ≤ ‖Matrix.toEuclideanLin A v - E • v‖ ^ 2 / (E - T) ^ 2 := by
  let g : I → ℝ := fun i =>
    if hA.eigenvalues i < T then ⟪hA.eigenvectorBasis i, v⟫ else 0
  have hinner : (∑ i, ⟪x, hA.eigenvectorBasis i⟫ * g i) = ⟪x, v⟫ := by
    rw [← hA.eigenvectorBasis.sum_inner_mul_inner x v]
    refine sum_congr rfl fun i _ => ?_
    dsimp only [g]
    by_cases hi : hA.eigenvalues i < T
    · rw [if_pos hi]
    · rw [if_neg hi, hlo i (le_of_not_gt hi), zero_mul, zero_mul]
  have hcs := sum_mul_sq_le_sq_mul_sq univ
    (fun i => ⟪x, hA.eigenvectorBasis i⟫) g
  rw [hinner, hA.eigenvectorBasis.sum_sq_inner_left x, hx, one_pow, one_mul] at hcs
  have hres (i : I) :
      ⟪Matrix.toEuclideanLin A v - E • v, hA.eigenvectorBasis i⟫ =
        (hA.eigenvalues i - E) * ⟪hA.eigenvectorBasis i, v⟫ := by
    simp only [inner_sub_left, inner_apply_eigenbasis, real_inner_smul_left,
      real_inner_comm v (hA.eigenvectorBasis i)]
    ring
  have hsum : (E - T) ^ 2 * (∑ i, g i ^ 2) ≤
      ‖Matrix.toEuclideanLin A v - E • v‖ ^ 2 := by
    rw [mul_sum, ← hA.eigenvectorBasis.sum_sq_inner_left
      (Matrix.toEuclideanLin A v - E • v)]
    refine sum_le_sum fun i _ => ?_
    rw [hres, mul_pow]
    dsimp only [g]
    by_cases hi : hA.eigenvalues i < T
    · rw [if_pos hi]
      have hgap : E - T ≤ E - hA.eigenvalues i := by linarith only [hi]
      have hsq : (E - T) ^ 2 ≤ (hA.eigenvalues i - E) ^ 2 := by
        have h := mul_self_le_mul_self (sub_pos.mpr hTE).le hgap
        nlinarith only [h]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    · rw [if_neg hi, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hTE))]
  calc ⟪x, v⟫ ^ 2 * (E - T) ^ 2 ≤ (∑ i, g i ^ 2) * (E - T) ^ 2 :=
      mul_le_mul_of_nonneg_right hcs (sq_nonneg _)
    _ ≤ _ := by simpa only [mul_comm] using hsum

/-- If finitely many trial coordinates detect every nonzero vector in a low
spectral window, that window has at most as many eigenvalues, with multiplicity. -/
theorem lowerSpectralWindow_card_le_of_coordinates
    {K : Type*} [Fintype K] (hA : A.IsHermitian) (T : ℝ)
    (w : K → EuclideanSpace ℝ I)
    (hdetect : ∀ x : EuclideanSpace ℝ I, ‖x‖ = 1 →
      (∀ i, T ≤ hA.eigenvalues i → ⟪x, hA.eigenvectorBasis i⟫ = 0) →
        ∃ k, ⟪x, w k⟫ ≠ 0) :
    (univ.filter (fun i => hA.eigenvalues i < T)).card ≤ Fintype.card K := by
  classical
  let J := univ.filter (fun i => hA.eigenvalues i < T)
  let b := hA.eigenvectorBasis
  have hb (i j : I) : ⟪b i, b j⟫ = if i = j then 1 else 0 :=
    (orthonormal_iff_ite.mp b.orthonormal) i j
  let syn : (J → ℝ) →ₗ[ℝ] EuclideanSpace ℝ I :=
    { toFun := fun a => ∑ j : J, a j • b j
      map_add' := by
        intro a d
        simp only [Pi.add_apply, add_smul, sum_add_distrib]
      map_smul' := by
        intro r a
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum, RingHom.id_apply] }
  have hcoeff (a : J → ℝ) (j : J) : ⟪syn a, b j⟫ = a j := by
    change ⟪∑ i : J, a i • b i, b j⟫ = _
    simp only [sum_inner, real_inner_smul_left, hb, Subtype.val_injective.eq_iff,
      mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  have hsupport (a : J → ℝ) : ∀ i, T ≤ hA.eigenvalues i → ⟪syn a, b i⟫ = 0 := by
    intro i hi
    change ⟪∑ j : J, a j • b j, b i⟫ = 0
    rw [sum_inner]
    refine sum_eq_zero fun j _ => ?_
    have hji : (j : I) ≠ i := by
      intro h
      have hj := (mem_filter.mp j.property).2
      rw [h] at hj
      exact (not_lt_of_ge hi) hj
    rw [real_inner_smul_left, hb, if_neg hji, mul_zero]
  let L : (J → ℝ) →ₗ[ℝ] (K → ℝ) :=
    { toFun := fun a k => ⟪syn a, w k⟫
      map_add' := by
        intro a d
        funext k
        simp only [map_add, inner_add_left, Pi.add_apply]
      map_smul' := by
        intro r a
        funext k
        simp only [map_smul, real_inner_smul_left, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply] }
  have hker (a : J → ℝ) (ha : L a = 0) : a = 0 := by
    have hx : syn a = 0 := by
      by_contra hx
      have hn : 0 < ‖syn a‖ := norm_pos_iff.mpr hx
      let y := ‖syn a‖⁻¹ • syn a
      have hy : ‖y‖ = 1 := by
        simp only [y, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn.ne']
      have hylow : ∀ i, T ≤ hA.eigenvalues i → ⟪y, b i⟫ = 0 := by
        intro i hi
        dsimp only [y]
        rw [real_inner_smul_left, hsupport a i hi, mul_zero]
      obtain ⟨k, hk⟩ := hdetect y hy hylow
      have hak : ⟪syn a, w k⟫ = 0 := congrFun ha k
      apply hk
      dsimp only [y]
      rw [real_inner_smul_left, hak, mul_zero]
    funext j
    have hj := hcoeff a j
    rw [hx, inner_zero_left] at hj
    exact hj.symm
  have hinj : Function.Injective L := by
    intro a d had
    have hzero : L (a - d) = 0 := by rw [map_sub, had, sub_self]
    exact sub_eq_zero.mp (hker (a - d) hzero)
  have hdim := L.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hdim

end GaloisForLFunctions.HTGeometry
