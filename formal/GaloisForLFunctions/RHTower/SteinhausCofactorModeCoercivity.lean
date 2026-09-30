import GaloisForLFunctions.RHTower.SteinhausFinitePrimeCofactorModes
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant

/-!
# Robust quantitative Cauchy directions for cofactor blocks

For any coefficient vector, one prescribed Cauchy mode has a pairing bounded below by a
fixed positive multiple of the vector norm. Every row in a fixed neighborhood of that mode
retains a uniform lower bound. This lets an entire actual prime block contribute to the
conditional energy, rather than replacing the conditional matrix by its arithmetic mean.
-/

noncomputable section
open Finset Matrix
namespace RHTower

private theorem exists_matrix_row_norm_lower {J : ℕ} (hJ : 0 < J)
    (C : Matrix (Fin J) (Fin J) ℂ) (hC : C.det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Fin J → ℂ, ∃ i : Fin J,
      c * ‖u‖ ≤ ‖∑ j, C i j * u j‖ := by
  haveI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  let e := (Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin J)) C
    (isUnit_iff_ne_zero.mpr hC)).toContinuousLinearEquiv
  have heq : ∀ u : Fin J → ℂ, e u = C.mulVec u := by
    intro u
    simp only [e, LinearEquiv.coe_toContinuousLinearEquiv', Matrix.toLinearEquiv_apply,
      Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  let K : ℝ := ‖(e.symm : (Fin J → ℂ) →L[ℂ] (Fin J → ℂ))‖ + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hbound : ∀ u : Fin J → ℂ, ‖u‖ ≤ K * ‖C.mulVec u‖ := by
    intro u
    have h := (e.symm : (Fin J → ℂ) →L[ℂ] (Fin J → ℂ)).le_opNorm (e u)
    change ‖e.symm (e u)‖ ≤ _ at h
    rw [e.symm_apply_apply, heq] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (norm_nonneg _))
  refine ⟨1 / K, by positivity, ?_⟩
  intro u
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm (C.mulVec u)).1
  refine ⟨i, ?_⟩
  have h := hbound u
  rw [← hi] at h
  change (1 / K) * ‖u‖ ≤ ‖C.mulVec u i‖
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    ((div_le_iff₀ hK).mpr (by simpa only [mul_comm] using h))

private theorem norm_node_dot_le {J : ℕ} (a u : Fin J → ℂ) :
    ‖∑ j, a j * u j‖ ≤ J * ‖a‖ * ‖u‖ := by
  calc
    _ ≤ ∑ j, ‖a j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin J, ‖a‖ * ‖u‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm a j) (norm_le_pi_norm u j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

private theorem cauchyModeMatrix_det_ne_zero {J : ℕ} (s : Fin J → ℂ)
    (hs : ∀ j, 0 < (s j).re) (hinj : Function.Injective s) :
    (Matrix.of fun (i j : Fin J) => cofactorCauchyMode s (i.val : ℝ) j).det ≠ 0 := by
  let x : Fin J → ℂ := fun i => (i.val : ℂ) * Complex.I
  have hx : Function.Injective x := by
    intro i k h
    have hh := congrArg Complex.im h
    simp only [x, Complex.mul_im, Complex.natCast_re, Complex.I_im, mul_one,
      Complex.natCast_im, Complex.I_re, mul_zero, add_zero] at hh
    exact Fin.ext (by exact_mod_cast hh)
  have hnonzero : ∀ i j, x i + s j ≠ 0 := by
    intro i j h
    have hh := congrArg Complex.re h
    have hp := hs j
    simp [x] at hh
    linarith
  have heq : (Matrix.of fun (i j : Fin J) => cofactorCauchyMode s (i.val : ℝ) j) =
      GaloisForLFunctions.HTGeometry.cauchyMatrix x s := by
    ext i j
    simp [cofactorCauchyMode, GaloisForLFunctions.HTGeometry.cauchyMatrix, x, add_comm]
  rw [heq]
  intro h
  have hh := GaloisForLFunctions.HTGeometry.det_cauchyMatrix x s hnonzero
  rw [h, zero_mul] at hh
  have hp : (∏ i, ∏ j ∈ Ioi i, (x i - x j) * (s i - s j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    exact mul_ne_zero (sub_ne_zero.mpr (fun h => hij (hx h)))
      (sub_ne_zero.mpr (fun h => hij (hinj h)))
  exact hp hh.symm

/-- Some prescribed Cauchy direction controls every given node coefficient vector,
and every nearby row keeps the same quantitative control. -/
theorem exists_cofactorCauchyMode_robust_row_lower
    {J : ℕ} (hJ : 0 < J) (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hinj : Function.Injective s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ u : Fin J → ℂ, ∃ i : Fin J,
      ∀ v : Fin J → ℂ, ‖v - cofactorCauchyMode s (i.val : ℝ)‖ ≤ ε →
        c * ‖u‖ ≤ ‖∑ j, v j * u j‖ := by
  classical
  obtain ⟨a, ha, hrow⟩ := exists_matrix_row_norm_lower hJ
    (Matrix.of fun (i j : Fin J) => cofactorCauchyMode s (i.val : ℝ) j)
    (cauchyModeMatrix_det_ne_zero s hs hinj)
  let ε : ℝ := a / (2 * (J + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hJε : (J : ℝ) * ε ≤ a / 2 := by
    dsimp only [ε]
    have hden : 0 < (2 : ℝ) * (J + 1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    field_simp
    nlinarith
  refine ⟨ε, a / 2, hε, by positivity, ?_⟩
  intro u
  obtain ⟨i, hi⟩ := hrow u
  refine ⟨i, ?_⟩
  intro v hv
  have herr : ‖(∑ j, v j * u j) - ∑ j, cofactorCauchyMode s (i.val : ℝ) j * u j‖ ≤
      (a / 2) * ‖u‖ := by
    have heq : (∑ j, v j * u j) - ∑ j, cofactorCauchyMode s (i.val : ℝ) j * u j =
        ∑ j, (v - cofactorCauchyMode s (i.val : ℝ)) j * u j := by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [heq]
    exact (norm_node_dot_le _ _).trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg J)) (norm_nonneg u)).trans
        (mul_le_mul_of_nonneg_right hJε (norm_nonneg u)))
  have htriangle := norm_sub_le (∑ j, v j * u j)
    ((∑ j, v j * u j) - ∑ j, cofactorCauchyMode s (i.val : ℝ) j * u j)
  simp only [sub_sub_cancel] at htriangle
  simp only [Matrix.of_apply] at hi
  linarith

end RHTower
