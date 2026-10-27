import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceCutoffControl
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian

/-!
# Differential control of holomorphic source squares

The squared modulus of a holomorphic transform has Laplacian four times the
squared modulus of its derivative. Combining this identity with the cutoff
product rule controls current errors using only first holomorphic derivatives.
-/

open Complex Set Metric Laplacian InnerProductSpace
open scoped Laplacian
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry

private theorem contDiff_normSq : ContDiff ℝ 2 Complex.normSq := by
  have he : (Complex.normSq : ℂ → ℝ) = fun z : ℂ => z.re ^ 2 + z.im ^ 2 := by
    funext z
    rw [Complex.normSq_apply]
    ring
  rw [he]
  exact (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)

/-- The planar energy density of a holomorphic source transform. -/
theorem laplacian_normSq_holomorphic (g : ℂ → ℂ) (hg : Differentiable ℂ g) (z : ℂ) :
    Δ (fun w => Complex.normSq (g w)) z = 4 * Complex.normSq (deriv g z) := by
  have hbase (w : ℂ) : Δ (Complex.normSq : ℂ → ℝ) w = 4 := by
    have he : (Complex.normSq : ℂ → ℝ) = fun z : ℂ => ‖z‖ ^ 2 :=
      funext Complex.normSq_eq_norm_sq
    rw [he, InnerProductSpace.laplacian_norm_sq]
    norm_num
  have h := laplacian_real_holomorphic_comp Complex.normSq g contDiff_normSq hg z
  have he : (Complex.normSq : ℂ → ℝ) ∘ g =
      (fun w => Complex.normSq (g w)) := rfl
  rw [he, hbase] at h
  simpa only [mul_comm] using h

/-- First real derivatives of a holomorphic square need only its first complex derivative. -/
theorem abs_fderiv_normSq_holomorphic_le (g : ℂ → ℂ)
    (hg : Differentiable ℂ g) (z v : ℂ) :
    |fderiv ℝ (fun w => Complex.normSq (g w)) z v| ≤
      2 * ‖g z‖ * ‖deriv g z‖ * ‖v‖ := by
  have he : (fun w => Complex.normSq (g w)) = fun w => ‖g w‖ ^ 2 := by
    funext w
    exact Complex.normSq_eq_norm_sq _
  have hd := ((hg z).restrictScalars ℝ).hasFDerivAt.norm_sq
  rw [he, hd.fderiv]
  simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ← two_mul]
  rw [(hg z).fderiv_restrictScalars ℝ]
  change |2 * inner ℝ (g z) (fderiv ℂ g z v)| ≤ _
  rw [fderiv_eq_deriv_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |inner ℝ (g z) (deriv g z * v)| ≤
        2 * (‖g z‖ * ‖deriv g z * v‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
    _ = _ := by rw [norm_mul]; ring

private theorem source_second_mul (u φ : ℂ → ℝ)
    (hu : ContDiff ℝ 2 u) (hp : ContDiff ℝ 2 φ) (v z : ℂ) :
    Bottcher.dderiv (fun w => u w * φ w) v z =
      u z * Bottcher.dderiv φ v z + φ z * Bottcher.dderiv u v z +
        2 * fderiv ℝ u z v * fderiv ℝ φ z v := by
  have he : (fun w => fderiv ℝ (fun x => u x * φ x) w v) =
      fun w => u w * fderiv ℝ φ w v + φ w * fderiv ℝ u w v := by
    funext w
    rw [fderiv_fun_mul (hu.differentiable (by norm_num) w)
      (hp.differentiable (by norm_num) w)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hdu : DifferentiableAt ℝ (fun w => fderiv ℝ u w v) z :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num) z
  have hdp : DifferentiableAt ℝ (fun w => fderiv ℝ φ w v) z :=
    ((hp.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num) z
  have hu' := hu.differentiable (by norm_num) z
  have hp' := hp.differentiable (by norm_num) z
  rw [Bottcher.dderiv, he, fderiv_fun_add (hu'.fun_mul hdp) (hp'.fun_mul hdu),
    fderiv_fun_mul hu' hdp, fderiv_fun_mul hp' hdu]
  simp only [add_apply, smul_apply, smul_eq_mul, Bottcher.dderiv]
  ring

/-- Product Laplacian in the two real spectral directions. -/
theorem source_laplacian_mul (u φ : ℂ → ℝ)
    (hu : ContDiff ℝ 2 u) (hp : ContDiff ℝ 2 φ) (z : ℂ) :
    Δ (fun w => u w * φ w) z =
      u z * Δ φ z + φ z * Δ u z +
        2 * fderiv ℝ u z 1 * fderiv ℝ φ z 1 +
        2 * fderiv ℝ u z Complex.I * fderiv ℝ φ z Complex.I := by
  rw [Bottcher.laplacian_eq_dderiv _ (hu.mul hp), source_second_mul u φ hu hp,
    source_second_mul u φ hu hp, Bottcher.laplacian_eq_dderiv _ hu,
    Bottcher.laplacian_eq_dderiv _ hp]
  ring

/-- A cutoff source square is controlled by the value and first derivative on its source disc. -/
theorem abs_laplacian_cutoff_normSq_le (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (n : ℕ) (z : ℂ) {B : ℝ} (hb : ‖g z‖ ≤ B) (hdb : ‖deriv g z‖ ≤ B) :
    |Δ (fun w => sourceCutoff n w * Complex.normSq (g w)) z| ≤
      4 * sourceCutoffControl n * B ^ 2 := by
  let φ : ℂ → ℝ := fun w => Complex.normSq (g w)
  have hp : ContDiff ℝ 2 φ := contDiff_normSq.comp (hg.contDiff.restrict_scalars ℝ)
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  have hv : |φ z| ≤ B ^ 2 := by
    dsimp only [φ]
    rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
    gcongr
  have hΔ : |Δ φ z| ≤ 4 * B ^ 2 := by
    dsimp only [φ]
    rw [laplacian_normSq_holomorphic g hg,
      abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Complex.normSq_nonneg _)),
      Complex.normSq_eq_norm_sq]
    gcongr
  have hd (v : ℂ) (hn : ‖v‖ = 1) : |fderiv ℝ φ z v| ≤ 2 * B ^ 2 := by
    have h := abs_fderiv_normSq_holomorphic_le g hg z v
    rw [hn, mul_one] at h
    calc
      |fderiv ℝ φ z v| ≤ 2 * ‖g z‖ * ‖deriv g z‖ := h
      _ ≤ 2 * B * B := by gcongr
      _ = _ := by ring
  have ha : |sourceCutoff n z * Δ φ z| ≤ 4 * B ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sourceCutoff n).nonneg]
    exact (mul_le_mul (sourceCutoff n).le_one hΔ (abs_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  have hb' : |φ z * Δ (sourceCutoff n : ℂ → ℝ) z| ≤ B ^ 2 * ‖sourceCutoffLaplacian n‖ := by
    rw [abs_mul]
    exact mul_le_mul hv (abs_sourceCutoffLaplacian_le n z) (abs_nonneg _) (sq_nonneg B)
  have hc (v : ℂ) (hn : ‖v‖ = 1) :
      |2 * fderiv ℝ (sourceCutoff n) z v * fderiv ℝ φ z v| ≤
        4 * B ^ 2 * ‖sourceCutoffDerivative n v‖ := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      2 * |fderiv ℝ (sourceCutoff n) z v| * |fderiv ℝ φ z v| ≤
          (2 * ‖sourceCutoffDerivative n v‖) * (2 * B ^ 2) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (abs_sourceCutoffDerivative_le n v z) (by norm_num)
        · exact hd v hn
        · exact abs_nonneg _
        · positivity
      _ = _ := by ring
  have hc1 := hc 1 norm_one
  have hcI := hc Complex.I Complex.norm_I
  rw [source_laplacian_mul _ φ (sourceCutoff n).contDiff hp]
  have ht1 := abs_add_le (sourceCutoff n z * Δ φ z) (φ z * Δ (sourceCutoff n : ℂ → ℝ) z)
  have ht2 := abs_add_le (sourceCutoff n z * Δ φ z + φ z * Δ (sourceCutoff n : ℂ → ℝ) z)
    (2 * fderiv ℝ (sourceCutoff n) z 1 * fderiv ℝ φ z 1)
  have ht3 := abs_add_le
    (sourceCutoff n z * Δ φ z + φ z * Δ (sourceCutoff n : ℂ → ℝ) z +
      2 * fderiv ℝ (sourceCutoff n) z 1 * fderiv ℝ φ z 1)
    (2 * fderiv ℝ (sourceCutoff n) z Complex.I * fderiv ℝ φ z Complex.I)
  have hnon := mul_nonneg (sq_nonneg B) (norm_nonneg (sourceCutoffLaplacian n))
  unfold sourceCutoffControl
  nlinarith only [ha, hb', hc1, hcI, ht1, ht2, ht3, hnon]

end GaloisForLFunctions.ConjugateDiagonalGeometry
