import GaloisForLFunctions.HTGeometry.GeometricDecayFredholmDeterminant

/-!
# The complementary Fredholm determinant of a rank-one constant mode

A triangular shear straightens the evaluation row of a projection. Finite
row multilinearity then identifies its determinant coefficient with the
complementary block, without an inverse assumption. Uniform geometric decay
passes this exact identity to the Fredholm limit.
-/

open Complex Matrix Finset Filter Topology
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCompression

/-- A finite triangular shear sends the evaluation row to its constant coordinate. -/
def shear {n : ℕ} (q : Fin (n+1) → ℂ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => if i = 0 then (if j = 0 then 1 else -q j) else (if i = j then 1 else 0)

private theorem shear_lower {n : ℕ} (q : Fin (n+1) → ℂ) :
    (shear q).submatrix Fin.succ Fin.succ = 1 := by
  ext i j
  simp only [Matrix.submatrix_apply, shear, Fin.succ_ne_zero, if_false,
    Fin.succ_inj, Matrix.one_apply]

theorem det_shear {n : ℕ} (q : Fin (n+1) → ℂ) : (shear q).det = 1 := by
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, shear, if_true, one_mul, Fin.succAbove_zero]
    rw [shear_lower, Matrix.det_one]
  · intro i hi hi0
    simp [shear,hi0]
  · intro hi
    exact absurd (Finset.mem_univ 0) hi

private theorem mul_shear_zero {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (q : Fin (n+1) → ℂ) (i : Fin (n+1)) : (B*shear q) i 0 = B i 0 := by
  simp [Matrix.mul_apply, shear, Fin.sum_univ_succ]

private theorem mul_shear_succ {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (q : Fin (n+1) → ℂ) (i : Fin (n+1)) (j : Fin n) :
    (B*shear q) i j.succ = B i j.succ-B i 0*q j.succ := by
  simp [Matrix.mul_apply, shear, Fin.sum_univ_succ, mul_ite]
  ring

/-- Finite complementary block in the coordinates with the constant mode removed. -/
def lowerBlock {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (q : Fin (n+1) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => M i.succ j.succ-M i.succ 0*q j.succ

/-- Replacing the constant row by evaluation leaves precisely the complementary block. -/
theorem det_evaluation_row {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (q : Fin (n+1) → ℂ) (hq : q 0 = 1) (lam : ℂ) :
    ((1-lam • M).updateRow 0 q).det =
      (1-lam • lowerBlock M q).det := by
  let B := (1-lam • M).updateRow 0 q
  have hrow (j : Fin (n+1)) : (B*shear q) 0 j = if j = 0 then 1 else 0 := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [mul_shear_zero]
      simpa only [B, Matrix.updateRow_self, if_true] using hq
    · rw [mul_shear_succ]
      simp only [B, Matrix.updateRow_self, hq, one_mul, sub_self,
        Fin.succ_ne_zero, if_false]
  have hlower : (B*shear q).submatrix Fin.succ Fin.succ =
      1-lam • lowerBlock M q := by
    ext i j
    rw [Matrix.submatrix_apply, mul_shear_succ]
    simp only [B, Matrix.updateRow_ne (Fin.succ_ne_zero _), Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, lowerBlock, Matrix.of_apply, Fin.succ_inj,
      Fin.succ_ne_zero, if_false]
    ring
  have hdet : (B*shear q).det = B.det := by rw [Matrix.det_mul, det_shear, mul_one]
  change B.det = _
  rw [← hdet, Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · rw [hrow]
    simp only [Fin.val_zero, pow_zero, if_true, one_mul, Fin.succAbove_zero]
    rw [hlower]
  · intro j hj hj0
    rw [hrow, if_neg hj0, mul_zero, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ 0) hj

/-- Finite evaluation projection in the Cauchy coordinates. -/
def projection {n : ℕ} (q : Fin (n+1) → ℂ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => if i = 0 then q j else 0

/-- The constant-mode coefficient is exactly the determinant of the complementary block. -/
theorem determinant_projection_affine {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (q : Fin (n+1) → ℂ) (hq : q 0 = 1) (lam t : ℂ) :
    (1-lam • (M+t • projection q)).det = (1-lam • M).det - t*lam *
      (1-lam • lowerBlock M q).det := by
  let A := 1-lam • M
  have he : 1-lam • (M+t • projection q) =
      A.updateRow 0 (A 0+(-t*lam) • q) := by
    ext i j
    by_cases hi : i = 0
    · subst i
      rw [Matrix.updateRow_self]
      simp only [A, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, projection, if_true]
      ring
    · rw [Matrix.updateRow_ne hi]
      simp only [A, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, projection, if_neg hi, mul_zero, add_zero]
  rw [he, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul]
  change (1-lam • M).det + (-t*lam)*((1-lam • M).updateRow 0 q).det = _
  rw [det_evaluation_row M q hq lam]
  ring


open GeomFredholm

/-- The infinite evaluation projection occupies its constant row. -/
def rowProjection (q : ℕ → ℂ) (i j : ℕ) : ℂ := if i = 0 then q j else 0

/-- Matrix of the complementary block after straightening the evaluation functional. -/
def complement (M : ℕ → ℕ → ℂ) (q : ℕ → ℂ) (i j : ℕ) : ℂ :=
  M (i+1) (j+1)-M (i+1) 0*q (j+1)

theorem geomDecay_rowProjection {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1)
    {q : ℕ → ℂ} (hq : ∀ j, ‖q j‖ ≤ η^j) : GeomDecay (rowProjection q) 1 η := by
  refine ⟨zero_le_one,hη,hη1,fun i j => ?_⟩
  by_cases hi : i = 0
  · subst i
    simpa only [rowProjection, if_true, pow_zero, one_mul] using hq j
  · simp only [rowProjection, if_neg hi, norm_zero]
    positivity

theorem geomDecay_complement {M : ℕ → ℕ → ℂ} {C η : ℝ}
    (hM : GeomDecay M C η) {q : ℕ → ℂ} (hq : ∀ j, ‖q j‖ ≤ η^j) :
    GeomDecay (complement M q) (2*C*η^2) η := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  refine ⟨by positivity,hη,hM.rate_lt_one,fun i j => ?_⟩
  calc
    ‖complement M q i j‖ ≤ ‖M (i+1) (j+1)‖+‖M (i+1) 0*q (j+1)‖ := norm_sub_le _ _
    _ = ‖M (i+1) (j+1)‖+‖M (i+1) 0‖*‖q (j+1)‖ := by rw [norm_mul]
    _ ≤ C*η^(i+1)*η^(j+1)+(C*η^(i+1)*η^0)*η^(j+1) :=
      add_le_add (hM.bound _ _) (mul_le_mul (hM.bound _ _) (hq _)
        (norm_nonneg _) (by positivity))
    _ = _ := by rw [pow_succ,pow_succ,pow_zero]; ring

theorem geomDecay_add_projection {M : ℕ → ℕ → ℂ} {C η : ℝ}
    (hM : GeomDecay M C η) {q : ℕ → ℂ} (hq : ∀ j, ‖q j‖ ≤ η^j) (t : ℂ) :
    GeomDecay (fun i j => M i j+t*rowProjection q i j) (C+‖t‖) η := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  have hP := geomDecay_rowProjection hη hM.rate_lt_one hq
  refine ⟨by positivity,hη,hM.rate_lt_one,fun i j => ?_⟩
  calc
    _ ≤ ‖M i j‖+‖t*rowProjection q i j‖ := norm_add_le _ _
    _ = ‖M i j‖+‖t‖*‖rowProjection q i j‖ := by rw [norm_mul]
    _ ≤ C*η^i*η^j+‖t‖*(1*η^i*η^j) :=
      add_le_add (hM.bound i j) (mul_le_mul_of_nonneg_left (hP.bound i j) (norm_nonneg t))
    _ = _ := by ring

/-- Each finite section has the same complementary determinant coefficient. -/
theorem truncDet_projection_affine (M : ℕ → ℕ → ℂ) (q : ℕ → ℂ) (hq : q 0 = 1)
    (lam t : ℂ) (n : ℕ) :
    truncDet (fun i j => M i j+t*rowProjection q i j) lam (n+1) =
      truncDet M lam (n+1)-t*lam*truncDet (complement M q) lam n := by
  have hP : trunc (rowProjection q) (n+1) = projection (fun i : Fin (n+1) => q i) := by
    ext i j
    simp only [trunc, Matrix.of_apply, rowProjection, projection, Fin.ext_iff, Fin.val_zero]
  have he : trunc (fun i j => M i j+t*rowProjection q i j) (n+1) =
      trunc M (n+1)+t • trunc (rowProjection q) (n+1) := rfl
  unfold truncDet
  rw [he,hP]
  exact determinant_projection_affine (trunc M (n+1)) (fun i => q i) hq lam t

/-- The coefficient of the constant mode is the genuine complementary Fredholm determinant. -/
theorem fdet_projection_affine {M : ℕ → ℕ → ℂ} {C η : ℝ}
    (hM : GeomDecay M C η) {q : ℕ → ℂ} (hq0 : q 0 = 1)
    (hq : ∀ j, ‖q j‖ ≤ η^j) (lam t : ℂ) :
    fdet (fun i j => M i j+t*rowProjection q i j) lam =
      fdet M lam-t*lam*fdet (complement M q) lam := by
  have hn : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hl := (tendsto_truncDet (geomDecay_add_projection hM hq t) lam).comp hn
  have hr := ((tendsto_truncDet hM lam).comp hn).sub
    ((tendsto_truncDet (geomDecay_complement hM hq) lam).const_mul (t*lam))
  have he : (fun n => truncDet (fun i j => M i j+t*rowProjection q i j) lam (n+1)) =
      fun n => truncDet M lam (n+1)-t*lam*truncDet (complement M q) lam n :=
    funext (truncDet_projection_affine M q hq0 lam t)
  change Tendsto (fun n => truncDet (fun i j => M i j+t*rowProjection q i j) lam (n+1))
    atTop _ at hl
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

#print axioms det_shear
#print axioms det_evaluation_row
#print axioms determinant_projection_affine
#print axioms geomDecay_complement
#print axioms fdet_projection_affine

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCompression
