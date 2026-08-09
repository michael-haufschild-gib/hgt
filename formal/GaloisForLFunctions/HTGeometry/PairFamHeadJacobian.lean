import GaloisForLFunctions.HTGeometry.PairFamOrbitScaling
import GaloisForLFunctions.HTGeometry.GenBellBorderedRows

/-!
# The head product's Jacobian is the peel's orbit determinant

The head product `jet m · H` is logarithmically linear, so its jets are the product times the affine
Bell values of its multiplier, and its Jacobian has the uniformly scaled shape.  Row reduction turns
the determinant into a power of the product times a bordered determinant; the border row is the
gradient of the product, which is the product times the peel's border row; and the Bell rows may be
replaced by the jet rows of the multiplier, which are the orbit of that same border row.

Nothing here sees the factors, so it is stated once for any factor family.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace PairFam

variable (F : PairFam)

/-- The Jacobian of the jets of the head product. -/
noncomputable def headJetJacobian (H : CascadeField) (m : ℕ) :
    Matrix (Fin m) (Fin m) CascadeField :=
  Matrix.of fun i j => fpderiv ((j : ℕ) + 1)
    (((F.law : CascadeField → CascadeField)^[(i : ℕ)]) (F.head H m))

/-- The gradient of the head product. -/
noncomputable def headGradient (H : CascadeField) (n : ℕ) : Fin (n + 1) → CascadeField :=
  fun j => fpderiv ((j : ℕ) + 1) (F.head H (n + 1))

/-- The gradients of the positive Bell values of the head product's multiplier. -/
noncomputable def headBellGradient (H : CascadeField) (n : ℕ) :
    Fin n → Fin (n + 1) → CascadeField :=
  fun r j => fpderiv ((j : ℕ) + 1)
    (genJetA F.law (F.headSum H (n + 1)) ((r : ℕ) + 1))

/-- **The jets of the head product are the product times the affine Bell values.** -/
theorem iterate_law_head (m : ℕ) {H : CascadeField} (hH0 : H ≠ 0) (hH : H ∈ coordField m)
    (i : ℕ) :
    ((F.law : CascadeField → CascadeField)^[i]) (F.head H m)
      = F.head H m * genJetA F.law (F.headSum H m) i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz, genJetA_succ,
        F.law_head m hH0 hH]
      simp only [smul_eq_mul]
      ring

/-- **The head product's Jacobian has the uniformly scaled shape.** -/
theorem headJetJacobian_eq_uniform (n : ℕ) {H : CascadeField} (hH0 : H ≠ 0)
    (hH : H ∈ coordField (n + 1)) :
    F.headJetJacobian H (n + 1)
      = uniformScaledMatrix (F.head H (n + 1)) (F.headGradient H n)
          (fun r : Fin n => genJetA F.law (F.headSum H (n + 1)) ((r : ℕ) + 1))
          (F.headBellGradient H n) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp [headJetJacobian, uniformScaledMatrix, headGradient]
  · have hjet : ((F.law : CascadeField → CascadeField)^[((r.succ : Fin (n + 1)) : ℕ)])
        (F.head H (n + 1))
        = F.head H (n + 1) * genJetA F.law (F.headSum H (n + 1)) ((r : ℕ) + 1) := by
      rw [Fin.val_succ]
      exact F.iterate_law_head (n + 1) hH0 hH ((r : ℕ) + 1)
    simp only [headJetJacobian, Matrix.of_apply, uniformScaledMatrix, Fin.cases_succ, hjet,
      Derivation.leibniz, smul_eq_mul, headGradient, headBellGradient]

theorem headJetJacobian_det_eq (n : ℕ) {H : CascadeField} (hH0 : H ≠ 0)
    (hH : H ∈ coordField (n + 1)) :
    (F.headJetJacobian H (n + 1)).det
      = F.head H (n + 1) ^ n
        * (uniformBordered (F.headGradient H n) (F.headBellGradient H n)).det := by
  rw [F.headJetJacobian_eq_uniform n hH0 hH, uniformScaledMatrix_det]

/-- **The head product scales out of the bordered determinant.** -/
theorem uniformBordered_headGradient_det {H : CascadeField} (hH0 : H ≠ 0) (n : ℕ)
    (L : Fin n → Fin (n + 1) → CascadeField) :
    (uniformBordered (F.headGradient H n) L).det
      = F.head H (n + 1)
        * (uniformBordered
            (fun j : Fin (n + 1) => F.headBorder H (n + 1) ((j : ℕ) + 1)) L).det := by
  classical
  have hrow : uniformBordered (F.headGradient H n) L
      = Matrix.of fun i j =>
        (Fin.cases (F.head H (n + 1)) (fun _ => (1 : CascadeField)) i)
          * (uniformBordered
              (fun j' : Fin (n + 1) => F.headBorder H (n + 1) ((j' : ℕ) + 1)) L) i j := by
    funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · simp only [uniformBordered, Matrix.of_apply, Fin.cases_zero, headGradient]
      exact F.fpderiv_head_eq hH0 (n + 1) ((j : ℕ) + 1)
    · simp [uniformBordered]
  rw [hrow, Matrix.det_mul_column]
  congr 1
  rw [Fin.prod_univ_succ]
  simp

/-- **The Bell rows are the jet rows of the multiplier.** -/
theorem uniformBordered_headBell_det_eq (H : CascadeField) (n : ℕ)
    (a : Fin (n + 1) → CascadeField) :
    (uniformBordered a (F.headBellGradient H n)).det
      = (uniformBordered a (fun k : Fin n => fun j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1)
            (((F.law : CascadeField → CascadeField)^[(k : ℕ)])
              (F.headSum H (n + 1))))).det :=
  uniformBordered_genBell_det_eq F.law (F.headSum H (n + 1)) n a

/-- **The bordered jet matrix is the peel's orbit matrix.** -/
theorem uniformBordered_eq_orbitMatrix (n : ℕ) {H : CascadeField}
    (hH : H ∈ coordField (n + 1)) :
    uniformBordered (fun j : Fin (n + 1) => F.headBorder H (n + 1) ((j : ℕ) + 1))
        (fun k : Fin n => fun j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1)
            (((F.law : CascadeField → CascadeField)^[(k : ℕ)]) (F.headSum H (n + 1))))
      = F.orbitMatrix (n + 1) (n + 1) (F.headBorder H (n + 1)) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp only [uniformBordered, Matrix.of_apply, Fin.cases_zero, orbitMatrix, Fin.val_zero,
      Function.iterate_zero, id_eq]
  · have hgrad := F.gradient_iterate_headSum (n + 1) (r : ℕ) hH
    have hval := congrArg (fun G : ℕ → CascadeField => G ((j : ℕ) + 1)) hgrad
    simp only [uniformBordered, Matrix.of_apply, Fin.cases_succ, orbitMatrix, Fin.val_succ]
    exact hval

/-- **The head product's jet Jacobian is a nonzero multiple of the peel's orbit determinant.** -/
theorem headJetJacobian_det_ne_zero_of_orbit (n : ℕ) {H : CascadeField} (hH0 : H ≠ 0)
    (hH : H ∈ coordField (n + 1))
    (horbit : (F.orbitMatrix (n + 1) (n + 1) (F.headBorder H (n + 1))).det ≠ 0) :
    (F.headJetJacobian H (n + 1)).det ≠ 0 := by
  rw [F.headJetJacobian_det_eq n hH0 hH,
    F.uniformBordered_headBell_det_eq H n (F.headGradient H n),
    F.uniformBordered_headGradient_det hH0 n, F.uniformBordered_eq_orbitMatrix n hH]
  exact mul_ne_zero (pow_ne_zero _ (F.head_ne_zero hH0 (n + 1)))
    (mul_ne_zero (F.head_ne_zero hH0 (n + 1)) horbit)

end PairFam

end GaloisForLFunctions.HTGeometry
