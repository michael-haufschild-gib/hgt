import GaloisForLFunctions.RHTower.PrimeRotationXiDeterminantSource
import GaloisForLFunctions.RHTower.WindingHomotopy
import GaloisForLFunctions.RHTower.WindingArgumentPrinciple

/-!
# Boundary topology of the literal arithmetic rotation relation

The full singleton Xi jet matrix admits explicit homotopies through
invertible matrices away from the critical line. On its right the actual
flow block shrinks to zero; on its left the circle term shrinks to zero.
The determinant boundary degrees are respectively the full Xi multiplicity
and zero. No zeros are enumerated and no projective class is assumed.

This identifies the source boundary class. Its quantum transgression and
an integral-trace projective realization remain separate open problems.
-/

namespace RHTower
noncomputable section
open scoped Classical

theorem deningerMeyerPrimeMellinCoordinate_norm (p : Nat.Primes) (rho : ℂ) :
    ‖deningerMeyerPrimeMellinCoordinate p rho‖ =
      Real.exp (-Real.log p * (rho.re - 1 / 2)) := by
  rw [deningerMeyerPrimeMellinCoordinate, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.sub_re,
    Complex.div_ofNat_re, Complex.one_re, Complex.neg_im, Complex.ofReal_im,
    neg_zero, zero_mul, sub_zero]

theorem deningerMeyerPrimeMellinCoordinate_norm_lt_one (p : Nat.Primes) (rho : ℂ)
    (h : 1 / 2 < rho.re) : ‖deningerMeyerPrimeMellinCoordinate p rho‖ < 1 := by
  rw [deningerMeyerPrimeMellinCoordinate_norm, Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos p.property.log_pos) (sub_pos.mpr h)

theorem deningerMeyerPrimeMellinCoordinate_one_lt_norm (p : Nat.Primes) (rho : ℂ)
    (h : rho.re < 1 / 2) : 1 < ‖deningerMeyerPrimeMellinCoordinate p rho‖ := by
  rw [deningerMeyerPrimeMellinCoordinate_norm, Real.one_lt_exp_iff]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos p.property.log_pos) (sub_neg.mpr h)

/-- Two scalar parameters deform the literal full prime-flow relation matrix. -/
def deningerMeyerXiBoundaryPencil (p : Nat.Primes) (rho : XiDivisorSupport) (r s : ℂ) :
    Matrix (Fin (xiSupportMultiplicity rho)) (Fin (xiSupportMultiplicity rho)) ℂ :=
  Matrix.scalar _ r - s • deningerMeyerSingleXiFlowMatrix rho (-Real.log p)

theorem deningerMeyerXiBoundaryPencil_det (p : Nat.Primes) (rho : XiDivisorSupport) (r s : ℂ) :
    (deningerMeyerXiBoundaryPencil p rho r s).det =
      (r - s * deningerMeyerPrimeMellinCoordinate p rho) ^ xiSupportMultiplicity rho := by
  have ht : (deningerMeyerXiBoundaryPencil p rho r s).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    simp only [deningerMeyerXiBoundaryPencil, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      deningerMeyerSingleXiFlowMatrix_lower rho (-Real.log p) i j hij', mul_zero,
      Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij'.ne, sub_zero]
  rw [Matrix.det_of_lowerTriangular _ ht]
  simp only [deningerMeyerXiBoundaryPencil, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq, deningerMeyerSingleXiFlowMatrix_diag,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    deningerMeyerPrimeMellinCoordinate, Complex.ofReal_neg]

theorem deningerMeyerXiBoundaryPencil_continuous (p : Nat.Primes) (rho : XiDivisorSupport) :
    Continuous (fun rs : ℂ × ℂ => deningerMeyerXiBoundaryPencil p rho rs.1 rs.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [deningerMeyerXiBoundaryPencil, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

private def relationClamp (s : ℝ) : ℝ := max 0 (min 1 s)

private theorem relationClamp_nonneg (s : ℝ) : 0 ≤ relationClamp s := le_max_left _ _

private theorem relationClamp_le_one (s : ℝ) : relationClamp s ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

private theorem relationClamp_continuous : Continuous relationClamp :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem circle_phase_closed :
    Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) := by
  rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * Real.pi * Complex.I by push_cast; ring]
  simp [Complex.exp_two_pi_mul_I]

/-- The literal relation matrix restricted to the unit circle. -/
def deningerMeyerXiRelationBoundaryMatrix (p : Nat.Primes) (rho : XiDivisorSupport) (theta : ℝ) :=
  deningerMeyerXiBoundaryPencil p rho (Complex.exp (Complex.I * theta)) 1

def deningerMeyerXiRelationBoundaryLoop (p : Nat.Primes) (rho : XiDivisorSupport) (theta : ℝ) : ℂ :=
  (deningerMeyerXiRelationBoundaryMatrix p rho theta).det

/-- On the right half-plane, shrink the actual full flow block to zero. -/
def deningerMeyerXiRightBoundaryHomotopy (p : Nat.Primes) (rho : XiDivisorSupport)
    (s theta : ℝ) :=
  deningerMeyerXiBoundaryPencil p rho (Complex.exp (Complex.I * theta)) (relationClamp s)

/-- On the left half-plane, shrink the circle term to zero. -/
def deningerMeyerXiLeftBoundaryHomotopy (p : Nat.Primes) (rho : XiDivisorSupport)
    (s theta : ℝ) :=
  deningerMeyerXiBoundaryPencil p rho ((relationClamp s : ℂ) * Complex.exp (Complex.I * theta)) 1

private theorem right_pencil_nonzero (p : Nat.Primes) (rho : XiDivisorSupport)
    (hrho : 1 / 2 < (rho : ℂ).re) (s theta : ℝ) :
    Complex.exp (Complex.I * theta) - (relationClamp s : ℂ) *
      deningerMeyerPrimeMellinCoordinate p rho ≠ 0 := by
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  rw [Complex.norm_exp_I_mul_ofReal, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (relationClamp_nonneg s)] at hn
  have hl := deningerMeyerPrimeMellinCoordinate_norm_lt_one p rho hrho
  have hm := mul_le_mul_of_nonneg_right (relationClamp_le_one s)
    (norm_nonneg (deningerMeyerPrimeMellinCoordinate p rho))
  rw [one_mul] at hm
  linarith

private theorem left_pencil_nonzero (p : Nat.Primes) (rho : XiDivisorSupport)
    (hrho : (rho : ℂ).re < 1 / 2) (s theta : ℝ) :
    (relationClamp s : ℂ) * Complex.exp (Complex.I * theta) -
      deningerMeyerPrimeMellinCoordinate p rho ≠ 0 := by
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (relationClamp_nonneg s), mul_one] at hn
  have hl := deningerMeyerPrimeMellinCoordinate_one_lt_norm p rho hrho
  have hm := relationClamp_le_one s
  linarith

theorem deningerMeyerXiRightBoundaryHomotopy_isUnit (p : Nat.Primes) (rho : XiDivisorSupport)
    (hrho : 1 / 2 < (rho : ℂ).re) (s theta : ℝ) :
    IsUnit (deningerMeyerXiRightBoundaryHomotopy p rho s theta) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [deningerMeyerXiRightBoundaryHomotopy, deningerMeyerXiBoundaryPencil_det]
  exact pow_ne_zero _ (right_pencil_nonzero p rho hrho s theta)

theorem deningerMeyerXiLeftBoundaryHomotopy_isUnit (p : Nat.Primes) (rho : XiDivisorSupport)
    (hrho : (rho : ℂ).re < 1 / 2) (s theta : ℝ) :
    IsUnit (deningerMeyerXiLeftBoundaryHomotopy p rho s theta) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [deningerMeyerXiLeftBoundaryHomotopy, deningerMeyerXiBoundaryPencil_det, one_mul]
  exact pow_ne_zero _ (left_pencil_nonzero p rho hrho s theta)

theorem deningerMeyerXiRightBoundaryHomotopy_continuous (p : Nat.Primes) (rho : XiDivisorSupport) :
    Continuous (fun st : ℝ × ℝ => deningerMeyerXiRightBoundaryHomotopy p rho st.1 st.2) := by
  exact (deningerMeyerXiBoundaryPencil_continuous p rho).comp
    ((by fun_prop : Continuous (fun st : ℝ × ℝ => Complex.exp (Complex.I * st.2))).prodMk
      (Complex.continuous_ofReal.comp (relationClamp_continuous.comp continuous_fst)))

theorem deningerMeyerXiLeftBoundaryHomotopy_continuous (p : Nat.Primes) (rho : XiDivisorSupport) :
    Continuous (fun st : ℝ × ℝ => deningerMeyerXiLeftBoundaryHomotopy p rho st.1 st.2) := by
  exact (deningerMeyerXiBoundaryPencil_continuous p rho).comp
    (((Complex.continuous_ofReal.comp (relationClamp_continuous.comp continuous_fst)).mul
      (by fun_prop : Continuous (fun st : ℝ × ℝ => Complex.exp (Complex.I * st.2)))).prodMk
        continuous_const)

@[simp] theorem deningerMeyerXiRightBoundaryHomotopy_zero (p : Nat.Primes) (rho : XiDivisorSupport)
    (theta : ℝ) : deningerMeyerXiRightBoundaryHomotopy p rho 0 theta =
      Matrix.scalar _ (Complex.exp (Complex.I * theta)) := by
  simp [deningerMeyerXiRightBoundaryHomotopy, relationClamp, deningerMeyerXiBoundaryPencil]

@[simp] theorem deningerMeyerXiRightBoundaryHomotopy_one (p : Nat.Primes) (rho : XiDivisorSupport)
    (theta : ℝ) : deningerMeyerXiRightBoundaryHomotopy p rho 1 theta =
      deningerMeyerXiRelationBoundaryMatrix p rho theta := by
  simp [deningerMeyerXiRightBoundaryHomotopy, relationClamp, deningerMeyerXiRelationBoundaryMatrix]

@[simp] theorem deningerMeyerXiLeftBoundaryHomotopy_zero (p : Nat.Primes) (rho : XiDivisorSupport)
    (theta : ℝ) : deningerMeyerXiLeftBoundaryHomotopy p rho 0 theta =
      -deningerMeyerSingleXiFlowMatrix rho (-Real.log p) := by
  simp [deningerMeyerXiLeftBoundaryHomotopy, relationClamp, deningerMeyerXiBoundaryPencil]

@[simp] theorem deningerMeyerXiLeftBoundaryHomotopy_one (p : Nat.Primes) (rho : XiDivisorSupport)
    (theta : ℝ) : deningerMeyerXiLeftBoundaryHomotopy p rho 1 theta =
      deningerMeyerXiRelationBoundaryMatrix p rho theta := by
  simp [deningerMeyerXiLeftBoundaryHomotopy, relationClamp, deningerMeyerXiRelationBoundaryMatrix]

/-- The actual source relation has full multiplicity as its right-side boundary degree. -/
theorem deningerMeyerXiRelationBoundaryLoop_winding_right (p : Nat.Primes) (rho : XiDivisorSupport)
    (hrho : 1 / 2 < (rho : ℂ).re) :
    windingNumber (deningerMeyerXiRelationBoundaryLoop p rho) 0 (2 * Real.pi) =
      xiSupportMultiplicity rho := by
  let H : ℝ → ℝ → ℂ := fun s theta =>
    (Complex.exp (Complex.I * theta) - (relationClamp s : ℂ) *
      deningerMeyerPrimeMellinCoordinate p rho) ^ xiSupportMultiplicity rho
  have hc : Continuous (fun st : ℝ × ℝ => H st.1 st.2) :=
    ((by fun_prop : Continuous (fun st : ℝ × ℝ => Complex.exp (Complex.I * st.2))).sub
      ((Complex.continuous_ofReal.comp (relationClamp_continuous.comp continuous_fst)).mul
        continuous_const)).pow _
  have hn : ∀ s theta, H s theta ≠ 0 := fun s theta =>
    pow_ne_zero _ (right_pencil_nonzero p rho hrho s theta)
  have hl : ∀ s, H s 0 = H s (2 * Real.pi) := by
    intro s
    change (_ - _) ^ _ = (_ - _) ^ _
    rw [circle_phase_closed]
  have hw := windingNumber_of_homotopic H hc hn hl
    (γ₀ := fun theta : ℝ => Complex.exp (Complex.I * theta) ^ xiSupportMultiplicity rho)
    (γ₁ := deningerMeyerXiRelationBoundaryLoop p rho)
    (fun theta => by simp [H, relationClamp])
    (fun theta => by simp [H, relationClamp, deningerMeyerXiRelationBoundaryLoop,
      deningerMeyerXiRelationBoundaryMatrix, deningerMeyerXiBoundaryPencil_det])
  rw [← hw]
  simpa using windingNumber_center_zero (xiSupportMultiplicity rho) 1 zero_lt_one

/-- The actual source relation contracts on the opposite side of the critical line. -/
theorem deningerMeyerXiRelationBoundaryLoop_winding_left (p : Nat.Primes) (rho : XiDivisorSupport)
    (hrho : (rho : ℂ).re < 1 / 2) :
    windingNumber (deningerMeyerXiRelationBoundaryLoop p rho) 0 (2 * Real.pi) = 0 := by
  let H : ℝ → ℝ → ℂ := fun s theta =>
    ((relationClamp s : ℂ) * Complex.exp (Complex.I * theta) -
      deningerMeyerPrimeMellinCoordinate p rho) ^ xiSupportMultiplicity rho
  have hc : Continuous (fun st : ℝ × ℝ => H st.1 st.2) :=
    (((Complex.continuous_ofReal.comp (relationClamp_continuous.comp continuous_fst)).mul
      (by fun_prop : Continuous (fun st : ℝ × ℝ => Complex.exp (Complex.I * st.2)))).sub
        continuous_const).pow _
  have hn : ∀ s theta, H s theta ≠ 0 := fun s theta =>
    pow_ne_zero _ (left_pencil_nonzero p rho hrho s theta)
  have hl : ∀ s, H s 0 = H s (2 * Real.pi) := by
    intro s
    change (_ * Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) - _) ^ _ = (_ - _) ^ _
    rw [circle_phase_closed]
  have hw := windingNumber_of_homotopic H hc hn hl
    (γ₀ := fun _ : ℝ => (-deningerMeyerPrimeMellinCoordinate p rho) ^ xiSupportMultiplicity rho)
    (γ₁ := deningerMeyerXiRelationBoundaryLoop p rho)
    (fun theta => by simp [H, relationClamp])
    (fun theta => by simp [H, relationClamp, deningerMeyerXiRelationBoundaryLoop,
      deningerMeyerXiRelationBoundaryMatrix, deningerMeyerXiBoundaryPencil_det])
  rw [← hw]
  exact windingNumber_const (pow_ne_zero _ (neg_ne_zero.mpr (Complex.exp_ne_zero _))) _ _

end
end RHTower
