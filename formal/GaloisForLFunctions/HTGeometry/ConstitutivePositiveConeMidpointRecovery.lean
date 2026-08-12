import Mathlib

/-!
# Positive-cone midpoint recovery for reciprocal formation packets

The metric geometric mean is built from continuous functional calculus and proved to be the unique
positive-definite solution of its Riccati equation.  Direct/reflected quadratic formation has exact
midpoint `R * R`; conversely every positive-definite packet reconstructs positive formation and
relative-law coordinates whose direct/reflected outputs are the original packet.

This is the unconditional reconstruction core of ULF-RFTM-3.  It contains no RH premise.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Metric geometric mean of two matrices, defined by positive square-root congruence. -/
noncomputable def positiveMatrixGeometricMean (A B : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  let H := CFC.sqrt A
  H * CFC.sqrt (H⁻¹ * B * H⁻¹) * H

/-- The continuous-functional-calculus square root of a positive-definite matrix is positive
definite. -/
lemma positiveMatrixSqrt_posDef {A : Matrix n n 𝕜} (hA : A.PosDef) :
    (CFC.sqrt A).PosDef := by
  exact Matrix.IsStrictlyPositive.posDef (hA.isStrictlyPositive.sqrt _)

/-- Positive congruence by a positive-definite matrix preserves positive definiteness. -/
lemma posDef_positiveCongruence {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef) :
    (A * B * A).PosDef := by
  have h := hA.isUnit.posDef_star_right_conjugate_iff.mpr hB
  simpa only [star_eq_conjTranspose, hA.isHermitian.eq] using h

/-- Inverse positive congruence preserves positive definiteness. -/
lemma posDef_inversePositiveCongruence {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) :
    (A⁻¹ * B * A⁻¹).PosDef := by
  exact posDef_positiveCongruence hA.inv hB

/-- Positive matrix square root squares to the original matrix. -/
lemma positiveMatrixSqrt_mul_self {A : Matrix n n 𝕜} (hA : A.PosDef) :
    CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A (ha := hA.posSemidef.nonneg)

/-- The inverse of a positive-definite matrix is the square of the inverse positive square root. -/
lemma posDef_inv_eq_sqrtInv_mul_sqrtInv {A : Matrix n n 𝕜} (hA : A.PosDef) :
    A⁻¹ = (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ := by
  let H := CFC.sqrt A
  have hH : H.PosDef := positiveMatrixSqrt_posDef hA
  have hHdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hHHdet : IsUnit (H * H).det :=
    (Matrix.isUnit_iff_isUnit_det (H * H)).mp (hH.isUnit.mul hH.isUnit)
  have hsq : H * H = A := positiveMatrixSqrt_mul_self hA
  calc
    A⁻¹ = (H * H)⁻¹ := congrArg Inv.inv hsq.symm
    _ = H⁻¹ * H⁻¹ := by
      apply left_inv_eq_right_inv (Matrix.nonsing_inv_mul (H * H) hHHdet)
      simp only [Matrix.mul_assoc]
      simp [Matrix.mul_nonsing_inv_cancel_left H H⁻¹ hHdet,
        Matrix.mul_nonsing_inv H hHdet]

/-- The metric geometric mean of positive-definite matrices is positive definite. -/
lemma positiveMatrixGeometricMean_posDef {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) :
    (positiveMatrixGeometricMean A B).PosDef := by
  let H := CFC.sqrt A
  have hH : H.PosDef := positiveMatrixSqrt_posDef hA
  have hC : (H⁻¹ * B * H⁻¹).PosDef := posDef_inversePositiveCongruence hH hB
  have hS : (CFC.sqrt (H⁻¹ * B * H⁻¹)).PosDef := positiveMatrixSqrt_posDef hC
  exact posDef_positiveCongruence hH hS

/-- The metric geometric mean solves the positive Riccati equation. -/
lemma positiveMatrixGeometricMean_riccati {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) :
    positiveMatrixGeometricMean A B * A⁻¹ * positiveMatrixGeometricMean A B = B := by
  let H := CFC.sqrt A
  let C := H⁻¹ * B * H⁻¹
  let K := CFC.sqrt C
  have hH : H.PosDef := positiveMatrixSqrt_posDef hA
  have hHdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hC : C.PosDef := posDef_inversePositiveCongruence hH hB
  have hKsq : K * K = C := CFC.sqrt_mul_sqrt_self C (ha := hC.posSemidef.nonneg)
  have hAinv : A⁻¹ = H⁻¹ * H⁻¹ := posDef_inv_eq_sqrtInv_mul_sqrtInv hA
  unfold positiveMatrixGeometricMean
  dsimp only
  change (H * K * H) * A⁻¹ * (H * K * H) = B
  rw [hAinv]
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_nonsing_inv_cancel_left H _ hHdet,
    Matrix.nonsing_inv_mul_cancel_left H _ hHdet]
  rw [← Matrix.mul_assoc K K H, hKsq]
  dsimp [C]
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_nonsing_inv_cancel_left H _ hHdet]
  rw [Matrix.nonsing_inv_mul H hHdet, Matrix.mul_one]

/-- The metric geometric mean is the unique positive-definite Riccati solution. -/
lemma positiveMatrixGeometricMean_unique {A B Z : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) (hZ : Z.PosDef)
    (hRiccati : Z * A⁻¹ * Z = B) :
    positiveMatrixGeometricMean A B = Z := by
  let H := CFC.sqrt A
  let C := H⁻¹ * B * H⁻¹
  let K := CFC.sqrt C
  let W := H⁻¹ * Z * H⁻¹
  have hH : H.PosDef := positiveMatrixSqrt_posDef hA
  have hHdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hC : C.PosDef := posDef_inversePositiveCongruence hH hB
  have hW : W.PosDef := posDef_inversePositiveCongruence hH hZ
  have hAinv : A⁻¹ = H⁻¹ * H⁻¹ := posDef_inv_eq_sqrtInv_mul_sqrtInv hA
  rw [hAinv] at hRiccati
  have hWsq : W * W = C := by
    dsimp [W, C]
    calc
      (H⁻¹ * Z * H⁻¹) * (H⁻¹ * Z * H⁻¹) =
          H⁻¹ * (Z * (H⁻¹ * H⁻¹) * Z) * H⁻¹ := by noncomm_ring
      _ = H⁻¹ * B * H⁻¹ := by rw [hRiccati]
  have hKW : K = W :=
    (CFC.sqrt_eq_iff C W (ha := hC.posSemidef.nonneg)
      (hb := hW.posSemidef.nonneg)).2 hWsq
  unfold positiveMatrixGeometricMean
  dsimp only
  change H * K * H = Z
  rw [hKW]
  dsimp [W]
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_nonsing_inv_cancel_left H _ hHdet]
  rw [Matrix.nonsing_inv_mul H hHdet, Matrix.mul_one]

/-- Direct leg of a positive reciprocal formation packet. -/
def positiveFormationPacketDirect (R Q : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  R * Q * R

/-- Reflected leg of a positive reciprocal formation packet. -/
noncomputable def positiveFormationPacketReflected (R Q : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  R * Q⁻¹ * R

/-- Inversion reverses a positive congruence triple. -/
lemma posDef_inv_triple {R Q : Matrix n n 𝕜} (hR : R.PosDef) (hQ : Q.PosDef) :
    (R * Q * R)⁻¹ = R⁻¹ * Q⁻¹ * R⁻¹ := by
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have hX : (R * Q * R).PosDef := posDef_positiveCongruence hR hQ
  have hXdet : IsUnit (R * Q * R).det :=
    (Matrix.isUnit_iff_isUnit_det (R * Q * R)).mp hX.isUnit
  apply left_inv_eq_right_inv (Matrix.nonsing_inv_mul (R * Q * R) hXdet)
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_nonsing_inv_cancel_left R _ hRdet,
    Matrix.mul_nonsing_inv_cancel_left Q _ hQdet]
  rw [Matrix.mul_nonsing_inv R hRdet]

/-- The formation square satisfies the Riccati midpoint equation for the packet. -/
lemma positiveFormationPacket_midpoint_riccati {R Q : Matrix n n 𝕜}
    (hR : R.PosDef) (hQ : Q.PosDef) :
    (R * R) * (positiveFormationPacketDirect R Q)⁻¹ * (R * R) =
      positiveFormationPacketReflected R Q := by
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  rw [positiveFormationPacketDirect, positiveFormationPacketReflected, posDef_inv_triple hR hQ]
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_nonsing_inv_cancel_left R _ hRdet,
    Matrix.nonsing_inv_mul_cancel_left R _ hRdet]

/-- Exact midpoint-recovery law: the direct/reflected packet's unique positive midpoint is the
formation square. -/
lemma positiveFormationPacket_midpoint {R Q : Matrix n n 𝕜}
    (hR : R.PosDef) (hQ : Q.PosDef) :
    positiveMatrixGeometricMean (positiveFormationPacketDirect R Q)
      (positiveFormationPacketReflected R Q) = R * R := by
  have hX : (positiveFormationPacketDirect R Q).PosDef := posDef_positiveCongruence hR hQ
  have hY : (positiveFormationPacketReflected R Q).PosDef :=
    posDef_positiveCongruence hR hQ.inv
  have hS : (R * R).PosDef := by
    have h := posDef_positiveCongruence hR (Matrix.PosDef.one : (1 : Matrix n n 𝕜).PosDef)
    simpa using h
  exact positiveMatrixGeometricMean_unique hX hY hS
    (positiveFormationPacket_midpoint_riccati hR hQ)

/-- Recovered positive formation factor of an arbitrary positive packet. -/
noncomputable def positiveFormationRecoveryR (X Y : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  CFC.sqrt (positiveMatrixGeometricMean X Y)

/-- Recovered relative-law factor of an arbitrary positive packet. -/
noncomputable def positiveFormationRecoveryQ (X Y : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  let R := positiveFormationRecoveryR X Y
  R⁻¹ * X * R⁻¹

lemma positiveFormationRecoveryR_posDef {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) : (positiveFormationRecoveryR X Y).PosDef := by
  exact positiveMatrixSqrt_posDef (positiveMatrixGeometricMean_posDef hX hY)

lemma positiveFormationRecoveryQ_posDef {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) : (positiveFormationRecoveryQ X Y).PosDef := by
  exact posDef_inversePositiveCongruence (positiveFormationRecoveryR_posDef hX hY) hX

lemma positiveFormationRecoveryR_sq {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) :
    positiveFormationRecoveryR X Y * positiveFormationRecoveryR X Y =
      positiveMatrixGeometricMean X Y := by
  exact CFC.sqrt_mul_sqrt_self _
    (ha := (positiveMatrixGeometricMean_posDef hX hY).posSemidef.nonneg)

/-- Recovered coordinates reproduce the direct packet leg exactly. -/
lemma positiveFormationRecovery_direct {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) :
    positiveFormationPacketDirect (positiveFormationRecoveryR X Y)
      (positiveFormationRecoveryQ X Y) = X := by
  let R := positiveFormationRecoveryR X Y
  have hR : R.PosDef := positiveFormationRecoveryR_posDef hX hY
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  unfold positiveFormationPacketDirect positiveFormationRecoveryQ
  change R * (R⁻¹ * X * R⁻¹) * R = X
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_nonsing_inv_cancel_left R _ hRdet]
  rw [Matrix.nonsing_inv_mul R hRdet, Matrix.mul_one]

/-- Recovered coordinates reproduce the reflected packet leg exactly. -/
lemma positiveFormationRecovery_reflected {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) :
    positiveFormationPacketReflected (positiveFormationRecoveryR X Y)
      (positiveFormationRecoveryQ X Y) = Y := by
  let S := positiveMatrixGeometricMean X Y
  let R := positiveFormationRecoveryR X Y
  let Q := positiveFormationRecoveryQ X Y
  have hR : R.PosDef := positiveFormationRecoveryR_posDef hX hY
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hQ : Q.PosDef := positiveFormationRecoveryQ_posDef hX hY
  have hQinv0 := posDef_inv_triple hR.inv hX
  have hQinv : Q⁻¹ = R * X⁻¹ * R := by
    dsimp [Q, positiveFormationRecoveryQ]
    simpa only [Matrix.nonsing_inv_nonsing_inv R hRdet] using hQinv0
  have hSric : S * X⁻¹ * S = Y := positiveMatrixGeometricMean_riccati hX hY
  have hRsq : R * R = S := positiveFormationRecoveryR_sq hX hY
  unfold positiveFormationPacketReflected
  change R * Q⁻¹ * R = Y
  rw [hQinv]
  calc
    R * (R * X⁻¹ * R) * R = (R * R) * X⁻¹ * (R * R) := by noncomm_ring
    _ = S * X⁻¹ * S := by rw [hRsq]
    _ = Y := hSric

/-- The positive square root of a positive square is the original positive factor. -/
lemma positiveMatrixSqrt_mul_self_eq {R : Matrix n n 𝕜} (hR : R.PosDef) :
    CFC.sqrt (R * R) = R := by
  have hRR : (R * R).PosDef := by
    have h := posDef_positiveCongruence hR (Matrix.PosDef.one : (1 : Matrix n n 𝕜).PosDef)
    simpa using h
  exact (CFC.sqrt_eq_iff (R * R) R (ha := hRR.posSemidef.nonneg)
    (hb := hR.posSemidef.nonneg)).2 rfl

/-- Midpoint recovery returns the original positive formation factor. -/
lemma positiveFormationRecoveryR_formation {R Q : Matrix n n 𝕜}
    (hR : R.PosDef) (hQ : Q.PosDef) :
    positiveFormationRecoveryR (positiveFormationPacketDirect R Q)
      (positiveFormationPacketReflected R Q) = R := by
  unfold positiveFormationRecoveryR
  rw [positiveFormationPacket_midpoint hR hQ]
  exact positiveMatrixSqrt_mul_self_eq hR

end GaloisForLFunctions.HTGeometry
