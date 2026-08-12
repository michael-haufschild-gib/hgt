import GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery

/-!
# Positive reciprocal formation reflection

Packet exchange is conjugate, through global positive-cone recovery, to inversion of the relative
law coordinate.  The formation midpoint is fixed and both coordinates remain exactly recoverable.

This is the unconditional reflection-neutrality core of ULF-RFTM-3A.  It contains no RH premise.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The positive Riccati midpoint is symmetric in its two packet legs. -/
lemma positiveMatrixGeometricMean_comm {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) :
    positiveMatrixGeometricMean A B = positiveMatrixGeometricMean B A := by
  let S := positiveMatrixGeometricMean A B
  have hS : S.PosDef := positiveMatrixGeometricMean_posDef hA hB
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hRiccati : S * A⁻¹ * S = B := positiveMatrixGeometricMean_riccati hA hB
  have hBinv : B⁻¹ = S⁻¹ * A * S⁻¹ := by
    calc
      B⁻¹ = (S * A⁻¹ * S)⁻¹ := congrArg Inv.inv hRiccati.symm
      _ = S⁻¹ * (A⁻¹)⁻¹ * S⁻¹ := posDef_inv_triple hS hA.inv
      _ = S⁻¹ * A * S⁻¹ := by rw [Matrix.nonsing_inv_nonsing_inv A hAdet]
  have hSwap : S * B⁻¹ * S = A := by
    rw [hBinv]
    simp only [Matrix.mul_assoc]
    simp only [Matrix.mul_nonsing_inv_cancel_left S _ hSdet]
    rw [Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one]
  exact (positiveMatrixGeometricMean_unique hB hA hS hSwap).symm

/-- Exchanging packet legs fixes the recovered positive formation factor. -/
lemma positiveFormationRecoveryR_swap {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) :
    positiveFormationRecoveryR Y X = positiveFormationRecoveryR X Y := by
  unfold positiveFormationRecoveryR
  rw [← positiveMatrixGeometricMean_comm hX hY]

/-- Exchanging packet legs inverts the recovered relative-law factor. -/
lemma positiveFormationRecoveryQ_swap {X Y : Matrix n n 𝕜}
    (hX : X.PosDef) (hY : Y.PosDef) :
    positiveFormationRecoveryQ Y X = (positiveFormationRecoveryQ X Y)⁻¹ := by
  let R := positiveFormationRecoveryR X Y
  let Q := positiveFormationRecoveryQ X Y
  have hR : R.PosDef := positiveFormationRecoveryR_posDef hX hY
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hRswap : positiveFormationRecoveryR Y X = R :=
    positiveFormationRecoveryR_swap hX hY
  have hDirectSwap :
      positiveFormationPacketDirect (positiveFormationRecoveryR Y X)
          (positiveFormationRecoveryQ Y X) = Y :=
    positiveFormationRecovery_direct hY hX
  have hReflected : positiveFormationPacketReflected R Q = Y :=
    positiveFormationRecovery_reflected hX hY
  rw [hRswap] at hDirectSwap
  have hCongruence :
      R * positiveFormationRecoveryQ Y X * R = R * Q⁻¹ * R := by
    exact hDirectSwap.trans hReflected.symm
  calc
    positiveFormationRecoveryQ Y X =
        R⁻¹ * (R * positiveFormationRecoveryQ Y X * R) * R⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv R hRdet, Matrix.mul_one]
      rw [Matrix.nonsing_inv_mul_cancel_left R _ hRdet]
    _ = R⁻¹ * (R * Q⁻¹ * R) * R⁻¹ := by rw [hCongruence]
    _ = Q⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv R hRdet, Matrix.mul_one]
      rw [Matrix.nonsing_inv_mul_cancel_left R _ hRdet]

/-- Recovery also returns the original relative-law coordinate of a formed packet. -/
lemma positiveFormationRecoveryQ_formation {R Q : Matrix n n 𝕜}
    (hR : R.PosDef) (hQ : Q.PosDef) :
    positiveFormationRecoveryQ (positiveFormationPacketDirect R Q)
      (positiveFormationPacketReflected R Q) = Q := by
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hX : (positiveFormationPacketDirect R Q).PosDef := posDef_positiveCongruence hR hQ
  have hY : (positiveFormationPacketReflected R Q).PosDef :=
    posDef_positiveCongruence hR hQ.inv
  have hDirect := positiveFormationRecovery_direct hX hY
  rw [positiveFormationRecoveryR_formation hR hQ] at hDirect
  have hCongruence :
      R * positiveFormationRecoveryQ (positiveFormationPacketDirect R Q)
          (positiveFormationPacketReflected R Q) * R = R * Q * R := by
    exact hDirect
  calc
    positiveFormationRecoveryQ (positiveFormationPacketDirect R Q)
        (positiveFormationPacketReflected R Q) =
        R⁻¹ * (R * positiveFormationRecoveryQ (positiveFormationPacketDirect R Q)
          (positiveFormationPacketReflected R Q) * R) * R⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv R hRdet, Matrix.mul_one]
      rw [Matrix.nonsing_inv_mul_cancel_left R _ hRdet]
    _ = R⁻¹ * (R * Q * R) * R⁻¹ := by rw [hCongruence]
    _ = Q := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv R hRdet, Matrix.mul_one]
      rw [Matrix.nonsing_inv_mul_cancel_left R _ hRdet]

/-- Parameter reflection exchanges the direct and reflected packet legs. -/
lemma positiveFormationPacketDirect_inverse {R Q : Matrix n n 𝕜} :
    positiveFormationPacketDirect R Q⁻¹ = positiveFormationPacketReflected R Q := by
  rfl

/-- The second exchanged leg returns the original direct leg for positive relative laws. -/
lemma positiveFormationPacketReflected_inverse {R Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    positiveFormationPacketReflected R Q⁻¹ = positiveFormationPacketDirect R Q := by
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  unfold positiveFormationPacketReflected positiveFormationPacketDirect
  rw [Matrix.nonsing_inv_nonsing_inv Q hQdet]

/-- **Positive functional-equation capstone.**  Packet exchange lifts through global recovery by
fixing formation and inverting the complete relative law; applying it twice returns every formed
packet and no recoverable coordinate is lost. -/
theorem positiveFormationReflection_informationNeutral {R Q : Matrix n n 𝕜}
    (hR : R.PosDef) (hQ : Q.PosDef) :
    positiveFormationPacketDirect R Q⁻¹ = positiveFormationPacketReflected R Q ∧
      positiveFormationPacketReflected R Q⁻¹ = positiveFormationPacketDirect R Q ∧
      positiveFormationRecoveryR (positiveFormationPacketReflected R Q)
          (positiveFormationPacketDirect R Q) = R ∧
      positiveFormationRecoveryQ (positiveFormationPacketReflected R Q)
          (positiveFormationPacketDirect R Q) = Q⁻¹ := by
  have hX : (positiveFormationPacketDirect R Q).PosDef := posDef_positiveCongruence hR hQ
  have hY : (positiveFormationPacketReflected R Q).PosDef :=
    posDef_positiveCongruence hR hQ.inv
  exact ⟨positiveFormationPacketDirect_inverse,
    positiveFormationPacketReflected_inverse hQ,
    (positiveFormationRecoveryR_swap hX hY).trans
      (positiveFormationRecoveryR_formation hR hQ),
    (positiveFormationRecoveryQ_swap hX hY).trans
      (congrArg Inv.inv (positiveFormationRecoveryQ_formation hR hQ))⟩

end GaloisForLFunctions.HTGeometry
