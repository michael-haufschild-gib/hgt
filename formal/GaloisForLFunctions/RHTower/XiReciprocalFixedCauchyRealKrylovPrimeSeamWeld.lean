import GaloisForLFunctions.RHTower.XiReciprocalFixedCauchyRealKrylovSeam
import GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoOrientationEnergy
import GaloisForLFunctions.RHTower.XiHurwitzOrientationUniversalityLaw

/-!
# Fixed reciprocal-Krylov seam to first-prime source seam

The local seam of the fixed adjoint response and the translated von Mangoldt/Hurwitz first-prime
seam have the same pointwise zero fibre.  This identifies the rightmost reciprocal-Krylov RH
interface directly with an actual prime--Gamma source condition, without passing through either
interface's separate RH equivalence.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Centered spectral reality is exactly vanishing of the raw-divisor first-prime source seam. -/
theorem xiSpectralPoint_im_eq_zero_iff_orbitwiseFirstPrimeSeamCharge_eq_zero
    (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 0 ↔
      orbitwiseFirstPrimeSeamCharge (q.1 : ℂ) = 0 := by
  rw [orbitwiseFirstPrimeSeamCharge_eq_zero_iff,
    xiSpectralPoint_eq_support]
  simp only [xiSpectralPointSupport, Complex.mul_im]
  norm_num
  constructor <;> intro h <;> linarith

/-- Pointwise fixed adjoint-response seam and first-prime source seam have identical zero fibres. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovSeam_eq_zero_iff_firstPrimeSeamCharge_eq_zero
    (q : XiZeroCopy) :
    xiReciprocalCauchyRealKrylovSeam xiReciprocalSquareFixedCauchyPole q
        (xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest
            (xiReciprocalSquareFixedCauchyPole : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
            xiReciprocalSquareFixedCauchyPole)) = 0 ↔
      orbitwiseFirstPrimeSeamCharge (q.1 : ℂ) = 0 := by
  constructor
  · intro hseam
    exact
      (xiSpectralPoint_im_eq_zero_iff_orbitwiseFirstPrimeSeamCharge_eq_zero q).mp
        (xiSpectralPoint_im_eq_zero_of_adjointResponse_realKrylovSeam_eq_zero
          xiReciprocalSquareFixedCauchyPole
          (by rw [xiReciprocalSquareFixedCauchyPole_im]; norm_num)
          q hseam)
  · intro hcharge
    have him : (xiSpectralPoint q).im = 0 :=
      (xiSpectralPoint_im_eq_zero_iff_orbitwiseFirstPrimeSeamCharge_eq_zero q).mpr
        hcharge
    rw [xiReciprocalCauchyRealKrylovSeam_adjointResponse_eq, him]
    simp

/-- Fixed adjoint-response seam saturation is exactly vanishing of all Xi-indexed first-prime
source seams. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_firstPrimeSeamChargesVanish :
    XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation ↔
      XiFirstPrimeSeamChargesVanish := by
  constructor
  · intro hseam rho
    have hpos := xi_divisor_pos_on_support rho
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      omega
    let q : XiZeroCopy := ⟨rho, ⟨0, hn⟩⟩
    exact
      xiReciprocalSquareFixedCauchyRealKrylovSeam_eq_zero_iff_firstPrimeSeamCharge_eq_zero
        q |>.mp (hseam q)
  · intro hcharge q
    exact
      xiReciprocalSquareFixedCauchyRealKrylovSeam_eq_zero_iff_firstPrimeSeamCharge_eq_zero
        q |>.mpr (hcharge q.1)

/-- The rightmost local Krylov seam is exactly the normalized Hurwitz/prime-two source asymptotic
seam, with no RH detour. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_hurwitzAnchorPrimeTwoSeamsVanish :
    XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation ↔
      XiHurwitzAnchorPrimeTwoSeamsVanish :=
  xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_firstPrimeSeamChargesVanish.trans
    xiHurwitzAnchorPrimeTwoSeamsVanish_iff_firstPrimeSeamChargesVanish.symm

/-- The same direct weld identifies local Krylov seam saturation with zero Xi--Hurwitz source
orientation energy. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_hurwitzOrientationEnergy_zero :
    XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation ↔
      xiHurwitzOrientationEnergy = 0 :=
  xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_firstPrimeSeamChargesVanish.trans
    xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero

/-- Existing Cauchy-source-core positivity discharges the fixed adjoint-response seam directly. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_of_cauchyCore_nonnegative
    (hpos : ∀ v ∈ xiWeilCauchyAlgebraicSubspace,
      0 ≤ xiWeilHilbertQuadratic v) :
    XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation := by
  apply
    xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_hurwitzAnchorPrimeTwoSeamsVanish.mpr
  exact xiHurwitzAnchorPrimeTwoSeamsVanish_of_cauchyCore_nonnegative hpos

/-- Eventual Weil nonnegativity along one convergent continued prime--Gamma source sequence
discharges the fixed adjoint-response seam without an RH intermediate. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_of_hurwitzContinuedCauchySequenceNonnegative
    (hsource : XiHurwitzContinuedCauchySequenceNonnegative) :
    XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation := by
  rcases hsource with ⟨V, _hmem, _hV, henergy, hnonneg⟩
  have hlimit : 0 ≤ -xiHurwitzOrientationEnergy :=
    ge_of_tendsto henergy hnonneg
  apply
    xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_hurwitzOrientationEnergy_zero.mpr
  linarith [xiHurwitzOrientationEnergy_nonneg]

/-- Eventual nonnegativity of one convergent sequence of pairwise-separated finite prime--Gamma
packets likewise discharges the fixed adjoint-response seam directly. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_of_hurwitzSeparatedSourceSequenceNonnegative
    (hsource : XiHurwitzSeparatedSourceSequenceNonnegative) :
    XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation := by
  rcases hsource with ⟨P, _hP, henergy, hnonneg⟩
  have hlimit : 0 ≤ -xiHurwitzOrientationEnergy :=
    ge_of_tendsto henergy hnonneg
  apply
    xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_hurwitzOrientationEnergy_zero.mpr
  linarith [xiHurwitzOrientationEnergy_nonneg]

/-- Empty separated source packet, used when orientation target has collapsed to zero. -/
def xiEmptySeparatedContinuedCauchyPacket : XiSeparatedContinuedCauchyPacket where
  index := Fin 0
  fintypeIndex := inferInstance
  coeff := Fin.elim0
  pole := Fin.elim0
  separated i := Fin.elim0 i

@[simp] theorem xiEmptySeparatedContinuedCauchyPacket_evaluation :
    xiEmptySeparatedContinuedCauchyPacket.evaluation = 0 := by
  rw [XiSeparatedContinuedCauchyPacket.evaluation]
  unfold xiWeilContinuedCauchyPacketLp
  change (∑ _i : Fin 0, _) = 0
  rw [Fintype.sum_empty]

@[simp] theorem xiEmptySeparatedContinuedCauchyPacket_sourceEnergy :
    xiEmptySeparatedContinuedCauchyPacket.sourceEnergy = 0 := by
  rw [XiSeparatedContinuedCauchyPacket.sourceEnergy_eq_hilbertQuadratic,
    xiEmptySeparatedContinuedCauchyPacket_evaluation]
  simp [xiWeilHilbertQuadratic, xiWeilLineConjLinearIsometry]

/-- Seam saturation constructs a continued-source nonnegative sequence directly: energy zero
makes the target orientation vector zero, so the constant zero sequence is a witness. -/
theorem xiHurwitzContinuedCauchySequenceNonnegative_of_reciprocalSquareFixedCauchyRealKrylovSeamSaturation
    (hseam : XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation) :
    XiHurwitzContinuedCauchySequenceNonnegative := by
  have henergy : xiHurwitzOrientationEnergy = 0 :=
    xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_hurwitzOrientationEnergy_zero.mp
      hseam
  have hvector : xiHurwitzOrientationVector = 0 :=
    xiHurwitzOrientationVector_eq_zero_iff_energy_eq_zero.mpr henergy
  refine ⟨fun _ => 0, fun _ => Submodule.zero_mem _, ?_, ?_, ?_⟩
  · simpa only [hvector] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (0 : lp (fun _ : XiZeroCopy => ℂ) 2)) atTop (nhds 0))
  · have hquadratic : xiWeilHilbertQuadratic
        (0 : lp (fun _ : XiZeroCopy => ℂ) 2) = 0 := by
      simp [xiWeilHilbertQuadratic, xiWeilLineConjLinearIsometry]
    simpa only [hquadratic, henergy, neg_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · exact Eventually.of_forall fun _ => by
      have hquadratic : xiWeilHilbertQuadratic
          (0 : lp (fun _ : XiZeroCopy => ℂ) 2) = 0 := by
        simp [xiWeilHilbertQuadratic, xiWeilLineConjLinearIsometry]
      rw [hquadratic]

/-- Seam saturation also constructs a separated finite prime--Gamma packet sequence directly:
the constant empty packet converges to the collapsed zero orientation target. -/
theorem xiHurwitzSeparatedSourceSequenceNonnegative_of_reciprocalSquareFixedCauchyRealKrylovSeamSaturation
    (hseam : XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation) :
    XiHurwitzSeparatedSourceSequenceNonnegative := by
  have henergy : xiHurwitzOrientationEnergy = 0 :=
    xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_hurwitzOrientationEnergy_zero.mp
      hseam
  have hvector : xiHurwitzOrientationVector = 0 :=
    xiHurwitzOrientationVector_eq_zero_iff_energy_eq_zero.mpr henergy
  refine ⟨fun _ => xiEmptySeparatedContinuedCauchyPacket, ?_, ?_, ?_⟩
  · simpa only [xiEmptySeparatedContinuedCauchyPacket_evaluation, hvector] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (0 : lp (fun _ : XiZeroCopy => ℂ) 2)) atTop (nhds 0))
  · simpa only [xiEmptySeparatedContinuedCauchyPacket_sourceEnergy,
      henergy, neg_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · exact Eventually.of_forall fun _ => by
      rw [xiEmptySeparatedContinuedCauchyPacket_sourceEnergy]

/-- Continued-source sequence sign and fixed adjoint-response seam are constructively identical. -/
theorem xiHurwitzContinuedCauchySequenceNonnegative_iff_reciprocalSquareFixedCauchyRealKrylovSeamSaturation :
    XiHurwitzContinuedCauchySequenceNonnegative ↔
      XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation :=
  ⟨xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_of_hurwitzContinuedCauchySequenceNonnegative,
    xiHurwitzContinuedCauchySequenceNonnegative_of_reciprocalSquareFixedCauchyRealKrylovSeamSaturation⟩

/-- Separated finite prime--Gamma sequence sign and fixed adjoint-response seam are likewise
constructively identical. -/
theorem xiHurwitzSeparatedSourceSequenceNonnegative_iff_reciprocalSquareFixedCauchyRealKrylovSeamSaturation :
    XiHurwitzSeparatedSourceSequenceNonnegative ↔
      XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation :=
  ⟨xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_of_hurwitzSeparatedSourceSequenceNonnegative,
    xiHurwitzSeparatedSourceSequenceNonnegative_of_reciprocalSquareFixedCauchyRealKrylovSeamSaturation⟩

end

end RHTower
