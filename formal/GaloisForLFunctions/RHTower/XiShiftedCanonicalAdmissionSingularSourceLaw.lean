import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionConnection
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveShearAdjacentDefect

/-!
# Canonical admission source law at a singular shifted-Xi face

The inverse-Hankel admission remains canonical when its next norm reaches a flat face.  This file
identifies its completed adaptive source with the first even Padé defect, then proves that its sign
is exactly the positive-semidefinite extension orientation.  The source is formed from the admitted
mixed amplitude before reflection aggregation; no fixed linear observer occurs.
-/

open Matrix Polynomial

namespace RHTower

noncomputable section

/-- Terminal normalization does nothing to the already monic inverse-Hankel admission. -/
theorem finiteHankelNullMonicPolynomial_monicMomentAdmissionVector
    (s : ℕ → ℝ) (n : ℕ) :
    HTGeometry.finiteHankelNullMonicPolynomial
        (HTGeometry.monicMomentAdmissionVector s n) =
      HTGeometry.monicMomentAdmissionPolynomial s n := by
  rw [HTGeometry.finiteHankelNullMonicPolynomial,
    show HTGeometry.finiteHankelNullPolynomial
        (HTGeometry.monicMomentAdmissionVector s n) =
      HTGeometry.monicMomentAdmissionPolynomial s n from rfl,
    (HTGeometry.monicMomentAdmissionPolynomial_monic s n).leadingCoeff]
  simp

/-- At a tangential flat face, the completed adaptive packet is exactly twice `n+1` times the
first even Padé defect. -/
theorem xiShiftedCompletedMomentAggregate_flatTangent_eq_evenPadeDefect
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (htangent : xiShiftedHankelBoundaryMonicRemainder y c = 0) :
    xiShiftedCompletedMomentAggregate y 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket
            (HTGeometry.finiteHankelNullMonicPolynomial c))) =
      2 * ((n + 1 : ℕ) : ℝ) *
        xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2) := by
  have hzero : ∀ k < 2 * n + (2 * 0 + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    apply xiShiftedHankelBoundaryPadeDefect_eq_zero_of_le c hhead hflat hlast
    omega
  have hadj :=
    xiShiftedCompletedMomentAggregate_adaptiveNullPacket_eq_adjacentDefects
      (m := 0) hy c hlast hzero
  dsimp only at hadj
  have hfirst :=
    xiShiftedHankelBoundaryPadeDefect_first_eq_monicRemainder
      c hhead hflat hlast
  rw [show 2 * n + (2 * 0 + 1) = 2 * n + 1 by omega,
    hfirst, htangent] at hadj
  convert hadj using 1 <;> push_cast <;> ring

/-- **First even source coordinate.**  For actual inverse-Hankel admission, terminal
normalization is already built in.  Hence the source law above is literally a canonical
`P^sharp` law, not a posterior choice of null orientation. -/
theorem xiShiftedCompletedMomentAggregate_canonicalFlatTangent_eq_evenPadeDefect
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (htangent : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) = 0) :
    xiShiftedCompletedMomentAggregate y 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket
            (HTGeometry.monicMomentAdmissionPolynomial
              (fun k => (xiShiftedReciprocalMoment y k).re) n))) =
      2 * ((n + 1 : ℕ) : ℝ) *
        xiShiftedHankelBoundaryPadeDefect y
          (HTGeometry.monicMomentAdmissionVector
            (fun k => (xiShiftedReciprocalMoment y k).re) n) (2 * n + 2) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
  have hlast : c (Fin.last n) ≠ 0 := by simp [c]
  have hsource := xiShiftedCompletedMomentAggregate_flatTangent_eq_evenPadeDefect
    hy c hhead hflat hlast htangent
  rw [finiteHankelNullMonicPolynomial_monicMomentAdmissionVector] at hsource
  exact hsource

/-- **Rank-one filling equivalence.**  Once the odd remainder vanishes, the next principal block
is positive semidefinite exactly when the first even Padé defect is nonnegative.  This closes both
directions of the local boundary classification, not merely the sufficient rank-one filling law. -/
theorem xiShiftedMomentHankelMatrix_succ_posSemidef_iff_evenPadeDefect_nonneg_of_flatTangent
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (htangent : xiShiftedHankelBoundaryMonicRemainder y c = 0) :
    (xiShiftedMomentHankelMatrix y (n + 2)).PosSemidef ↔
      0 ≤ xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2) := by
  have hfirst :=
    xiShiftedHankelBoundaryPadeDefect_first_eq_monicRemainder
      c hhead hflat hlast
  have hzero : ∀ k < 2 * n + 2 * 1,
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    by_cases hvisible : k ≤ 2 * n
    · exact xiShiftedHankelBoundaryPadeDefect_eq_zero_of_le
        c hhead hflat hlast hvisible
    · have hkfirst : k = 2 * n + 1 := by omega
      rw [hkfirst, hfirst, htangent]
  constructor
  · intro hpsd
    have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2
      (xiShiftedHankelBoundaryLiftedNullVector c 1)
    rw [star_trivial, xiShiftedMomentHankelMatrix,
      GaloisForLFunctions.HTGeometry.finiteHankelMatrix,
      HTGeometry.dotProduct_mulVec_momentHankelMatrix,
      ofFn_xiShiftedHankelBoundaryLiftedNullVector c hlast] at hquad
    rw [xiShiftedHankelBoundaryPadeDefect_first_even_eq_liftedSquare
      c hlast (by omega : 0 < 1) hzero]
    exact hquad
  · intro hnonneg
    exact xiShiftedMomentHankelMatrix_posSemidef_rankOneFilled_of_even_contact
      c hhead hflat hlast hzero hnonneg

/-- **Admission-sensitive extension classifier.**  At a canonical tangential flat face, sign of
the completed adaptive `P^sharp` packet is equivalent to survival of the next PSD Hankel block.
This is a nonlinear source law because admission occurs before packet formation. -/
theorem xiShiftedCanonicalAdmission_succ_posSemidef_iff_completedSource_nonneg_of_flatTangent
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ}
    (hhead : (xiShiftedMomentHankelMatrix (w ^ 2) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n = 0)
    (htangent : xiShiftedHankelBoundaryMonicRemainder (w ^ 2)
      (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n) = 0) :
    (xiShiftedMomentHankelMatrix (w ^ 2) (n + 2)).PosSemidef ↔
      0 ≤ xiShiftedCompletedMomentAggregate (w ^ 2) 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n))) := by
  let c := HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n
  have hlast : c (Fin.last n) ≠ 0 := by simp [c]
  have hface :=
    xiShiftedMomentHankelMatrix_succ_posSemidef_iff_evenPadeDefect_nonneg_of_flatTangent
      c hhead hflat hlast htangent
  have hy : 0 < w ^ 2 := sq_pos_of_pos (by linarith : 0 < w)
  have hsource :=
    xiShiftedCompletedMomentAggregate_canonicalFlatTangent_eq_evenPadeDefect
      hy hhead hflat htangent
  change xiShiftedCompletedMomentAggregate (w ^ 2) 2
      (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
        (xiShiftedOddCrossingCoefficientPacket
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n))) =
    2 * ((n + 1 : ℕ) : ℝ) *
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + 2) at hsource
  rw [hface, hsource]
  have hfactor : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
  exact (mul_nonneg_iff_of_pos_left hfactor).symm

/-- **Norm-flux acceleration law.**  At canonical tangency, the actual division-free admission
norm flux accelerates by the explicit positive combinatorial factor times the first even Padé
defect.  This is the Schur-complement boundary acceleration without dividing by the vanishing
norm. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_evenPadeDefect_of_flatTangent
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ 2) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n = 0)
    (htangent : xiShiftedHankelBoundaryMonicRemainder (w ^ 2)
      (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n) = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNormFlux v n)
      (2 * ((2 * n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
        xiShiftedHankelBoundaryPadeDefect (w ^ 2)
          (HTGeometry.monicMomentAdmissionVector
            (xiShiftedRealMomentSequence w) n) (2 * n + 2)) (w ^ 2) := by
  have hflux :=
    hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_completedAggregate_of_flatTangent
      hw hn hhead hflat htangent
  dsimp only at hflux
  simp only [xiShiftedRealMomentSequence] at hflux
  have hy : 0 < w ^ 2 := sq_pos_of_pos (by linarith : 0 < w)
  have hsource :=
    xiShiftedCompletedMomentAggregate_canonicalFlatTangent_eq_evenPadeDefect
      hy hhead hflat htangent
  change xiShiftedCompletedMomentAggregate (w ^ 2) 2
      (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
        (xiShiftedOddCrossingCoefficientPacket
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n))) =
    2 * ((n + 1 : ℕ) : ℝ) *
      xiShiftedHankelBoundaryPadeDefect (w ^ 2)
        (HTGeometry.monicMomentAdmissionVector
          (xiShiftedRealMomentSequence w) n) (2 * n + 2) at hsource
  rw [hsource] at hflux
  refine hflux.congr_deriv ?_
  ring

end

end RHTower
