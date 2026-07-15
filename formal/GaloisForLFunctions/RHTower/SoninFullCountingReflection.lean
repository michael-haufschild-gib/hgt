/-
# Full-counting reflection for the central Sonin pair

The central prolate compression and the zero-mode-subtracted exterior compression are the two
positive Hamiltonians of the concrete two-projection supersymmetry.  The existing Sonin theory
proves equality of their Hilbert--Schmidt energies and a telescoping invariant for all power
traces.  Self-adjointness identifies the degree-two trace with that energy, so the invariant
vanishes and every trace coordinate from degree two onward agrees.

Consequently the two coordinate-free Hilbert--Carleman determinant germs agree.  This is the
operator-theoretic full-counting statement available without importing an unformalized entire
Fredholm-product construction.
-/
import GaloisForLFunctions.HTGeometry.OperatorFredholmGerm
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

noncomputable section

namespace RHTower

open ContinuousLinearMap

/-- The central prolate compression is self-adjoint. -/
theorem adjoint_centralSoninAlternatingBlock (a : ℝ) :
    ContinuousLinearMap.adjoint
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a)) =
      soninAlternatingBlock (centralPhysicalForbidden a)
        (centralFourierForbidden a) := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection B).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection A).star_eq
  simpa only [A, B, P, R, soninAlternatingBlock,
    HTGeometry.twoProjectionInteriorCompression] using
    HTGeometry.adjoint_twoProjectionInteriorCompression P R hPadj hRadj

/-- The common-zero-mode-subtracted exterior compression is self-adjoint. -/
theorem adjoint_centralSoninExteriorCompression (a : ℝ) :
    ContinuousLinearMap.adjoint (centralSoninExteriorCompression a) =
      centralSoninExteriorCompression a := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection B).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection A).star_eq
  have hQadj : ContinuousLinearMap.adjoint Q = Q := by
    dsimp only [Q, centralSoninProjection, centralSoninCarrier]
    exact (isSelfAdjoint_starProjection (Aᵮ ⊓ Bᵮ)).star_eq
  simpa only [A, B, P, R, Q, centralSoninExteriorCompression] using
    HTGeometry.adjoint_twoProjectionExteriorCompression P R Q hPadj hRadj hQadj

/-- The degree-two trace coordinates of the interior and exterior Sonin Hamiltonians agree
exactly, including their imaginary parts. -/
theorem opTrace_centralSoninAlternatingBlock_sq_eq_exteriorCompression_sq
    (a : ℝ) (ha : 0 < a) :
    opTrace
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a) ^ 2) =
      opTrace (centralSoninExteriorCompression a ^ 2) := by
  let A : SoninL2 →L[ℂ] SoninL2 :=
    soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a)
  let E : SoninL2 →L[ℂ] SoninL2 := centralSoninExteriorCompression a
  have hA : IsHilbertSchmidt A := by
    simpa only [A] using centralSoninAlternatingBlock_isHilbertSchmidt a ha
  have hE : IsHilbertSchmidt E := by
    simpa only [E] using centralSoninExteriorCompression_isHilbertSchmidt a ha
  have hAadj : ContinuousLinearMap.adjoint A = A := by
    simpa only [A] using adjoint_centralSoninAlternatingBlock a
  have hEadj : ContinuousLinearMap.adjoint E = E := by
    simpa only [E] using adjoint_centralSoninExteriorCompression a
  change opTrace (A ^ 2) = opTrace (E ^ 2)
  rw [HTGeometry.opTrace_sq_eq_ofReal_hsNormSq hA hAadj,
    HTGeometry.opTrace_sq_eq_ofReal_hsNormSq hE hEadj]
  exact congrArg (fun x : ℝ => (x : ℂ))
    (hsNormSq_centralSoninExteriorCompression_eq_prolateBlock a ha).symm

/-- **All Sonin full-counting moments from degree two.**  The telescoping Witten invariant has
zero degree-two value, hence every higher power trace agrees. -/
theorem opTrace_centralSoninAlternatingBlock_pow_add_two_eq_exteriorCompression_pow_add_two
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    opTrace
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a) ^ (n + 2)) =
      opTrace (centralSoninExteriorCompression a ^ (n + 2)) := by
  have hinvariant :=
    opTrace_centralProlate_sq_sub_exteriorCompression_sq_eq_power_sub_power a ha n
  rw [opTrace_centralSoninAlternatingBlock_sq_eq_exteriorCompression_sq a ha,
    sub_self] at hinvariant
  exact sub_eq_zero.mp hinvariant.symm

/-- **Regularized Sonin full-counting reflection.**  The interior and zero-mode-subtracted
exterior Hilbert--Carleman determinant germs agree in every complex parameter. -/
theorem centralSoninFullCountingDet2Germ_eq
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    HTGeometry.operatorFredholmDet2Germ
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a)) z =
      HTGeometry.operatorFredholmDet2Germ
        (centralSoninExteriorCompression a) z := by
  exact HTGeometry.operatorFredholmDet2Germ_eq_of_powerTrace_eq
    (opTrace_centralSoninAlternatingBlock_pow_add_two_eq_exteriorCompression_pow_add_two a ha) z

end RHTower
