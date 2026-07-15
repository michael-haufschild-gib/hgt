/-
# Full-counting reflection for the central Sonin pair

The central prolate compression and the zero-mode-subtracted exterior compression are the two
positive Hamiltonians of the concrete two-projection supersymmetry.  The existing Sonin theory
proves equality of their Hilbert--Schmidt energies and a telescoping invariant for all power
traces.  Self-adjointness identifies the degree-two trace with that energy, so the invariant
vanishes and every trace coordinate from degree two onward agrees.

Consequently the two coordinate-free Hilbert--Carleman determinant germs agree.  Factoring both
compressions as positive energies of concrete Hilbert--Schmidt overlaps also supplies their
degree-one traces, so the degree-one-corrected Fredholm germs agree as well.  These are local
operator-theoretic full-counting statements; no unformalized entire Fredholm-product construction
is imported.
-/
import GaloisForLFunctions.HTGeometry.OperatorFredholmGerm
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

noncomputable section

namespace RHTower

open ContinuousLinearMap

private theorem adjoint_sub_soninFullCounting
    (S T : SoninL2 →L[ℂ] SoninL2) :
    ContinuousLinearMap.adjoint (S - T) =
      ContinuousLinearMap.adjoint S - ContinuousLinearMap.adjoint T := by
  let adj : (SoninL2 →L[ℂ] SoninL2) ≃ₗᵢ⋆[ℂ] (SoninL2 →L[ℂ] SoninL2) :=
    ContinuousLinearMap.adjoint
  exact adj.map_sub S T

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
    exact (isSelfAdjoint_starProjection (A.orthogonal ⊓ B.orthogonal)).star_eq
  simpa only [A, B, P, R, Q, centralSoninExteriorCompression] using
    HTGeometry.adjoint_twoProjectionExteriorCompression P R Q hPadj hRadj hQadj

/-- The central prolate compression is the positive energy of the physical-to-Fourier overlap.
This supplies a concrete trace-class factorization, not merely Hilbert--Schmidt membership. -/
theorem adjoint_centralPhysicalFourierOverlap_mul_self_eq_alternatingBlock (a : ℝ) :
    ContinuousLinearMap.adjoint
          ((centralPhysicalForbidden a).starProjection *
            (centralFourierForbidden a).starProjection) *
        ((centralPhysicalForbidden a).starProjection *
          (centralFourierForbidden a).starProjection) =
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
  have hRR : R * R = R := A.isIdempotentElem_starProjection
  have hAdj : ContinuousLinearMap.adjoint (R * P) = P * R := by
    change ContinuousLinearMap.adjoint (R ∘L P) = P ∘L R
    rw [ContinuousLinearMap.adjoint_comp, hPadj, hRadj]
  change ContinuousLinearMap.adjoint (R * P) * (R * P) = P * R * P
  rw [hAdj]
  noncomm_ring [hRR]

/-- The zero-mode-subtracted exterior compression is likewise a positive Hilbert--Schmidt
energy.  The removed common mode is exactly what makes the exterior overlap square to `E` rather
than to the uncorrected complementary compression. -/
theorem centralSoninExteriorOverlap_mul_adjoint_eq_exteriorCompression (a : ℝ) :
    centralSoninExteriorOverlap a *
        ContinuousLinearMap.adjoint (centralSoninExteriorOverlap a) =
      centralSoninExteriorCompression a := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  let Z : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  have hPP : P * P = P := B.isIdempotentElem_starProjection
  have hRR : R * R = R := A.isIdempotentElem_starProjection
  have hZZ : Z * Z = Z := by
    dsimp only [Z, centralSoninProjection, centralSoninCarrier]
    exact (A.orthogonal ⊓ B.orthogonal).isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection B).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection A).star_eq
  have hZadj : ContinuousLinearMap.adjoint Z = Z := by
    dsimp only [Z, centralSoninProjection, centralSoninCarrier]
    exact (isSelfAdjoint_starProjection (A.orthogonal ⊓ B.orthogonal)).star_eq
  have hPZ : P * Z = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change B.starProjection ((A.orthogonal ⊓ B.orthogonal).starProjection x) = 0
    apply B.starProjection_apply_eq_zero_iff.mpr
    exact ((A.orthogonal ⊓ B.orthogonal).starProjection_apply_mem x).2
  have hZP : Z * P = 0 := by
    calc
      Z * P = ContinuousLinearMap.adjoint (P * Z) := by
        change Z ∘L P = ContinuousLinearMap.adjoint (P ∘L Z)
        rw [ContinuousLinearMap.adjoint_comp, hZadj, hPadj]
      _ = 0 := by rw [hPZ]; simp
  have hRZ : R * Z = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change A.starProjection ((A.orthogonal ⊓ B.orthogonal).starProjection x) = 0
    apply A.starProjection_apply_eq_zero_iff.mpr
    exact ((A.orthogonal ⊓ B.orthogonal).starProjection_apply_mem x).1
  have hZR : Z * R = 0 := by
    calc
      Z * R = ContinuousLinearMap.adjoint (R * Z) := by
        change Z ∘L R = ContinuousLinearMap.adjoint (R ∘L Z)
        rw [ContinuousLinearMap.adjoint_comp, hZadj, hRadj]
      _ = 0 := by rw [hRZ]; simp
  have hAdj :
      ContinuousLinearMap.adjoint
          (HTGeometry.twoProjectionExteriorOverlap R P Z) =
        (1 - P) * (1 - R) - Z := by
    rw [HTGeometry.twoProjectionExteriorOverlap,
      adjoint_sub_soninFullCounting]
    change ContinuousLinearMap.adjoint (((1 - P) ∘L (1 - R))) -
        ContinuousLinearMap.adjoint Z = _
    rw [ContinuousLinearMap.adjoint_comp, adjoint_one_sub hRadj,
      adjoint_one_sub hPadj, hZadj]
  change HTGeometry.twoProjectionExteriorOverlap R P Z *
      ContinuousLinearMap.adjoint
        (HTGeometry.twoProjectionExteriorOverlap R P Z) =
        HTGeometry.twoProjectionExteriorCompression P R Z
  rw [hAdj, HTGeometry.twoProjectionExteriorOverlap,
    HTGeometry.twoProjectionExteriorCompression]
  noncomm_ring [hPP, hRR, hZZ, hPZ, hZP, hRZ, hZR]

/-- Both Sonin full-counting Hamiltonians are trace class by their explicit positive
Hilbert--Schmidt factorizations. -/
theorem centralSoninFullCounting_pair_isTraceClass (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsTraceClass
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a)) ∧
      ContinuousLinearMap.IsTraceClass (centralSoninExteriorCompression a) := by
  have hInterior : IsHilbertSchmidt
      ((centralPhysicalForbidden a).starProjection *
        (centralFourierForbidden a).starProjection) := by
    simpa only [centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      isHilbertSchmidt_indicatorCutoff_fourierCutoff_central a a ha
  have hExterior := centralSoninExteriorOverlap_isHilbertSchmidt a ha
  constructor
  · rw [← adjoint_centralPhysicalFourierOverlap_mul_self_eq_alternatingBlock a]
    exact hInterior.adjoint_comp_self_isTraceClass
  · rw [← centralSoninExteriorOverlap_mul_adjoint_eq_exteriorCompression a]
    exact hExterior.comp_isTraceClass hExterior.adjoint

/-- **Degree-one Sonin trace reflection.**  Both positive compressions have the exact Shannon
trace `4a²`; hence the full-counting reflection includes the previously missing first moment. -/
theorem opTrace_centralSoninAlternatingBlock_eq_exteriorCompression
    (a : ℝ) (ha : 0 < a) :
    opTrace
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a)) =
      opTrace (centralSoninExteriorCompression a) := by
  let S : SoninL2 →L[ℂ] SoninL2 :=
    (centralPhysicalForbidden a).starProjection *
      (centralFourierForbidden a).starProjection
  let D : SoninL2 →L[ℂ] SoninL2 :=
    ContinuousLinearMap.adjoint (centralSoninExteriorOverlap a)
  have hS : IsHilbertSchmidt S := by
    simpa only [S, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      isHilbertSchmidt_indicatorCutoff_fourierCutoff_central a a ha
  have hD : IsHilbertSchmidt D := by
    simpa only [D] using
      (centralSoninExteriorOverlap_isHilbertSchmidt a ha).adjoint
  have hSadj : ContinuousLinearMap.adjoint S =
      (centralFourierForbidden a).starProjection *
        (centralPhysicalForbidden a).starProjection := by
    change ContinuousLinearMap.adjoint
        ((centralPhysicalForbidden a).starProjection ∘L
          (centralFourierForbidden a).starProjection) = _
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq,
      (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq]
  have hSnorm : hsNormSq S = 4 * a ^ 2 := by
    calc
      hsNormSq S = hsNormSq (ContinuousLinearMap.adjoint S) :=
        hS.hsNormSq_adjoint.symm
      _ = hsNormSq
          ((centralFourierForbidden a).starProjection *
            (centralPhysicalForbidden a).starProjection) := by rw [hSadj]
      _ = 4 * a ^ 2 := hsNormSq_centralTimeBandOverlap_eq_four_mul_sq a ha
  have hDnorm : hsNormSq D = 4 * a ^ 2 := by
    rw [D, (centralSoninExteriorOverlap_isHilbertSchmidt a ha).hsNormSq_adjoint]
    exact hsNormSq_centralSoninExteriorOverlap_eq_four_mul_sq a ha
  calc
    opTrace
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a)) =
        opTrace (ContinuousLinearMap.adjoint S ∘L S) := by
          rw [adjoint_centralPhysicalFourierOverlap_mul_self_eq_alternatingBlock]
    _ = hsInner S S := opTrace_adjoint_comp_self S
    _ = (hsNormSq S : ℂ) := HTGeometry.hsInner_self_eq_ofReal_hsNormSq hS
    _ = (hsNormSq D : ℂ) := by rw [hSnorm, hDnorm]
    _ = hsInner D D := (HTGeometry.hsInner_self_eq_ofReal_hsNormSq hD).symm
    _ = opTrace (ContinuousLinearMap.adjoint D ∘L D) :=
      (opTrace_adjoint_comp_self D).symm
    _ = opTrace (centralSoninExteriorCompression a) := by
      rw [D, ContinuousLinearMap.adjoint_adjoint,
        centralSoninExteriorOverlap_mul_adjoint_eq_exteriorCompression]

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

/-- **Ordinary Sonin full-counting germ reflection.**  The explicit positive-energy
factorizations close the degree-one trace, so the interior and exterior degree-one-corrected
Fredholm germs agree, not only their Hilbert--Carleman regularizations. -/
theorem centralSoninFullCountingDet1Germ_eq
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    HTGeometry.operatorFredholmDet1Germ
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a)) z =
      HTGeometry.operatorFredholmDet1Germ
        (centralSoninExteriorCompression a) z := by
  exact HTGeometry.operatorFredholmDet1Germ_eq_of_trace_eq
    (opTrace_centralSoninAlternatingBlock_eq_exteriorCompression a ha)
    (opTrace_centralSoninAlternatingBlock_pow_add_two_eq_exteriorCompression_pow_add_two a ha) z

end RHTower
