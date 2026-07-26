import GaloisForLFunctions.RHTower.SoninProjectionQuantumWalk

/-!
# Sonin projection-walk prolate phase-energy law

The anti-Hermitian phase energy of the two-reflection Sonin walk is exactly the prolate
free-fermion number variance.  Eliminating that variance from the finite-aperture occupation
identity gives a complete walk-phase/prolate-energy conservation law.
-/

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- The central physical/Fourier cutoff commutator is Hilbert--Schmidt at every positive
aperture. -/
private theorem centralCutoffCommutator_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) :
    IsHilbertSchmidt
      (ccmCommutator (centralPhysicalForbidden a).starProjection
        (centralFourierForbidden a).starProjection) := by
  let P : SoninL2 →L[ℂ] SoninL2 := (centralFourierForbidden a).starProjection
  let X : SoninL2 →L[ℂ] SoninL2 := (centralPhysicalForbidden a).starProjection
  let L : SoninL2 →L[ℂ] SoninL2 := crossBoundary P X
  let U : SoninL2 →L[ℂ] SoninL2 := upperBoundary P X
  have hL : IsHilbertSchmidt L := by
    simpa only [L, P, X] using centralProlateTransition_isHilbertSchmidt a ha
  have hAdjL : adjoint L = U := by
    dsimp only [L, U]
    unfold crossBoundary upperBoundary
    change adjoint (((1 - P) * X) ∘L P) = _
    rw [ContinuousLinearMap.adjoint_comp]
    change adjoint P ∘L adjoint ((1 - P) ∘L X) = _
    rw [ContinuousLinearMap.adjoint_comp,
      adjoint_one_sub (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq,
      (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq,
      (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq]
  have hU : IsHilbertSchmidt U := by
    rw [← hAdjL]
    exact hL.adjoint
  have hsplit :
      ccmCommutator (centralPhysicalForbidden a).starProjection
          (centralFourierForbidden a).starProjection = L - U := by
    simpa only [L, U, P, X] using
      ccmCommutator_eq_crossBoundary_sub_upperBoundary
        (centralFourierForbidden a).starProjection
        (centralPhysicalForbidden a).starProjection
  rw [hsplit]
  exact hL.sub hU

/-- **Sonin walk-phase/free-fermion universality law.**  At every positive aperture, squared
Hilbert--Schmidt energy of the walk's anti-Hermitian phase is exactly thirty-two times the
prolate number variance. -/
theorem hsNormSq_centralSoninProjectionQuantumWalk_sub_adjoint_eq
    (a : ℝ) (ha : 0 < a) :
    hsNormSq
        (centralSoninProjectionQuantumWalk a -
          adjoint (centralSoninProjectionQuantumWalk a)) =
      32 * Complex.re
        (opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a)
                (centralFourierForbidden a) -
            soninAlternatingBlock (centralPhysicalForbidden a)
                (centralFourierForbidden a) *
              soninAlternatingBlock (centralPhysicalForbidden a)
                (centralFourierForbidden a))) := by
  let C : SoninL2 →L[ℂ] SoninL2 :=
    ccmCommutator (centralPhysicalForbidden a).starProjection
      (centralFourierForbidden a).starProjection
  have hC : IsHilbertSchmidt C := by
    simpa only [C] using centralCutoffCommutator_isHilbertSchmidt a ha
  have hwalk :
      centralSoninProjectionQuantumWalk a -
          adjoint (centralSoninProjectionQuantumWalk a) =
        (4 : ℂ) • C := by
    simpa only [C, Algebra.smul_def] using
      centralSoninProjectionQuantumWalk_sub_adjoint_eq_four_mul_cutoffCommutator a
  rw [hwalk, hsNormSq_smul_eq hC (4 : ℂ)]
  norm_num
  rw [show hsNormSq C =
      2 * Complex.re
        (opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a)
                (centralFourierForbidden a) -
            soninAlternatingBlock (centralPhysicalForbidden a)
                (centralFourierForbidden a) *
              soninAlternatingBlock (centralPhysicalForbidden a)
                (centralFourierForbidden a))) by
    simpa only [C] using
      hsNormSq_centralCutoffCommutator_eq_two_mul_re_opTrace_prolateImpurity a ha]
  ring

/-- **Finite-aperture Sonin phase/occupation conservation law.**  Walk phase energy plus
thirty-two times retained prolate Hilbert--Schmidt energy is the exact aperture budget
`128 a²`. -/
theorem hsNormSq_centralSoninProjectionQuantumWalk_sub_adjoint_add_prolate_eq
    (a : ℝ) (ha : 0 < a) :
    hsNormSq
          (centralSoninProjectionQuantumWalk a -
            adjoint (centralSoninProjectionQuantumWalk a)) +
        32 * hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) =
      128 * a ^ 2 := by
  have hphase :=
    hsNormSq_centralSoninProjectionQuantumWalk_sub_adjoint_eq a ha
  have hbudget :=
    hsNormSq_centralProlateBlock_add_re_opTrace_impurity_eq_four_mul_sq a ha
  nlinarith

end

end RHTower
