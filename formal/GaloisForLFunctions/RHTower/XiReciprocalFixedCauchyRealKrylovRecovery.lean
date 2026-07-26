import GaloisForLFunctions.RHTower.XiReciprocalFixedCauchyKrylovCyclicity
import GaloisForLFunctions.RHTower.TraceHankelConverse

/-!
# Real reciprocal-Krylov recovery is equivalent to RH

Complex reciprocal polynomials unconditionally recover fixed adjoint response. Restricting
coefficients to real numbers changes the situation sharply. Every finite real-polynomial response
has exactly zero holomorphic source contrast, because its mixed Cauchy polarization is symmetric.
Therefore norm recovery by real polynomials forces fixed orientation defect to vanish. Conversely,
under RH critical-line reflection is trivial on spectral coordinates and constant polynomial
sequence X^2 recovers response exactly.

This extracts a strict real-form predecessor to fixed source-contrast saturation. No estimate,
simplicity hypothesis, or zero computation is used.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

def xiRealPolynomialToComplex (p : Polynomial ℝ) : Polynomial ℂ :=
  p.map (algebraMap ℝ ℂ)

theorem xiWeilPolarization_cauchy_realReciprocalKrylov_symm
    (z : XiContinuedCauchyPoint) (p : Polynomial ℝ) :
    xiWeilPolarization (xiWeilCauchyTest (z : ℂ))
        (xiReciprocalCauchyKrylovPolynomialTest z (xiRealPolynomialToComplex p)) =
      xiWeilPolarization
        (xiReciprocalCauchyKrylovPolynomialTest z (xiRealPolynomialToComplex p))
        (xiWeilCauchyTest (z : ℂ)) := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  simp only [xiWeilSharp, xiReciprocalCauchyKrylovPolynomialTest,
    xiWeilCauchyTest, xiRealPolynomialToComplex]
  rw [← evalRealPolynomial]
  rw [← evalRealPolynomial]
  simp only [map_mul, map_inv₀, map_sub]
  rw [← evalRealPolynomial_conj]
  simp
  ring

theorem xiReciprocalCauchyRealKrylovSourceContrast_eq_zero
    (z : XiContinuedCauchyPoint) (p : Polynomial ℝ) :
    ((xiWeilPolarization
          (xiReciprocalCauchyKrylovSourcePlusTest z (xiRealPolynomialToComplex p))
          (xiReciprocalCauchyKrylovSourcePlusTest z (xiRealPolynomialToComplex p))).re -
      (xiWeilPolarization
          (xiReciprocalCauchyKrylovSourceMinusTest z (xiRealPolynomialToComplex p))
          (xiReciprocalCauchyKrylovSourceMinusTest z (xiRealPolynomialToComplex p))).re) / 4 = 0 := by
  let f := xiWeilContinuedCauchyLp z
  let htest := xiReciprocalCauchyKrylovPolynomialTest z (xiRealPolynomialToComplex p)
  let g := xiWeilEvaluationLp htest
    (xiReciprocalCauchyKrylovPolynomialTest_squareSummable z (xiRealPolynomialToComplex p))
  have hsym : inner ℂ (xiWeilLineConjLp f) g =
      (starRingEnd ℂ) (inner ℂ (xiWeilLineConjLp g) f) := by
    change inner ℂ
        (xiWeilLineConjLp
          (xiWeilEvaluationLp (xiWeilCauchyTest (z : ℂ))
            (XiWeilSquareSummable_cauchy (z : ℂ))))
        (xiWeilEvaluationLp htest
          (xiReciprocalCauchyKrylovPolynomialTest_squareSummable z
            (xiRealPolynomialToComplex p))) =
      (starRingEnd ℂ) (inner ℂ
        (xiWeilLineConjLp
          (xiWeilEvaluationLp htest
            (xiReciprocalCauchyKrylovPolynomialTest_squareSummable z
              (xiRealPolynomialToComplex p))))
        (xiWeilEvaluationLp (xiWeilCauchyTest (z : ℂ))
          (XiWeilSquareSummable_cauchy (z : ℂ))))
    rw [inner_xiWeilLineConjLp_evaluation_eq_polarization,
      inner_xiWeilLineConjLp_evaluation_eq_polarization,
      xiWeilPolarization_conj_symm]
  have hcross : (inner ℂ (xiWeilLineConjLp g) f).im = 0 := by
    dsimp only [g, f, htest]
    change (inner ℂ
      (xiWeilLineConjLp
        (xiWeilEvaluationLp
          (xiReciprocalCauchyKrylovPolynomialTest z (xiRealPolynomialToComplex p))
          (xiReciprocalCauchyKrylovPolynomialTest_squareSummable z
            (xiRealPolynomialToComplex p))))
      (xiWeilEvaluationLp (xiWeilCauchyTest (z : ℂ))
        (XiWeilSquareSummable_cauchy (z : ℂ)))).im = 0
    rw [inner_xiWeilLineConjLp_evaluation_eq_polarization]
    change (xiWeilPolarization (xiWeilCauchyTest (z : ℂ)) htest).im = 0
    have hconj := xiWeilPolarization_conj_symm
      (xiWeilCauchyTest (z : ℂ)) htest
    rw [← xiWeilPolarization_cauchy_realReciprocalKrylov_symm z p] at hconj
    exact Complex.conj_eq_iff_im.mp hconj.symm
  rw [← xiWeilHilbertQuadratic_evaluation_eq_polarization_re
      (xiReciprocalCauchyKrylovSourcePlusTest z (xiRealPolynomialToComplex p))
      (xiReciprocalCauchyKrylovSourcePlusTest_squareSummable z
        (xiRealPolynomialToComplex p)),
    ← xiWeilHilbertQuadratic_evaluation_eq_polarization_re
      (xiReciprocalCauchyKrylovSourceMinusTest z (xiRealPolynomialToComplex p))
      (xiReciprocalCauchyKrylovSourceMinusTest_squareSummable z
        (xiRealPolynomialToComplex p)),
    xiReciprocalCauchyKrylovSourcePlusTest_evaluation,
    xiReciprocalCauchyKrylovSourceMinusTest_evaluation]
  rw [← xiReciprocalCauchyKrylovPolynomialTest_evaluation z
      (xiRealPolynomialToComplex p)]
  change (xiWeilHilbertQuadratic (f + I • g) -
      xiWeilHilbertQuadratic (f - I • g)) / 4 = 0
  rw [xiWeilHilbertQuadratic_I_polarization_difference f g hsym, hcross]
  ring

def XiReciprocalSquareFixedCauchyRealKrylovResponseRecovery : Prop :=
  ∃ p : ℕ → Polynomial ℝ,
    Tendsto (fun n => xiReciprocalCauchyKrylovPolynomialVector
        xiReciprocalSquareFixedCauchyPole (xiRealPolynomialToComplex (p n))) atTop
      (nhds (xiWeilEvaluationLp
        (xiReciprocalSquareCauchyAdjointResponseTest
          (xiReciprocalSquareFixedCauchyPole : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
          xiReciprocalSquareFixedCauchyPole)))

theorem xiReciprocalSquareFixedCauchyRealKrylov_X_sq_eq_adjointResponse_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    xiReciprocalCauchyKrylovPolynomialVector
        xiReciprocalSquareFixedCauchyPole
        (xiRealPolynomialToComplex (Polynomial.X ^ 2)) =
      xiWeilEvaluationLp
        (xiReciprocalSquareCauchyAdjointResponseTest
          (xiReciprocalSquareFixedCauchyPole : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
          xiReciprocalSquareFixedCauchyPole) := by
  apply Subtype.ext
  funext q
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply,
    xiWeilEvaluationLp_apply]
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  simp [xiRealPolynomialToComplex, xiReciprocalSquareCauchyAdjointResponseTest,
    xiWeilContinuedCauchyLp, xiWeilCauchyLp_apply, xiWeilCauchyTest, ht]

theorem xiReciprocalSquareFixedCauchyRealKrylovResponseRecovery_iff_riemannHypothesis :
    XiReciprocalSquareFixedCauchyRealKrylovResponseRecovery ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨p, hp⟩
    have hdefect :=
      xiReciprocalCauchyKrylovSourceContrast_tendsto_orientationDefect_of_response_tendsto
        xiReciprocalSquareFixedCauchyPole
        (fun n => xiRealPolynomialToComplex (p n)) hp
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds
    have hcontrastZero : Tendsto (fun n =>
        ((xiWeilPolarization
              (xiReciprocalCauchyKrylovSourcePlusTest
                xiReciprocalSquareFixedCauchyPole (xiRealPolynomialToComplex (p n)))
              (xiReciprocalCauchyKrylovSourcePlusTest
                xiReciprocalSquareFixedCauchyPole (xiRealPolynomialToComplex (p n)))).re -
          (xiWeilPolarization
              (xiReciprocalCauchyKrylovSourceMinusTest
                xiReciprocalSquareFixedCauchyPole (xiRealPolynomialToComplex (p n)))
              (xiReciprocalCauchyKrylovSourceMinusTest
                xiReciprocalSquareFixedCauchyPole (xiRealPolynomialToComplex (p n)))).re) / 4)
        atTop (nhds 0) := by
      apply hzero.congr'
      exact Eventually.of_forall fun n =>
        (xiReciprocalCauchyRealKrylovSourceContrast_eq_zero
          xiReciprocalSquareFixedCauchyPole (p n)).symm
    have hD : xiReciprocalSquareContinuedCauchyOrientationDefect
        xiReciprocalSquareFixedCauchyPole = 0 :=
      tendsto_nhds_unique hdefect hcontrastZero
    exact xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.mp hD
  · intro hRH
    refine ⟨fun _ => Polynomial.X ^ 2, ?_⟩
    simpa only [xiReciprocalSquareFixedCauchyRealKrylov_X_sq_eq_adjointResponse_of_riemannHypothesis hRH] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest
            (xiReciprocalSquareFixedCauchyPole : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
            xiReciprocalSquareFixedCauchyPole)) atTop
        (nhds (xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest
            (xiReciprocalSquareFixedCauchyPole : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
            xiReciprocalSquareFixedCauchyPole))))

end

end RHTower

