import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexCompactAngularPhaseReversal
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdjacentEdgeArithmeticAction

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Homogeneous projective Wronskian of two adjacent shifted-Xi characteristic-apex
coordinates. Unlike the affine ratio, this quantity is defined at both coordinate axes. -/
def xiShiftedCanonicalAdmissionApexProjectiveWronskian (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionApexValue y (n + 1) * deriv
      (fun v => xiShiftedCanonicalAdmissionApexValue v n) y -
    xiShiftedCanonicalAdmissionApexValue y n * deriv
      (fun v => xiShiftedCanonicalAdmissionApexValue v (n + 1)) y

/-- The characteristic-apex coordinates obey the literal shifted-Xi Jacobi recurrence in the
degree variable. -/
theorem xiShiftedCanonicalAdmissionApexValue_succ_succ_eq_jacobiRenewal
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 4)).PosDef) :
    xiShiftedCanonicalAdmissionApexValue y (n + 2) =
      (y⁻¹ - xiShiftedCanonicalAdmissionAlpha y (n + 1)) *
          xiShiftedCanonicalAdmissionApexValue y (n + 1) -
        xiShiftedCanonicalAdmissionAdjacentEdge y (n + 1) *
          xiShiftedCanonicalAdmissionApexValue y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hHn : (HTGeometry.momentHankelMatrix s (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHnext : (HTGeometry.momentHankelMatrix s ((n + 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHnext2 : (HTGeometry.momentHankelMatrix s ((n + 2) + 2)).PosDef := by
    simpa only [s, Nat.add_assoc] using hH
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hrec := congrArg (fun p : Polynomial ℝ => p.eval y⁻¹)
    (HTGeometry.X_mul_monicOrtho_below hbelow
      (n := n + 1) (by omega : n + 1 + 1 ≤ n + 4))
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul] at hrec
  rw [xiShiftedCanonicalAdmissionApexValue,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHnext2,
    xiShiftedCanonicalAdmissionApexValue,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHnext,
    xiShiftedCanonicalAdmissionApexValue,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHn,
    xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha hHnext,
    xiShiftedCanonicalAdmissionAdjacentEdge_eq_monicOrthoBeta (by omega) hHnext]
  rw [show n + 1 - 1 = n by omega] at hrec
  linarith

/-- Exact degree-renewal law for the homogeneous projective Wronskian. The curvature source is
the motion of the two literal shifted-Xi Jacobi coefficients. -/
theorem xiShiftedCanonicalAdmissionApexProjectiveWronskian_degreeRenewal
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 4)).PosDef) :
    xiShiftedCanonicalAdmissionApexProjectiveWronskian y (n + 1) =
      xiShiftedCanonicalAdmissionAdjacentEdge y (n + 1) *
          xiShiftedCanonicalAdmissionApexProjectiveWronskian y n +
        deriv (fun v => xiShiftedCanonicalAdmissionAdjacentEdge v (n + 1)) y *
          xiShiftedCanonicalAdmissionApexValue y n *
          xiShiftedCanonicalAdmissionApexValue y (n + 1) +
        (y⁻¹ ^ 2 + deriv
          (fun v => xiShiftedCanonicalAdmissionAlpha v (n + 1)) y) *
          xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ 2 := by
  let A0 : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionApexValue v n
  let A1 : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionApexValue v (n + 1)
  let A2 : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionApexValue v (n + 2)
  let alpha : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionAlpha v (n + 1)
  let beta : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionAdjacentEdge v (n + 1)
  have hH0 : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hH1 : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n + 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hA0 := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_next hy hn hH0
  have hA1 := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_next
    (n := n + 1) hy (by omega) hH1
  have hAlpha := hasDerivAt_xiShiftedCanonicalAdmissionAlpha_eq_sourceConnection
    (n := n + 1) hy (by omega) hH1
  have hN0 := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow
    (n := n) hy hn hH0
  have hN1 := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow
    (n := n + 1) hy (by omega) hH1
  have hN0pos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH0]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH0) (by omega)
  have hBeta : DifferentiableAt ℝ beta y := by
    change DifferentiableAt ℝ (fun v =>
      xiShiftedCanonicalAdmissionNorm v (n + 1) /
        xiShiftedCanonicalAdmissionNorm v n) y
    exact (hN1.div hN0 hN0pos.ne').differentiableAt
  have hInv : HasDerivAt (fun v : ℝ => v⁻¹) (-(y ^ 2)⁻¹) y :=
    hasDerivAt_inv hy.ne'
  have hAlpha' : HasDerivAt alpha (deriv alpha y) y :=
    hAlpha.differentiableAt.hasDerivAt
  have hA0' : HasDerivAt A0 (deriv A0 y) y :=
    hA0.differentiableAt.hasDerivAt
  have hA1' : HasDerivAt A1 (deriv A1 y) y :=
    hA1.differentiableAt.hasDerivAt
  have hRhs : HasDerivAt (fun v => (v⁻¹ - alpha v) * A1 v - beta v * A0 v)
      ((-(y ^ 2)⁻¹ - deriv alpha y) * A1 y +
          (y⁻¹ - alpha y) * deriv A1 y -
        (deriv beta y * A0 y + beta y * deriv A0 y)) y := by
    change HasDerivAt
      (((fun v : ℝ => v⁻¹) - alpha) * A1 - beta * A0)
      ((-(y ^ 2)⁻¹ - deriv alpha y) * A1 y +
          (y⁻¹ - alpha y) * deriv A1 y -
        (deriv beta y * A0 y + beta y * deriv A0 y)) y
    exact ((hInv.sub hAlpha').mul hA1').sub (hBeta.hasDerivAt.mul hA0')
  have hsub : Tendsto (fun v : ℝ => v - y) (nhds y) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr tendsto_id
  have hchamber0 := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hH
  have hchamber : ∀ᶠ v in nhds y,
      (xiShiftedMomentHankelMatrix v (n + 4)).PosDef := by
    filter_upwards [hsub.eventually hchamber0] with v hv
    simpa only [add_sub_cancel] using hv
  have hrecEvent : A2 =ᶠ[nhds y]
      (fun v => (v⁻¹ - alpha v) * A1 v - beta v * A0 v) := by
    filter_upwards [hchamber] with v hv
    exact xiShiftedCanonicalAdmissionApexValue_succ_succ_eq_jacobiRenewal hv
  have hA2' : HasDerivAt A2
      ((-(y ^ 2)⁻¹ - deriv alpha y) * A1 y +
          (y⁻¹ - alpha y) * deriv A1 y -
        (deriv beta y * A0 y + beta y * deriv A0 y)) y :=
    hRhs.congr_of_eventuallyEq hrecEvent
  have hrec := xiShiftedCanonicalAdmissionApexValue_succ_succ_eq_jacobiRenewal hH
  have hrec' : A2 y = (y⁻¹ - alpha y) * A1 y - beta y * A0 y := by
    simpa only [A0, A1, A2, alpha, beta] using hrec
  change A2 y * deriv A1 y - A1 y * deriv A2 y =
    beta y * (A1 y * deriv A0 y - A0 y * deriv A1 y) +
      deriv beta y * A0 y * A1 y +
      (y⁻¹ ^ 2 + deriv alpha y) * A1 y ^ 2
  rw [hrec', hA2'.deriv]
  field_simp [hy.ne']
  ring

end
end RHTower
