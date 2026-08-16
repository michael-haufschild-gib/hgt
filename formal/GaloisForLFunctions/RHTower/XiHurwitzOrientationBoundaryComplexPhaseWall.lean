import GaloisForLFunctions.RHTower.XiHurwitzOrientationBoundaryMixedIncidence

/-!
# Complex-phase wall for Route-Q boundary fusion

The real boundary plane has only its two coordinate axes as null rays.  Complexifying the two
coefficients enlarges the null cone: the exact energy becomes

`Q(alpha b₊ + beta b₋) = -Re(conj(alpha) beta) E`.

This extra phase freedom does not repair target-aligned fusion.  Every nonnegative complex phase
pair lies at squared coefficient distance at least one from `(1,1)`, equivalently at squared
Hilbert distance at least `E/2` from the orientation vector.  The constant is sharp.  Moreover,
even adaptive phases converging to `(1,1)` force every pair of boundary-packet reconstructions
back into the negative chamber off RH.  Thus phase rotation supplies null and positive comparison
directions, but no cofinal source repair approaching the Route-Q target.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Complex scaling multiplies the real Xi--Weil quadratic by the coefficient norm square. -/
theorem xiWeilHilbertQuadratic_smul_complex (c : ℂ) (v : XiWeilCarrier) :
    xiWeilHilbertQuadratic (c • v) =
      Complex.normSq c * xiWeilHilbertQuadratic v := by
  unfold xiWeilHilbertQuadratic
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.normSq_apply, Complex.mul_re]
  ring

/-- The anti-fixed orientation vector and fixed absolute companion are Hilbert-orthogonal. -/
theorem inner_xiHurwitzOrientationVector_absoluteVector_eq_zero :
    inner ℂ xiHurwitzOrientationVector xiHurwitzOrientationAbsoluteVector = 0 := by
  have h := CliffordWeil.inner_map_left_eq_inner_map_right
    xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive
    xiHurwitzOrientationVector xiHurwitzOrientationAbsoluteVector
  rw [xiWeilLineConjLinearIsometry_apply,
    xiWeilLineConjLp_xiHurwitzOrientationVector,
    xiWeilLineConjLinearIsometry_apply,
    xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector,
    inner_neg_left] at h
  exact neg_eq_self.mp h

/-- Exact Hermitian phase law on the complexified Route-Q boundary plane. -/
theorem xiWeilHilbertQuadratic_boundaryComplexCoordinates (alpha beta : ℂ) :
    xiWeilHilbertQuadratic
        (alpha • xiHurwitzOrientationBoundaryPlus +
          beta • xiHurwitzOrientationBoundaryMinus) =
      -(starRingEnd ℂ alpha * beta).re * xiHurwitzOrientationEnergy := by
  have hdecomp :
      alpha • xiHurwitzOrientationBoundaryPlus +
          beta • xiHurwitzOrientationBoundaryMinus =
        ((alpha + beta) / 2) • xiHurwitzOrientationVector +
          ((alpha - beta) / 2) • xiHurwitzOrientationAbsoluteVector := by
    unfold xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus
    module
  rw [hdecomp]
  have hwa : inner ℂ xiHurwitzOrientationVector
      xiHurwitzOrientationAbsoluteVector = 0 :=
    inner_xiHurwitzOrientationVector_absoluteVector_eq_zero
  rw [xiWeilHilbertQuadratic_add_cross,
    xiWeilHilbertQuadratic_smul_complex,
    xiWeilHilbertQuadratic_smul_complex,
    xiWeilHilbertQuadratic_xiHurwitzOrientationVector]
  have hqabs :
      xiWeilHilbertQuadratic xiHurwitzOrientationAbsoluteVector =
        xiHurwitzOrientationEnergy := by
    unfold xiWeilHilbertQuadratic
    rw [xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector]
    change RCLike.re (inner ℂ xiHurwitzOrientationAbsoluteVector
      xiHurwitzOrientationAbsoluteVector) = _
    rw [inner_self_eq_norm_sq,
      norm_sq_xiHurwitzOrientationAbsoluteVector]
  rw [hqabs]
  have hcross :
      (inner ℂ
        (xiWeilLineConjLinearIsometry
          (((alpha + beta) / 2) • xiHurwitzOrientationVector))
        (((alpha - beta) / 2) • xiHurwitzOrientationAbsoluteVector)).re = 0 := by
    rw [map_smul, xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationVector,
      inner_smul_left, inner_smul_right, inner_neg_left, hwa]
    simp
  rw [hcross]
  simp only [mul_zero, add_zero]
  simp [Complex.normSq_apply, Complex.mul_re]
  ring

/-- Any coefficient pair with nonpositive Hermitian incidence stays one unit from `(1,1)`. -/
theorem one_le_boundaryComplexCoefficient_displacement
    {alpha beta : ℂ} (hphase : (starRingEnd ℂ alpha * beta).re ≤ 0) :
    1 ≤ Complex.normSq (alpha - 1) + Complex.normSq (beta - 1) := by
  have hphase' : alpha.re * beta.re + alpha.im * beta.im ≤ 0 := by
    simpa [Complex.mul_re] using hphase
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith [sq_nonneg (alpha.re + beta.re - 1),
    sq_nonneg (alpha.im + beta.im)]

/-- The unit coefficient-displacement lower bound is attained on a boundary axis. -/
theorem boundaryComplexCoefficient_displacement_sharp :
    (starRingEnd ℂ (0 : ℂ) * 1).re ≤ 0 ∧
      Complex.normSq ((0 : ℂ) - 1) + Complex.normSq ((1 : ℂ) - 1) = 1 := by
  norm_num [Complex.normSq_apply]

/-- The two canonical null boundaries are orthogonal for the positive Hilbert metric. -/
theorem inner_xiHurwitzOrientationBoundaryPlus_boundaryMinus_eq_zero :
    inner ℂ xiHurwitzOrientationBoundaryPlus
      xiHurwitzOrientationBoundaryMinus = 0 := by
  unfold xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus
  have hwa := inner_xiHurwitzOrientationVector_absoluteVector_eq_zero
  have haw : inner ℂ xiHurwitzOrientationAbsoluteVector
      xiHurwitzOrientationVector = 0 := inner_eq_zero_symm.mp hwa
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right,
    hwa, haw, inner_self_eq_norm_sq_to_K]
  rw [norm_xiHurwitzOrientationAbsoluteVector_eq_orientationVector]
  norm_num

/-- Exact Hilbert distance from a complex boundary phase pair to target-aligned fusion. -/
theorem norm_sq_boundaryComplexCoordinates_sub_orientation
    (alpha beta : ℂ) :
    ‖alpha • xiHurwitzOrientationBoundaryPlus +
        beta • xiHurwitzOrientationBoundaryMinus -
        xiHurwitzOrientationVector‖ ^ 2 =
      (Complex.normSq (alpha - 1) + Complex.normSq (beta - 1)) *
        xiHurwitzOrientationEnergy / 2 := by
  have hdiff :
      alpha • xiHurwitzOrientationBoundaryPlus +
          beta • xiHurwitzOrientationBoundaryMinus -
          xiHurwitzOrientationVector =
        (alpha - 1) • xiHurwitzOrientationBoundaryPlus +
          (beta - 1) • xiHurwitzOrientationBoundaryMinus := by
    rw [← xiHurwitzOrientationBoundaryPlus_add_boundaryMinus]
    module
  rw [hdiff, norm_add_sq (𝕜 := ℂ)]
  have hcross :
      RCLike.re (inner ℂ
        ((alpha - 1) • xiHurwitzOrientationBoundaryPlus)
        ((beta - 1) • xiHurwitzOrientationBoundaryMinus)) = 0 := by
    rw [inner_smul_left, inner_smul_right,
      inner_xiHurwitzOrientationBoundaryPlus_boundaryMinus_eq_zero]
    simp
  rw [hcross]
  simp only [mul_zero, add_zero, norm_smul]
  rw [mul_pow, mul_pow, Complex.sq_norm, Complex.sq_norm]
  have hp := two_mul_norm_sq_xiHurwitzOrientationBoundaryPlus
  have hm := two_mul_norm_sq_xiHurwitzOrientationBoundaryMinus
  have hp' : ‖xiHurwitzOrientationBoundaryPlus‖ ^ 2 =
      xiHurwitzOrientationEnergy / 2 := by linarith
  have hm' : ‖xiHurwitzOrientationBoundaryMinus‖ ^ 2 =
      xiHurwitzOrientationEnergy / 2 := by linarith
  rw [hp', hm']
  ring

/-- Off RH, every nonnegative complex boundary fusion obeys the sharp orientation exclusion
radius `E/2`. -/
theorem orientationEnergy_div_two_le_norm_sq_boundaryComplexCoordinates_sub_orientation_of_nonnegative_of_not_rh
    (hnot : ¬ RiemannHypothesis) {alpha beta : ℂ}
    (hnonneg : 0 ≤ xiWeilHilbertQuadratic
      (alpha • xiHurwitzOrientationBoundaryPlus +
        beta • xiHurwitzOrientationBoundaryMinus)) :
    xiHurwitzOrientationEnergy / 2 ≤
      ‖alpha • xiHurwitzOrientationBoundaryPlus +
        beta • xiHurwitzOrientationBoundaryMinus -
        xiHurwitzOrientationVector‖ ^ 2 := by
  rw [norm_sq_boundaryComplexCoordinates_sub_orientation]
  have hEpos : 0 < xiHurwitzOrientationEnergy :=
    xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
  have hphase : (starRingEnd ℂ alpha * beta).re ≤ 0 := by
    rw [xiWeilHilbertQuadratic_boundaryComplexCoordinates] at hnonneg
    nlinarith
  have hdisp := one_le_boundaryComplexCoefficient_displacement hphase
  have hE : 0 ≤ xiHurwitzOrientationEnergy := xiHurwitzOrientationEnergy_nonneg
  nlinarith

/-- Off RH, nonnegative boundary energy is exactly nonpositive Hermitian coefficient incidence. -/
theorem xiWeilHilbertQuadratic_boundaryComplexCoordinates_nonnegative_iff_of_not_rh
    (hnot : ¬ RiemannHypothesis) (alpha beta : ℂ) :
    0 ≤ xiWeilHilbertQuadratic
        (alpha • xiHurwitzOrientationBoundaryPlus +
          beta • xiHurwitzOrientationBoundaryMinus) ↔
      (starRingEnd ℂ alpha * beta).re ≤ 0 := by
  rw [xiWeilHilbertQuadratic_boundaryComplexCoordinates]
  have hE : 0 < xiHurwitzOrientationEnergy :=
    xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
  constructor <;> intro h <;> nlinarith

/-- Source-sign form of the sharp coefficient wall. -/
theorem one_le_boundaryComplexCoefficient_displacement_of_weil_nonnegative_of_not_rh
    (hnot : ¬ RiemannHypothesis) {alpha beta : ℂ}
    (hnonneg : 0 ≤ xiWeilHilbertQuadratic
      (alpha • xiHurwitzOrientationBoundaryPlus +
        beta • xiHurwitzOrientationBoundaryMinus)) :
    1 ≤ Complex.normSq (alpha - 1) + Complex.normSq (beta - 1) := by
  apply one_le_boundaryComplexCoefficient_displacement
  exact (xiWeilHilbertQuadratic_boundaryComplexCoordinates_nonnegative_iff_of_not_rh
    hnot alpha beta).mp hnonneg

/-- Adaptive complex phases approaching target alignment cannot alter the limiting defect. -/
theorem tendsto_xiSeparatedBoundaryPacket_complexPhaseFusionEnergy
    (alpha beta : ℕ → ℂ)
    (halpha : Tendsto alpha atTop (nhds 1))
    (hbeta : Tendsto beta atTop (nhds 1))
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (nhds xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (nhds xiHurwitzOrientationBoundaryMinus)) :
    Tendsto (fun n => xiWeilHilbertQuadratic
      (alpha n • (P n).evaluation + beta n • (Q n).evaluation))
      atTop (nhds (-xiHurwitzOrientationEnergy)) := by
  have hvec := (halpha.smul hP).add (hbeta.smul hQ)
  have henergy :=
    continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hvec
  change Tendsto (fun n => xiWeilHilbertQuadratic
      (alpha n • (P n).evaluation + beta n • (Q n).evaluation))
    atTop (nhds (xiWeilHilbertQuadratic
      ((1 : ℂ) • xiHurwitzOrientationBoundaryPlus +
        (1 : ℂ) • xiHurwitzOrientationBoundaryMinus))) at henergy
  simpa only [one_smul,
    xiHurwitzOrientationBoundaryPlus_add_boundaryMinus,
    xiWeilHilbertQuadratic_xiHurwitzOrientationVector] using henergy

/-- Off RH, every adaptive target-aligned complex-phase packet fusion is eventually negative. -/
theorem eventually_xiSeparatedBoundaryPacket_complexPhaseFusionEnergy_neg_of_not_rh
    (hnot : ¬ RiemannHypothesis)
    (alpha beta : ℕ → ℂ)
    (halpha : Tendsto alpha atTop (nhds 1))
    (hbeta : Tendsto beta atTop (nhds 1))
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (nhds xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (nhds xiHurwitzOrientationBoundaryMinus)) :
    ∀ᶠ n in atTop, xiWeilHilbertQuadratic
      (alpha n • (P n).evaluation + beta n • (Q n).evaluation) < 0 := by
  have hE : 0 < xiHurwitzOrientationEnergy :=
    xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
  exact (tendsto_xiSeparatedBoundaryPacket_complexPhaseFusionEnergy
    alpha beta halpha hbeta P Q hP hQ).eventually
      (Iio_mem_nhds (by linarith))

end

end RHTower
