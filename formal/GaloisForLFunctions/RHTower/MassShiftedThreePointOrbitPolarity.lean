import GaloisForLFunctions.RHTower.SquaredXiThreePointOrbitPositivity
import GaloisForLFunctions.RHTower.XiSquaredEulerApertureHilbertCorrelation
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# Separated-point positivity and confluent negativity of an actual Xi orbit

Every multiplicity copy of an actual Xi zero lies in the protected three-point chamber
`t > 2`, `0 ≤ q ≤ t + 1/4` of the paired log-derivative response, so its diameter-two orbit
matrix is positive definite.  The same orbit has strictly negative first confluent
derivative-Hankel minor as soon as it is off the critical line.

The two facts are computed from one and the same reciprocal-square coordinate
`λ = -((ρ - 1/2)⁻¹)²`, whose real part is exactly the `(0,0)` entry of the orbit matrix.  Hence
separated-point positivity has the wrong polarization to orient the mass-shifted boundary: it
cannot pay the transverse charge that the confluent minor exposes.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Chamber coordinates of an actual Xi orbit -/

/-- Transverse square `u = (Re ρ - 1/2)²` of an Xi orbit. -/
def xiOrbitTransverse (q : XiZeroCopy) : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2

/-- Height square `v = (Im ρ)²` of an Xi orbit. -/
def xiOrbitHeight (q : XiZeroCopy) : ℝ := ((q.1 : ℂ).im) ^ 2

/-- Shear `(Re ρ - 1/2)(Im ρ)` of an Xi orbit. -/
def xiOrbitShear (q : XiZeroCopy) : ℝ := ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im

/-- Detuning `t = v - u` of an Xi orbit. -/
def xiOrbitDetuning (q : XiZeroCopy) : ℝ := xiOrbitHeight q - xiOrbitTransverse q

/-- Coupling `c = 4uv` of an Xi orbit. -/
def xiOrbitCoupling (q : XiZeroCopy) : ℝ := 4 * xiOrbitTransverse q * xiOrbitHeight q

theorem xiOrbitTransverse_nonneg (q : XiZeroCopy) : 0 ≤ xiOrbitTransverse q :=
  sq_nonneg _

theorem xiOrbitHeight_nonneg (q : XiZeroCopy) : 0 ≤ xiOrbitHeight q :=
  sq_nonneg _

/-- The coupling is four times the squared shear. -/
theorem xiOrbitCoupling_eq_four_mul_shear_sq (q : XiZeroCopy) :
    xiOrbitCoupling q = 4 * xiOrbitShear q ^ 2 := by
  unfold xiOrbitCoupling xiOrbitTransverse xiOrbitHeight xiOrbitShear
  ring

/-- The critical strip bounds the transverse square below `1/4`. -/
theorem xiOrbitTransverse_lt_quarter (q : XiZeroCopy) :
    xiOrbitTransverse q < 1 / 4 :=
  xi_divisor_support_centered_re_sq_lt_quarter q.1

/-- The endpoint-source height gap puts every orbit above squared height `41/2`. -/
theorem fortyOne_div_two_lt_xiOrbitHeight (q : XiZeroCopy) :
    (41 / 2 : ℝ) < xiOrbitHeight q :=
  xiZeroCopy_fortyOne_div_two_lt_im_sq q

/-- Every actual Xi orbit is strongly detuned. -/
theorem two_lt_xiOrbitDetuning (q : XiZeroCopy) : 2 < xiOrbitDetuning q := by
  have hu := xiOrbitTransverse_lt_quarter q
  have hv := fortyOne_div_two_lt_xiOrbitHeight q
  unfold xiOrbitDetuning
  linarith

theorem xiOrbitCoupling_nonneg (q : XiZeroCopy) : 0 ≤ xiOrbitCoupling q := by
  rw [xiOrbitCoupling_eq_four_mul_shear_sq]
  positivity

/-- The exact chamber factorization `(t + 1/4) - c = (1 - 4u)(v + 1/4)`. -/
theorem xiOrbitDetuning_add_quarter_sub_coupling (q : XiZeroCopy) :
    xiOrbitDetuning q + 1 / 4 - xiOrbitCoupling q =
      (1 - 4 * xiOrbitTransverse q) * (xiOrbitHeight q + 1 / 4) := by
  unfold xiOrbitDetuning xiOrbitCoupling
  ring

/-- Every actual Xi orbit lies strictly inside the protected coupling chamber. -/
theorem xiOrbitCoupling_lt_detuning_add_quarter (q : XiZeroCopy) :
    xiOrbitCoupling q < xiOrbitDetuning q + 1 / 4 := by
  have hfac := xiOrbitDetuning_add_quarter_sub_coupling q
  have hu := xiOrbitTransverse_lt_quarter q
  have hv := fortyOne_div_two_lt_xiOrbitHeight q
  nlinarith [hfac]

/-- **Actual-Xi chamber specialization.**  Every multiplicity copy of every Xi zero has a
positive definite diameter-two three-point orbit matrix. -/
theorem xiOrbitMatrix_posDef (q : XiZeroCopy) :
    Matrix.PosDef (orbitMatrix (xiOrbitDetuning q) (xiOrbitCoupling q)) :=
  orbitMatrix_posDef (two_lt_xiOrbitDetuning q) (xiOrbitCoupling_nonneg q)
    (xiOrbitCoupling_lt_detuning_add_quarter q).le

theorem xiOrbitMatrix_det_pos (q : XiZeroCopy) :
    0 < (orbitMatrix (xiOrbitDetuning q) (xiOrbitCoupling q)).det :=
  (xiOrbitMatrix_posDef q).det_pos

/-! ## The chamber coordinates compute the reciprocal-square atom -/

theorem xiOrbit_normSq_centered (q : XiZeroCopy) :
    Complex.normSq ((q.1 : ℂ) - 1 / 2) = xiOrbitTransverse q + xiOrbitHeight q := by
  unfold xiOrbitTransverse xiOrbitHeight
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem xiOrbit_normSq_centered_pos (q : XiZeroCopy) :
    0 < xiOrbitTransverse q + xiOrbitHeight q := by
  rw [← xiOrbit_normSq_centered]
  refine Complex.normSq_pos.mpr ?_
  exact sub_ne_zero.mpr (xi_divisor_support_ne_half q.1)

/-- The chamber radius: `t² + c = (u + v)²`. -/
theorem xiOrbitDetuning_sq_add_coupling (q : XiZeroCopy) :
    xiOrbitDetuning q ^ 2 + xiOrbitCoupling q =
      (xiOrbitTransverse q + xiOrbitHeight q) ^ 2 := by
  unfold xiOrbitDetuning xiOrbitCoupling
  ring

theorem xiOrbitDetuning_sq_add_coupling_pos (q : XiZeroCopy) :
    0 < xiOrbitDetuning q ^ 2 + xiOrbitCoupling q := by
  rw [xiOrbitDetuning_sq_add_coupling]
  exact pow_pos (xiOrbit_normSq_centered_pos q) 2

/-- Real part of `-(w⁻¹)²` in Cartesian coordinates. -/
theorem neg_inv_sq_re {w : ℂ} (hw : w ≠ 0) :
    (-(w⁻¹ ^ 2)).re = (w.im ^ 2 - w.re ^ 2) / (w.re ^ 2 + w.im ^ 2) ^ 2 := by
  have hN : w.re * w.re + w.im * w.im ≠ 0 := by
    have hpos := Complex.normSq_pos.mpr hw
    rw [Complex.normSq_apply] at hpos
    exact ne_of_gt hpos
  simp only [Complex.neg_re, pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply]
  field_simp
  ring

/-- Imaginary part of `-(w⁻¹)²` in Cartesian coordinates. -/
theorem neg_inv_sq_im {w : ℂ} (hw : w ≠ 0) :
    (-(w⁻¹ ^ 2)).im = 2 * w.re * w.im / (w.re ^ 2 + w.im ^ 2) ^ 2 := by
  have hN : w.re * w.re + w.im * w.im ≠ 0 := by
    have hpos := Complex.normSq_pos.mpr hw
    rw [Complex.normSq_apply] at hpos
    exact ne_of_gt hpos
  simp only [Complex.neg_im, pow_two, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply]
  field_simp
  ring

theorem xiOrbit_centered_re (q : XiZeroCopy) :
    ((q.1 : ℂ) - 1 / 2).re = (q.1 : ℂ).re - 1 / 2 := by
  simp

theorem xiOrbit_centered_im (q : XiZeroCopy) :
    ((q.1 : ℂ) - 1 / 2).im = (q.1 : ℂ).im := by
  simp

/-- Real part of the reciprocal-square atom in chamber coordinates. -/
theorem xiZeroCopyReciprocalSquare_re_eq_chamber (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).re =
      xiOrbitDetuning q / (xiOrbitDetuning q ^ 2 + xiOrbitCoupling q) := by
  have hw : (q.1 : ℂ) - 1 / 2 ≠ 0 := sub_ne_zero.mpr (xi_divisor_support_ne_half q.1)
  rw [xiOrbitDetuning_sq_add_coupling, xiZeroCopyReciprocalSquare_eq,
    xiCentralReciprocalSquare, neg_inv_sq_re hw, xiOrbit_centered_re, xiOrbit_centered_im]
  unfold xiOrbitDetuning xiOrbitTransverse xiOrbitHeight
  ring_nf

/-- Imaginary part of the reciprocal-square atom in chamber coordinates. -/
theorem xiZeroCopyReciprocalSquare_im_eq_chamber (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im =
      2 * xiOrbitShear q / (xiOrbitDetuning q ^ 2 + xiOrbitCoupling q) := by
  have hw : (q.1 : ℂ) - 1 / 2 ≠ 0 := sub_ne_zero.mpr (xi_divisor_support_ne_half q.1)
  rw [xiOrbitDetuning_sq_add_coupling, xiZeroCopyReciprocalSquare_eq,
    xiCentralReciprocalSquare, neg_inv_sq_im hw, xiOrbit_centered_re, xiOrbit_centered_im]
  unfold xiOrbitShear xiOrbitTransverse xiOrbitHeight
  ring_nf

/-- The `(0,0)` entry of the protected orbit matrix is exactly the positive orbit mass. -/
theorem orbitH_zero_eq_xiSquaredEulerApertureOrbitMass (q : XiZeroCopy) :
    orbitH (xiOrbitDetuning q) (xiOrbitCoupling q) 0 =
      xiSquaredEulerApertureOrbitMass q := by
  rw [xiSquaredEulerApertureOrbitMass, xiZeroCopyReciprocalSquare_re_eq_chamber,
    orbitH]
  norm_num

/-! ## The confluent first derivative-Hankel minor -/

/-- First confluent derivative-Hankel minor `m₀ m₂ - m₁²` of one orbit, where
`mₖ = Re λ^{k+1}`. -/
def xiOrbitConfluentMinor (q : XiZeroCopy) : ℝ :=
  (xiZeroCopyReciprocalSquare q).re * (xiZeroCopyReciprocalSquare q ^ 3).re -
    ((xiZeroCopyReciprocalSquare q ^ 2).re) ^ 2

/-- **Exact confluent polarity identity.**  The first confluent minor of one orbit is minus the
squared transverse part times the squared modulus. -/
theorem xiOrbitConfluentMinor_eq (q : XiZeroCopy) :
    xiOrbitConfluentMinor q =
      -((xiZeroCopyReciprocalSquare q).im ^ 2 *
        Complex.normSq (xiZeroCopyReciprocalSquare q)) := by
  unfold xiOrbitConfluentMinor
  set z := xiZeroCopyReciprocalSquare q with hz
  have h3 : z ^ 3 = z * z * z := by ring
  have h2 : z ^ 2 = z * z := by ring
  rw [h3, h2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem xiOrbitConfluentMinor_nonpos (q : XiZeroCopy) :
    xiOrbitConfluentMinor q ≤ 0 := by
  rw [xiOrbitConfluentMinor_eq]
  have : 0 ≤ (xiZeroCopyReciprocalSquare q).im ^ 2 *
      Complex.normSq (xiZeroCopyReciprocalSquare q) :=
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  linarith

/-- **Strict confluent negativity off the critical line.** -/
theorem xiOrbitConfluentMinor_neg_of_re_ne_half (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    xiOrbitConfluentMinor q < 0 := by
  have him : (xiZeroCopyReciprocalSquare q).im ≠ 0 := by
    intro him
    apply hoff
    apply (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp
    simpa only [xiZeroCopyReciprocalSquare_eq] using him
  have hnorm : 0 < Complex.normSq (xiZeroCopyReciprocalSquare q) :=
    Complex.normSq_pos.mpr fun hzero => him (by rw [hzero]; rfl)
  rw [xiOrbitConfluentMinor_eq]
  have : 0 < (xiZeroCopyReciprocalSquare q).im ^ 2 *
      Complex.normSq (xiZeroCopyReciprocalSquare q) :=
    mul_pos (sq_pos_of_ne_zero him) hnorm
  linarith

/-- The confluent minor vanishes exactly on the critical line. -/
theorem xiOrbitConfluentMinor_eq_zero_iff (q : XiZeroCopy) :
    xiOrbitConfluentMinor q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    by_contra hoff
    exact (ne_of_lt (xiOrbitConfluentMinor_neg_of_re_ne_half q hoff)) hzero
  · intro hline
    have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_eq]
      exact (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mpr hline
    rw [xiOrbitConfluentMinor_eq, him]
    ring

/-! ## The polarity no-go -/

/-- **Mass-shifted three-point orbit polarity no-go.**  Every actual Xi orbit is simultaneously
strictly positive in the separated-point three-point matrix and, when off the critical line,
strictly negative in the first confluent derivative-Hankel minor.  Separated-point positivity
therefore cannot orient the mass-shifted boundary. -/
theorem xiOrbit_separated_positive_and_confluent_negative (q : XiZeroCopy) :
    Matrix.PosDef (orbitMatrix (xiOrbitDetuning q) (xiOrbitCoupling q)) ∧
      xiOrbitConfluentMinor q ≤ 0 ∧
      ((q.1 : ℂ).re ≠ 1 / 2 → xiOrbitConfluentMinor q < 0) :=
  ⟨xiOrbitMatrix_posDef q, xiOrbitConfluentMinor_nonpos q,
    xiOrbitConfluentMinor_neg_of_re_ne_half q⟩

/-- No orbit-diagonal positivity can be inherited by the confluent detector: on the critical-line
complement the two detectors have strictly opposite sign. -/
theorem xiOrbit_polarity_split (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < (orbitMatrix (xiOrbitDetuning q) (xiOrbitCoupling q)).det ∧
      xiOrbitConfluentMinor q < 0 :=
  ⟨xiOrbitMatrix_det_pos q, xiOrbitConfluentMinor_neg_of_re_ne_half q hoff⟩

end

end RHTower
