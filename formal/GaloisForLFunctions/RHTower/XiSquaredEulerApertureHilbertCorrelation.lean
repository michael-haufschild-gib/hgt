import GaloisForLFunctions.HTGeometry.ReciprocalSquareTransverseDefectLaw
import GaloisForLFunctions.RHTower.XiSquaredEulerRayFullResponse
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization

/-!
# The squared-Euler aperture Hilbert correlation

For a reciprocal-square Xi atom `lambda = a + i b`, the source height gap gives `a > 0`.
This permits an exact, all-degree completion of the trace-Hankel square:

`Re (lambda * w^2)
  = a * (Re w - (b / a) * Im w)^2
      - (|lambda|^2 / a) * (Im w)^2`.

Thus the RH-bearing form is not an unspecified signed Jordan decomposition.  It is the difference
of a positive sheared-evaluation Hilbert energy and an explicit transverse charge energy.

At the first nonconstant Hankel level this becomes a sharper response-correlation law.  If

`a_q = Re lambda_q`,
`tau_q = Re(lambda_q^2) / a_q`, and
`chi_q = Im(lambda_q)^2 * |lambda_q|^2 / a_q`,

then every finite multiplicity-exact Xi packet satisfies

`A C - B^2 = G - A * sum_q chi_q`,

where `G` is the Hilbert Gram determinant of the mass vector `sqrt(a_q)` and the response-slope
vector `sqrt(a_q) tau_q`.  Equivalently,

`2 G = sum_{q,r} a_q a_r (tau_q - tau_r)^2`.

The correlation side is therefore manifestly nonnegative.  The remaining signed boundary problem
is exactly whether this Hilbert dispersion dominates the transverse charge.  A single transverse
orbit has negative minor `-Im(lambda)^2 * |lambda|^2`, while cross-orbit response dispersion is
the only possible positive cancellation mechanism.
-/

open Complex Polynomial Set
open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Positive square in the oriented complex-square decomposition. -/
def orientedComplexSquareHilbertTerm (lam w : ℂ) : ℝ :=
  lam.re * (w.re - lam.im / lam.re * w.im) ^ 2

/-- Transverse square in the oriented complex-square decomposition. -/
def orientedComplexSquareTransverseTerm (lam w : ℂ) : ℝ :=
  Complex.normSq lam / lam.re * w.im ^ 2

/-- Exact oriented completion of a complex square. -/
theorem re_mul_sq_eq_orientedHilbert_sub_transverse
    (lam w : ℂ) (hlam : lam.re ≠ 0) :
    (lam * w ^ 2).re =
      orientedComplexSquareHilbertTerm lam w -
        orientedComplexSquareTransverseTerm lam w := by
  unfold orientedComplexSquareHilbertTerm orientedComplexSquareTransverseTerm
  rw [Complex.mul_re, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply]
  field_simp [hlam]
  ring

theorem orientedComplexSquareHilbertTerm_nonneg
    {lam w : ℂ} (hlam : 0 ≤ lam.re) :
    0 ≤ orientedComplexSquareHilbertTerm lam w := by
  exact mul_nonneg hlam (sq_nonneg _)

theorem orientedComplexSquareTransverseTerm_nonneg
    {lam w : ℂ} (hlam : 0 ≤ lam.re) :
    0 ≤ orientedComplexSquareTransverseTerm lam w := by
  have hnorm : 0 ≤ Complex.normSq lam := by
    rw [Complex.normSq_apply]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  exact mul_nonneg (div_nonneg hnorm hlam) (sq_nonneg _)

end

end HTGeometry

namespace RHTower

noncomputable section

/-! ## All-degree Xi Hilbert/charge splitting -/

/-- The sheared real evaluation which forms the positive aperture channel. -/
def xiSquaredEulerApertureShearedEvaluation
    (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiZeroCopyReciprocalSquare q
  let w := evalRealPolynomial p lam
  w.re - lam.im / lam.re * w.im

/-- Positive Hilbert energy of one multiplicity-exact Xi atom. -/
def xiSquaredEulerApertureHilbertTerm
    (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiZeroCopyReciprocalSquare q
  lam.re * (xiSquaredEulerApertureShearedEvaluation p q) ^ 2

/-- Transverse boundary-charge energy of one multiplicity-exact Xi atom. -/
def xiSquaredEulerApertureTransverseTerm
    (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiZeroCopyReciprocalSquare q
  Complex.normSq lam / lam.re * (evalRealPolynomial p lam).im ^ 2

/-- The unweighted copy summand of the actual Xi trace-Hankel form.  Multiplicity is represented
by the `XiZeroCopy` index itself. -/
def xiSquaredEulerApertureHankelTerm
    (p : Polynomial ℝ) (q : XiZeroCopy) : ℝ :=
  let lam := xiZeroCopyReciprocalSquare q
  (lam * evalRealPolynomial p lam ^ 2).re

/-- Every reciprocal-square Xi atom has positive oriented mass, unconditionally. -/
theorem xiZeroCopyReciprocalSquare_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q).re := by
  simpa only [xiThermalNode] using xiThermalNode_pos q

/-- **All-degree aperture Hilbert/charge law.**  Each trace-Hankel summand is exactly a positive
sheared-evaluation square minus its transverse boundary-charge square. -/
theorem xiSquaredEulerApertureHankelTerm_eq_hilbert_sub_transverse
    (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiSquaredEulerApertureHankelTerm p q =
      xiSquaredEulerApertureHilbertTerm p q -
        xiSquaredEulerApertureTransverseTerm p q := by
  let lam := xiZeroCopyReciprocalSquare q
  let w := evalRealPolynomial p lam
  have hlam : lam.re ≠ 0 := (xiZeroCopyReciprocalSquare_re_pos q).ne'
  simpa only [xiSquaredEulerApertureHankelTerm,
    xiSquaredEulerApertureHilbertTerm,
    xiSquaredEulerApertureTransverseTerm,
    xiSquaredEulerApertureShearedEvaluation,
    HTGeometry.orientedComplexSquareHilbertTerm,
    HTGeometry.orientedComplexSquareTransverseTerm, lam, w] using
    HTGeometry.re_mul_sq_eq_orientedHilbert_sub_transverse lam w hlam

/-- The positive aperture term is the squared real response amplitude divided by the positive
oriented mass.  This is the intrinsic metric formula: the shear is forced by multiplication by
the reciprocal-square response atom. -/
theorem xiSquaredEulerApertureHilbertTerm_eq_responseAmplitude_sq_div
    (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiSquaredEulerApertureHilbertTerm p q =
      (xiZeroCopyReciprocalSquare q *
          evalRealPolynomial p (xiZeroCopyReciprocalSquare q)).re ^ 2 /
        (xiZeroCopyReciprocalSquare q).re := by
  have hre : (xiZeroCopyReciprocalSquare q).re ≠ 0 :=
    (xiZeroCopyReciprocalSquare_re_pos q).ne'
  unfold xiSquaredEulerApertureHilbertTerm
    xiSquaredEulerApertureShearedEvaluation
  rw [Complex.mul_re]
  field_simp [hre]

theorem xiSquaredEulerApertureHilbertTerm_nonneg
    (p : Polynomial ℝ) (q : XiZeroCopy) :
    0 ≤ xiSquaredEulerApertureHilbertTerm p q := by
  exact mul_nonneg (xiZeroCopyReciprocalSquare_re_pos q).le (sq_nonneg _)

theorem xiSquaredEulerApertureTransverseTerm_nonneg
    (p : Polynomial ℝ) (q : XiZeroCopy) :
    0 ≤ xiSquaredEulerApertureTransverseTerm p q := by
  unfold xiSquaredEulerApertureTransverseTerm
  have hre := (xiZeroCopyReciprocalSquare_re_pos q).le
  have hnorm : 0 ≤ Complex.normSq (xiZeroCopyReciprocalSquare q) := by
    rw [Complex.normSq_apply]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  exact mul_nonneg (div_nonneg hnorm hre) (sq_nonneg _)

/-- Finite positive Hilbert energy. -/
def xiSquaredEulerFiniteApertureHilbertEnergy
    (S : Finset XiZeroCopy) (p : Polynomial ℝ) : ℝ :=
  ∑ q ∈ S, xiSquaredEulerApertureHilbertTerm p q

/-- Finite transverse boundary-charge energy. -/
def xiSquaredEulerFiniteApertureTransverseEnergy
    (S : Finset XiZeroCopy) (p : Polynomial ℝ) : ℝ :=
  ∑ q ∈ S, xiSquaredEulerApertureTransverseTerm p q

/-- Finite multiplicity-exact trace-Hankel value. -/
def xiSquaredEulerFiniteApertureHankelValue
    (S : Finset XiZeroCopy) (p : Polynomial ℝ) : ℝ :=
  ∑ q ∈ S, xiSquaredEulerApertureHankelTerm p q

/-- Finite packet version of the all-degree Hilbert/charge decomposition. -/
theorem xiSquaredEulerFiniteApertureHankelValue_eq_hilbert_sub_transverse
    (S : Finset XiZeroCopy) (p : Polynomial ℝ) :
    xiSquaredEulerFiniteApertureHankelValue S p =
      xiSquaredEulerFiniteApertureHilbertEnergy S p -
        xiSquaredEulerFiniteApertureTransverseEnergy S p := by
  classical
  rw [xiSquaredEulerFiniteApertureHankelValue,
    xiSquaredEulerFiniteApertureHilbertEnergy,
    xiSquaredEulerFiniteApertureTransverseEnergy,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  exact xiSquaredEulerApertureHankelTerm_eq_hilbert_sub_transverse p q

theorem xiSquaredEulerFiniteApertureHilbertEnergy_nonneg
    (S : Finset XiZeroCopy) (p : Polynomial ℝ) :
    0 ≤ xiSquaredEulerFiniteApertureHilbertEnergy S p := by
  unfold xiSquaredEulerFiniteApertureHilbertEnergy
  exact Finset.sum_nonneg fun q _hq =>
    xiSquaredEulerApertureHilbertTerm_nonneg p q

theorem xiSquaredEulerFiniteApertureTransverseEnergy_nonneg
    (S : Finset XiZeroCopy) (p : Polynomial ℝ) :
    0 ≤ xiSquaredEulerFiniteApertureTransverseEnergy S p := by
  unfold xiSquaredEulerFiniteApertureTransverseEnergy
  exact Finset.sum_nonneg fun q _hq =>
    xiSquaredEulerApertureTransverseTerm_nonneg p q

/-- Exact finite all-degree cancellation criterion. -/
theorem xiSquaredEulerFiniteApertureHankelValue_nonneg_iff
    (S : Finset XiZeroCopy) (p : Polynomial ℝ) :
    0 ≤ xiSquaredEulerFiniteApertureHankelValue S p ↔
      xiSquaredEulerFiniteApertureTransverseEnergy S p ≤
        xiSquaredEulerFiniteApertureHilbertEnergy S p := by
  rw [xiSquaredEulerFiniteApertureHankelValue_eq_hilbert_sub_transverse]
  exact sub_nonneg

/-! ## The first nonconstant response-correlation shadow -/

/-- Positive central mass of one squared-Euler orbit. -/
def xiSquaredEulerApertureOrbitMass (q : XiZeroCopy) : ℝ :=
  (xiZeroCopyReciprocalSquare q).re

/-- Radial response slope of one squared-Euler orbit at the central aperture. -/
def xiSquaredEulerApertureOrbitSlope (q : XiZeroCopy) : ℝ :=
  (xiZeroCopyReciprocalSquare q ^ 2).re /
    xiSquaredEulerApertureOrbitMass q

/-- Transverse charge density exposed by the cubic response coefficient. -/
def xiSquaredEulerApertureOrbitChargeDensity (q : XiZeroCopy) : ℝ :=
  (xiZeroCopyReciprocalSquare q).im ^ 2 *
    Complex.normSq (xiZeroCopyReciprocalSquare q) /
      xiSquaredEulerApertureOrbitMass q

theorem xiSquaredEulerApertureOrbitMass_pos (q : XiZeroCopy) :
    0 < xiSquaredEulerApertureOrbitMass q :=
  xiZeroCopyReciprocalSquare_re_pos q

/-- The second central response coefficient is mass times radial slope. -/
theorem xiSquaredEulerAperture_pow_two_re_eq_mass_mul_slope
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q ^ 2).re =
      xiSquaredEulerApertureOrbitMass q *
        xiSquaredEulerApertureOrbitSlope q := by
  unfold xiSquaredEulerApertureOrbitSlope
  field_simp [(xiSquaredEulerApertureOrbitMass_pos q).ne']

/-- The cubic central response coefficient is a positive slope square minus the transverse
charge density. -/
theorem xiSquaredEulerAperture_pow_three_re_eq_mass_mul_slope_sq_sub_charge
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q ^ 3).re =
      xiSquaredEulerApertureOrbitMass q *
          xiSquaredEulerApertureOrbitSlope q ^ 2 -
        xiSquaredEulerApertureOrbitChargeDensity q := by
  let z := xiZeroCopyReciprocalSquare q
  have hz : z.re ≠ 0 := (xiZeroCopyReciprocalSquare_re_pos q).ne'
  unfold xiSquaredEulerApertureOrbitMass xiSquaredEulerApertureOrbitSlope
    xiSquaredEulerApertureOrbitChargeDensity
  change (z ^ 3).re =
    z.re * ((z ^ 2).re / z.re) ^ 2 -
      z.im ^ 2 * Complex.normSq z / z.re
  rw [show z ^ 3 = z * z * z by ring, show z ^ 2 = z * z by ring]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  field_simp [hz]
  ring

theorem xiSquaredEulerApertureOrbitChargeDensity_nonneg (q : XiZeroCopy) :
    0 ≤ xiSquaredEulerApertureOrbitChargeDensity q := by
  unfold xiSquaredEulerApertureOrbitChargeDensity
  have hnorm : 0 ≤ Complex.normSq (xiZeroCopyReciprocalSquare q) := by
    rw [Complex.normSq_apply]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnorm)
    (xiSquaredEulerApertureOrbitMass_pos q).le

/-- The charge density is strictly positive at every genuinely off-critical orbit. -/
theorem xiSquaredEulerApertureOrbitChargeDensity_pos_of_ne_half
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < xiSquaredEulerApertureOrbitChargeDensity q := by
  have him : (xiZeroCopyReciprocalSquare q).im ≠ 0 := by
    intro him
    apply hoff
    apply (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp
    simpa only [xiZeroCopyReciprocalSquare_eq] using him
  have hnorm : 0 < Complex.normSq (xiZeroCopyReciprocalSquare q) := by
    apply Complex.normSq_pos.mpr
    exact fun hzero => him (by rw [hzero]; rfl)
  unfold xiSquaredEulerApertureOrbitChargeDensity
  exact div_pos (mul_pos (sq_pos_of_ne_zero him) hnorm)
    (xiSquaredEulerApertureOrbitMass_pos q)

/-- The charge radical is exactly the critical line. -/
theorem xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff
    (q : XiZeroCopy) :
    xiSquaredEulerApertureOrbitChargeDensity q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    by_contra hoff
    exact (ne_of_gt
      (xiSquaredEulerApertureOrbitChargeDensity_pos_of_ne_half q hoff)) hzero
  · intro hline
    have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_eq]
      exact (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mpr hline
    simp [xiSquaredEulerApertureOrbitChargeDensity, him]

/-- Finite zeroth central response coefficient. -/
def xiSquaredEulerFiniteApertureCentralA (S : Finset XiZeroCopy) : ℝ :=
  ∑ q ∈ S, xiSquaredEulerApertureOrbitMass q

/-- Finite first central response coefficient. -/
def xiSquaredEulerFiniteApertureCentralB (S : Finset XiZeroCopy) : ℝ :=
  ∑ q ∈ S, (xiZeroCopyReciprocalSquare q ^ 2).re

/-- Finite second central response coefficient. -/
def xiSquaredEulerFiniteApertureCentralC (S : Finset XiZeroCopy) : ℝ :=
  ∑ q ∈ S, (xiZeroCopyReciprocalSquare q ^ 3).re

/-- The first nonconstant central Hankel minor of a finite Xi packet. -/
def xiSquaredEulerFiniteApertureCentralMinor (S : Finset XiZeroCopy) : ℝ :=
  xiSquaredEulerFiniteApertureCentralA S *
      xiSquaredEulerFiniteApertureCentralC S -
    xiSquaredEulerFiniteApertureCentralB S ^ 2

/-- The actual positive Hilbert Gram determinant of central orbit mass and response slope. -/
def xiSquaredEulerFiniteApertureHilbertGram (S : Finset XiZeroCopy) : ℝ :=
  xiSquaredEulerFiniteApertureCentralA S *
      (∑ q ∈ S, xiSquaredEulerApertureOrbitMass q *
        xiSquaredEulerApertureOrbitSlope q ^ 2) -
    (∑ q ∈ S, xiSquaredEulerApertureOrbitMass q *
      xiSquaredEulerApertureOrbitSlope q) ^ 2

/-- Total transverse boundary charge at the first nonconstant response level. -/
def xiSquaredEulerFiniteApertureBoundaryCharge (S : Finset XiZeroCopy) : ℝ :=
  xiSquaredEulerFiniteApertureCentralA S *
    ∑ q ∈ S, xiSquaredEulerApertureOrbitChargeDensity q

/-- **Exact response-correlation cancellation law.**  The finite central minor is the positive
Hilbert Gram minus the complete transverse boundary charge. -/
theorem xiSquaredEulerFiniteApertureCentralMinor_eq_hilbertGram_sub_boundaryCharge
    (S : Finset XiZeroCopy) :
    xiSquaredEulerFiniteApertureCentralMinor S =
      xiSquaredEulerFiniteApertureHilbertGram S -
        xiSquaredEulerFiniteApertureBoundaryCharge S := by
  classical
  have hB : xiSquaredEulerFiniteApertureCentralB S =
      ∑ q ∈ S, xiSquaredEulerApertureOrbitMass q *
        xiSquaredEulerApertureOrbitSlope q := by
    unfold xiSquaredEulerFiniteApertureCentralB
    apply Finset.sum_congr rfl
    intro q _hq
    exact xiSquaredEulerAperture_pow_two_re_eq_mass_mul_slope q
  have hC : xiSquaredEulerFiniteApertureCentralC S =
      (∑ q ∈ S, xiSquaredEulerApertureOrbitMass q *
          xiSquaredEulerApertureOrbitSlope q ^ 2) -
        ∑ q ∈ S, xiSquaredEulerApertureOrbitChargeDensity q := by
    unfold xiSquaredEulerFiniteApertureCentralC
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    exact
      xiSquaredEulerAperture_pow_three_re_eq_mass_mul_slope_sq_sub_charge q
  rw [xiSquaredEulerFiniteApertureCentralMinor,
    xiSquaredEulerFiniteApertureHilbertGram,
    xiSquaredEulerFiniteApertureBoundaryCharge, hB, hC]
  ring

/-- The Hilbert Gram is exactly half the ordered pairwise response-slope dispersion. -/
theorem two_mul_xiSquaredEulerFiniteApertureHilbertGram_eq_pairwiseDispersion
    (S : Finset XiZeroCopy) :
    2 * xiSquaredEulerFiniteApertureHilbertGram S =
      ∑ q ∈ S, ∑ r ∈ S,
        xiSquaredEulerApertureOrbitMass q *
          xiSquaredEulerApertureOrbitMass r *
            (xiSquaredEulerApertureOrbitSlope q -
              xiSquaredEulerApertureOrbitSlope r) ^ 2 := by
  classical
  have hvariance := two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion
    S xiSquaredEulerApertureOrbitMass
      xiSquaredEulerApertureOrbitSlope xiSquaredEulerApertureOrbitSlope
  unfold xiSquaredEulerFiniteApertureHilbertGram
    xiSquaredEulerFiniteApertureCentralA
  simp only [pow_two, mul_assoc] at hvariance ⊢
  nlinarith only [hvariance]

theorem xiSquaredEulerFiniteApertureHilbertGram_nonneg
    (S : Finset XiZeroCopy) :
    0 ≤ xiSquaredEulerFiniteApertureHilbertGram S := by
  have hdisp : 0 ≤
      ∑ q ∈ S, ∑ r ∈ S,
        xiSquaredEulerApertureOrbitMass q *
          xiSquaredEulerApertureOrbitMass r *
            (xiSquaredEulerApertureOrbitSlope q -
              xiSquaredEulerApertureOrbitSlope r) ^ 2 := by
    apply Finset.sum_nonneg
    intro q _hq
    apply Finset.sum_nonneg
    intro r _hr
    exact mul_nonneg
      (mul_nonneg (xiSquaredEulerApertureOrbitMass_pos q).le
        (xiSquaredEulerApertureOrbitMass_pos r).le)
      (sq_nonneg _)
  have hid :=
    two_mul_xiSquaredEulerFiniteApertureHilbertGram_eq_pairwiseDispersion S
  nlinarith

theorem xiSquaredEulerFiniteApertureCentralA_pos
    {S : Finset XiZeroCopy} (hS : S.Nonempty) :
    0 < xiSquaredEulerFiniteApertureCentralA S := by
  unfold xiSquaredEulerFiniteApertureCentralA
  exact Finset.sum_pos (fun q _hq => xiSquaredEulerApertureOrbitMass_pos q) hS

theorem xiSquaredEulerFiniteApertureBoundaryCharge_nonneg
    (S : Finset XiZeroCopy) :
    0 ≤ xiSquaredEulerFiniteApertureBoundaryCharge S := by
  unfold xiSquaredEulerFiniteApertureBoundaryCharge
  apply mul_nonneg
  · unfold xiSquaredEulerFiniteApertureCentralA
    exact Finset.sum_nonneg fun q _hq =>
      (xiSquaredEulerApertureOrbitMass_pos q).le
  · exact Finset.sum_nonneg fun q _hq =>
      xiSquaredEulerApertureOrbitChargeDensity_nonneg q

/-- **Sharp first-minor cancellation criterion.**  Nonnegativity is exactly domination of the
transverse boundary charge by the response-slope Hilbert dispersion. -/
theorem xiSquaredEulerFiniteApertureCentralMinor_nonneg_iff
    (S : Finset XiZeroCopy) :
    0 ≤ xiSquaredEulerFiniteApertureCentralMinor S ↔
      xiSquaredEulerFiniteApertureBoundaryCharge S ≤
        xiSquaredEulerFiniteApertureHilbertGram S := by
  rw [xiSquaredEulerFiniteApertureCentralMinor_eq_hilbertGram_sub_boundaryCharge]
  exact sub_nonneg

/-- The finite boundary charge vanishes exactly when every orbit in a nonempty packet lies on the
critical line. -/
theorem xiSquaredEulerFiniteApertureBoundaryCharge_eq_zero_iff
    {S : Finset XiZeroCopy} (hS : S.Nonempty) :
    xiSquaredEulerFiniteApertureBoundaryCharge S = 0 ↔
      ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2 := by
  have hAne : xiSquaredEulerFiniteApertureCentralA S ≠ 0 :=
    (xiSquaredEulerFiniteApertureCentralA_pos hS).ne'
  rw [xiSquaredEulerFiniteApertureBoundaryCharge, mul_eq_zero]
  simp only [hAne, false_or]
  constructor
  · intro hsum q hq
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun r _hr => xiSquaredEulerApertureOrbitChargeDensity_nonneg r)).mp hsum q hq
    exact (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).mp hterm
  · intro hline
    apply Finset.sum_eq_zero
    intro q hq
    exact (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).mpr
      (hline q hq)

/-- A single orbit has central minor equal to the negative transverse charge
`-Im(lambda)^2 |lambda|^2`. -/
theorem xiSquaredEulerAperture_singleOrbitCentralMinor_eq
    (q : XiZeroCopy) :
    xiSquaredEulerFiniteApertureCentralMinor {q} =
      -(xiZeroCopyReciprocalSquare q).im ^ 2 *
        Complex.normSq (xiZeroCopyReciprocalSquare q) := by
  classical
  let z := xiZeroCopyReciprocalSquare q
  unfold xiSquaredEulerFiniteApertureCentralMinor
    xiSquaredEulerFiniteApertureCentralA
    xiSquaredEulerFiniteApertureCentralB
    xiSquaredEulerFiniteApertureCentralC
    xiSquaredEulerApertureOrbitMass
  simp only [Finset.sum_singleton]
  change z.re * (z ^ 3).re - (z ^ 2).re ^ 2 =
    -z.im ^ 2 * Complex.normSq z
  rw [show z ^ 3 = z * z * z by ring, show z ^ 2 = z * z by ring]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Atomic sharpness: every genuinely off-critical orbit has a strictly negative first central
minor, so only cross-orbit Hilbert dispersion can cancel its boundary charge. -/
theorem xiSquaredEulerAperture_singleOrbitCentralMinor_neg_of_ne_half
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    xiSquaredEulerFiniteApertureCentralMinor {q} < 0 := by
  rw [xiSquaredEulerAperture_singleOrbitCentralMinor_eq]
  have him : (xiZeroCopyReciprocalSquare q).im ≠ 0 := by
    intro him
    apply hoff
    apply (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp
    simpa only [xiZeroCopyReciprocalSquare_eq] using him
  have hnorm : 0 < Complex.normSq (xiZeroCopyReciprocalSquare q) := by
    exact Complex.normSq_pos.mpr (fun hzero => him (by rw [hzero]; rfl))
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero him)) hnorm

end

end RHTower
