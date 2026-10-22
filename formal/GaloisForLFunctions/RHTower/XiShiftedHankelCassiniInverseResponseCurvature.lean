import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCassiniHyperbolicSourceLaw
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniSourceJet

/-!
# Route-U first minor as inverse Cassini-response curvature

The first nonconstant shifted-Xi Hankel determinant is not merely a two-moment sign test.
If `F(y)` is the positive zeroth shifted reciprocal moment, then

`det H₂(y) = -F(y)^(3 : ℕ) / 2 * (1 / F)''(y)`.

The canonical monic null polynomial at a zero determinant is
`X - m₁(y) / m₀(y)`.  Its first shifted-square extension is exactly the third derivative of
`1 / F`, up to the positive factor `F(y)^(2 : ℕ) / 6`.  Thus a degree-one genuine Route-U crossing is
a downward-oriented inflection of the reciprocal response, not an arbitrary Hankel accident.

Inside the theta Fourier--Laplace strip, the same reciprocal response is the source-built ratio

`t * thetaCuspHyperbolicPartition t / thetaCuspHyperbolicFlux t`,  `y = t²`.

This isolates a concrete source rigidity target: exclude downward inflections of that one
hyperbolic partition/flux quotient at a flat first-minor contact.
-/

open Complex Matrix Polynomial

namespace RHTower

noncomputable section

/-- Positive zeroth Route-U response at squared mass `y`. -/
def xiShiftedCassiniResponse (y : ℝ) : ℝ :=
  (xiShiftedReciprocalMoment y 0).re

/-- Reciprocal response whose curvature detects the first nonconstant Hankel minor. -/
def xiShiftedCassiniInverseResponse (y : ℝ) : ℝ :=
  (xiShiftedCassiniResponse y)⁻¹

/-- First derivative of the reciprocal response, written directly in shifted moments. -/
def xiShiftedCassiniInverseResponseSlope (y : ℝ) : ℝ :=
  (xiShiftedReciprocalMoment y 1).re / xiShiftedCassiniResponse y ^ (2 : ℕ)

/-- Second derivative of the reciprocal response, written directly in shifted moments. -/
def xiShiftedCassiniInverseResponseCurvature (y : ℝ) : ℝ :=
  2 * ((xiShiftedReciprocalMoment y 1).re ^ (2 : ℕ) -
      xiShiftedCassiniResponse y * (xiShiftedReciprocalMoment y 2).re) /
    xiShiftedCassiniResponse y ^ (3 : ℕ)

/-- First nonconstant shifted-Xi Hankel determinant. -/
def xiShiftedDegreeOneHankelMinor (y : ℝ) : ℝ :=
  xiShiftedCassiniResponse y * (xiShiftedReciprocalMoment y 2).re -
    (xiShiftedReciprocalMoment y 1).re ^ (2 : ℕ)

/-- Root of the canonical monic linear null polynomial at a singular first minor. -/
def xiShiftedDegreeOneNullRoot (y : ℝ) : ℝ :=
  (xiShiftedReciprocalMoment y 1).re / xiShiftedCassiniResponse y

/-- Canonical monic linear candidate on the first nonconstant Hankel face. -/
def xiShiftedDegreeOneNullPolynomial (y : ℝ) : Polynomial ℝ :=
  X - C (xiShiftedDegreeOneNullRoot y)

/-- First shifted-square extension of the canonical monic linear candidate. -/
def xiShiftedDegreeOneTerminalFlux (y : ℝ) : ℝ :=
  HTGeometry.momentFunctional
    (fun n => (xiShiftedReciprocalMoment y n).re)
    (X * xiShiftedDegreeOneNullPolynomial y ^ (2 : ℕ))

/-- Third derivative of the reciprocal response in canonical null-polynomial coordinates. -/
def xiShiftedCassiniInverseResponseThirdJet (y : ℝ) : ℝ :=
  6 * xiShiftedDegreeOneTerminalFlux y / xiShiftedCassiniResponse y ^ (2 : ℕ)

theorem xiShiftedCassiniResponse_pos {y : ℝ} (hy : 0 < y) :
    0 < xiShiftedCassiniResponse y := by
  exact re_xiShiftedReciprocalMoment_pos hy (by norm_num)

theorem xiShiftedCassiniResponse_eq_sourceMoment
    {y : ℝ} (hy : 0 < y) :
    xiShiftedCassiniResponse y = xiShiftedCassiniSourceMoment y 0 := by
  exact xiShiftedReciprocalMoment_re_eq_cassiniSourceMoment hy 0

theorem hasDerivAt_xiShiftedCassiniResponse
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt xiShiftedCassiniResponse
      (-(xiShiftedReciprocalMoment y 1).re) y := by
  change HasDerivAt (fun v => (xiShiftedReciprocalMoment v 0).re)
    (-(xiShiftedReciprocalMoment y 1).re) y
  simpa using hasDerivAt_re_xiShiftedReciprocalMoment hy 0

/-- The reciprocal-response slope is an actual derivative, not a formal jet abbreviation. -/
theorem hasDerivAt_xiShiftedCassiniInverseResponse
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt xiShiftedCassiniInverseResponse
      (xiShiftedCassiniInverseResponseSlope y) y := by
  have hresponse := hasDerivAt_xiShiftedCassiniResponse hy
  have hne : xiShiftedCassiniResponse y ≠ 0 :=
    (xiShiftedCassiniResponse_pos hy).ne'
  change HasDerivAt (fun v => (xiShiftedCassiniResponse v)⁻¹)
    (xiShiftedCassiniInverseResponseSlope y) y
  have hinv := hresponse.inv hne
  change HasDerivAt (fun v => (xiShiftedCassiniResponse v)⁻¹) _ y at hinv
  simpa [xiShiftedCassiniInverseResponseSlope] using hinv

/-- The inverse-response curvature is the derivative of its source-defined slope. -/
theorem hasDerivAt_xiShiftedCassiniInverseResponseSlope
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt xiShiftedCassiniInverseResponseSlope
      (xiShiftedCassiniInverseResponseCurvature y) y := by
  let m0 : ℝ → ℝ := fun v => (xiShiftedReciprocalMoment v 0).re
  let m1 : ℝ → ℝ := fun v => (xiShiftedReciprocalMoment v 1).re
  have h0 : HasDerivAt m0 (-m1 y) y := by
    have h := hasDerivAt_re_xiShiftedReciprocalMoment hy 0
    norm_num at h
    simpa [m0, m1] using h
  have h1 : HasDerivAt m1 (-2 * (xiShiftedReciprocalMoment y 2).re) y := by
    have h := hasDerivAt_re_xiShiftedReciprocalMoment hy 1
    norm_num at h
    simpa [m1] using h
  have h0ne : m0 y ≠ 0 := by
    exact (xiShiftedCassiniResponse_pos hy).ne'
  have hquot := h1.div (h0.pow 2) (pow_ne_zero 2 h0ne)
  simp only [Pi.pow_apply] at hquot
  change HasDerivAt (fun v => m1 v / m0 v ^ (2 : ℕ))
    (xiShiftedCassiniInverseResponseCurvature y) y
  change HasDerivAt (fun v => m1 v / m0 v ^ (2 : ℕ)) _ y at hquot
  convert hquot using 1
  dsimp only [xiShiftedCassiniInverseResponseCurvature,
    xiShiftedCassiniResponse, m0, m1]
  dsimp only [m0] at h0ne
  field_simp [h0ne]
  ring

theorem xiShiftedDegreeOneTerminalFlux_eq_moments (y : ℝ) :
    xiShiftedDegreeOneTerminalFlux y =
      (xiShiftedReciprocalMoment y 3).re -
        2 * xiShiftedDegreeOneNullRoot y *
          (xiShiftedReciprocalMoment y 2).re +
        xiShiftedDegreeOneNullRoot y ^ (2 : ℕ) *
          (xiShiftedReciprocalMoment y 1).re := by
  let r := xiShiftedDegreeOneNullRoot y
  have hpoly :
      X * (X - C r) ^ (2 : ℕ) =
        X ^ (3 : ℕ) + (-2 * r) • X ^ (2 : ℕ) + r ^ (2 : ℕ) • X ^ (1 : ℕ) := by
    rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
    simp only [map_mul, map_neg, map_ofNat, map_pow]
    ring
  simp only [xiShiftedDegreeOneTerminalFlux, xiShiftedDegreeOneNullPolynomial]
  change HTGeometry.momentFunctional
      (fun n => (xiShiftedReciprocalMoment y n).re)
      (X * (X - C r) ^ (2 : ℕ)) = _
  rw [hpoly, HTGeometry.momentFunctional_add,
    HTGeometry.momentFunctional_add,
    HTGeometry.momentFunctional_smul,
    HTGeometry.momentFunctional_smul,
    HTGeometry.momentFunctional_X_pow,
    HTGeometry.momentFunctional_X_pow,
    HTGeometry.momentFunctional_X_pow]
  dsimp only [r]
  ring

/-- The source-defined third jet is the derivative of reciprocal-response curvature. -/
theorem hasDerivAt_xiShiftedCassiniInverseResponseCurvature
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt xiShiftedCassiniInverseResponseCurvature
      (xiShiftedCassiniInverseResponseThirdJet y) y := by
  let m0 : ℝ → ℝ := fun v => (xiShiftedReciprocalMoment v 0).re
  let m1 : ℝ → ℝ := fun v => (xiShiftedReciprocalMoment v 1).re
  let m2 : ℝ → ℝ := fun v => (xiShiftedReciprocalMoment v 2).re
  have h0 : HasDerivAt m0 (-m1 y) y := by
    have h := hasDerivAt_re_xiShiftedReciprocalMoment hy 0
    norm_num at h
    simpa [m0, m1] using h
  have h1 : HasDerivAt m1 (-2 * m2 y) y := by
    have h := hasDerivAt_re_xiShiftedReciprocalMoment hy 1
    norm_num at h
    simpa [m1, m2] using h
  have h2 : HasDerivAt m2 (-3 * (xiShiftedReciprocalMoment y 3).re) y := by
    have h := hasDerivAt_re_xiShiftedReciprocalMoment hy 2
    norm_num at h
    simpa [m2] using h
  have h0ne : m0 y ≠ 0 := by
    exact (xiShiftedCassiniResponse_pos hy).ne'
  have hnumRaw := ((h1.pow 2).sub (h0.mul h2)).const_mul 2
  change HasDerivAt (fun v => 2 * (m1 v ^ (2 : ℕ) - m0 v * m2 v)) _ y at hnumRaw
  have hnum : HasDerivAt
      (fun v => 2 * (m1 v ^ (2 : ℕ) - m0 v * m2 v))
      (6 * (m0 y * (xiShiftedReciprocalMoment y 3).re - m1 y * m2 y)) y := by
    convert hnumRaw using 1
    ring
  have hquot := hnum.div (h0.pow 3) (pow_ne_zero 3 h0ne)
  simp only [Pi.pow_apply] at hquot
  change HasDerivAt
    (fun v => 2 * (m1 v ^ (2 : ℕ) - m0 v * m2 v) / m0 v ^ (3 : ℕ))
    (xiShiftedCassiniInverseResponseThirdJet y) y
  change HasDerivAt
    (fun v => 2 * (m1 v ^ (2 : ℕ) - m0 v * m2 v) / m0 v ^ (3 : ℕ)) _ y at hquot
  convert hquot using 1
  rw [xiShiftedCassiniInverseResponseThirdJet,
    xiShiftedDegreeOneTerminalFlux_eq_moments]
  dsimp only [xiShiftedDegreeOneNullRoot, xiShiftedCassiniResponse, m0, m1, m2]
  dsimp only [m0] at h0ne
  field_simp [h0ne]
  ring

/-- Exact curvature form of the first nonconstant shifted-Xi Hankel determinant. -/
theorem xiShiftedDegreeOneHankelMinor_eq_inverseResponseCurvature
    {y : ℝ} (hy : 0 < y) :
    xiShiftedDegreeOneHankelMinor y =
      -(xiShiftedCassiniResponse y ^ (3 : ℕ) / 2) *
        xiShiftedCassiniInverseResponseCurvature y := by
  have hne := (xiShiftedCassiniResponse_pos hy).ne'
  rw [xiShiftedDegreeOneHankelMinor,
    xiShiftedCassiniInverseResponseCurvature]
  field_simp [hne]
  ring

/-- A singular first minor is exactly a reciprocal-response inflection. -/
theorem xiShiftedDegreeOneHankelMinor_eq_zero_iff_inverseResponseCurvature_eq_zero
    {y : ℝ} (hy : 0 < y) :
    xiShiftedDegreeOneHankelMinor y = 0 ↔
      xiShiftedCassiniInverseResponseCurvature y = 0 := by
  rw [xiShiftedDegreeOneHankelMinor_eq_inverseResponseCurvature hy,
    mul_eq_zero]
  exact or_iff_right (neg_ne_zero.mpr
    (div_ne_zero (pow_ne_zero 3 (xiShiftedCassiniResponse_pos hy).ne')
      (by norm_num)))

/-- The Route-U terminal sign is exactly orientation of the inverse-response third jet. -/
theorem xiShiftedDegreeOneTerminalFlux_neg_iff_inverseResponseThirdJet_neg
    {y : ℝ} (hy : 0 < y) :
    xiShiftedDegreeOneTerminalFlux y < 0 ↔
      xiShiftedCassiniInverseResponseThirdJet y < 0 := by
  rw [xiShiftedCassiniInverseResponseThirdJet, div_neg_iff]
  have hden : 0 < xiShiftedCassiniResponse y ^ (2 : ℕ) :=
    sq_pos_of_pos (xiShiftedCassiniResponse_pos hy)
  simp only [hden, not_lt_of_ge hden.le, and_false, false_or, and_true]
  constructor <;> intro h <;> nlinarith

/-- A flat degree-one Hankel face with negative terminal flux is exactly a downward-oriented
inflection of the inverse Cassini response, with all three derivatives certified. -/
theorem xiShiftedDegreeOne_flat_negative_is_downwardInverseResponseInflection
    {y : ℝ} (hy : 0 < y)
    (hflat : xiShiftedDegreeOneHankelMinor y = 0)
    (hterminal : xiShiftedDegreeOneTerminalFlux y < 0) :
    xiShiftedCassiniInverseResponseCurvature y = 0 ∧
      xiShiftedCassiniInverseResponseThirdJet y < 0 ∧
      HasDerivAt xiShiftedCassiniInverseResponseCurvature
        (xiShiftedCassiniInverseResponseThirdJet y) y := by
  exact ⟨
    (xiShiftedDegreeOneHankelMinor_eq_zero_iff_inverseResponseCurvature_eq_zero hy).mp hflat,
    (xiShiftedDegreeOneTerminalFlux_neg_iff_inverseResponseThirdJet_neg hy).mp hterminal,
    hasDerivAt_xiShiftedCassiniInverseResponseCurvature hy⟩

/-- Theta-strip radial profile of the inverse Cassini response. -/
def thetaCuspCassiniInverseResponseProfile (t : ℝ) : ℝ :=
  t * thetaCuspHyperbolicPartition t / thetaCuspHyperbolicFlux t

/-- First radial jet, pulled back from squared mass. -/
def thetaCuspCassiniInverseResponseProfileSlope (t : ℝ) : ℝ :=
  2 * t * xiShiftedCassiniInverseResponseSlope (t ^ (2 : ℕ))

/-- Second radial jet.  Its Euler defect detects mass-coordinate inflection. -/
def thetaCuspCassiniInverseResponseProfileCurvature (t : ℝ) : ℝ :=
  2 * xiShiftedCassiniInverseResponseSlope (t ^ (2 : ℕ)) +
    4 * t ^ (2 : ℕ) * xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ))

/-- Third radial jet of the theta-strip inverse response. -/
def thetaCuspCassiniInverseResponseProfileThirdJet (t : ℝ) : ℝ :=
  12 * t * xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ)) +
    8 * t ^ (3 : ℕ) * xiShiftedCassiniInverseResponseThirdJet (t ^ (2 : ℕ))

/-- On the theta strip, reciprocal Cassini response is one fixed hyperbolic partition/flux
quotient.  This is the source-side normal form of the degree-one Route-U obstruction. -/
theorem xiShiftedCassiniInverseResponse_sq_eq_hyperbolicPartition_div_flux
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    xiShiftedCassiniInverseResponse (t ^ (2 : ℕ)) =
      t * thetaCuspHyperbolicPartition t / thetaCuspHyperbolicFlux t := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hu0 : 0 < 1 - t ^ (2 : ℕ) := by nlinarith
  have hu1 : 1 - t ^ (2 : ℕ) < 1 := by nlinarith
  have hsource :=
    thetaCuspCassiniInwardCoordinateResponse_eq_cassiniLogDeriv hu0 hu1
  have hratio :=
    thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_hyperbolicFluxRatio
      ht0 ht1
  have hjet :=
    neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hy 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at hjet
  have hcomplex :
      ((thetaCuspHyperbolicFlux t /
          (t * thetaCuspHyperbolicPartition t) : ℝ) : ℂ) =
        xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 0 := by
    exact hratio.symm.trans (hsource.trans (by
      convert hjet using 1 <;> push_cast <;> ring))
  have hreal := congrArg Complex.re hcomplex
  simp only [Complex.ofReal_re] at hreal
  have hflux : thetaCuspHyperbolicFlux t ≠ 0 :=
    (thetaCuspHyperbolicFlux_pos ht0 ht1).ne'
  have hpart : thetaCuspHyperbolicPartition t ≠ 0 :=
    (thetaCuspHyperbolicPartition_pos (by
      rw [abs_of_pos ht0]
      exact ht1)).ne'
  rw [xiShiftedCassiniInverseResponse, xiShiftedCassiniResponse, ← hreal]
  field_simp [ht0.ne', hflux, hpart]

theorem thetaCuspCassiniInverseResponseProfile_eq
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniInverseResponseProfile t =
      xiShiftedCassiniInverseResponse (t ^ (2 : ℕ)) := by
  unfold thetaCuspCassiniInverseResponseProfile
  exact (xiShiftedCassiniInverseResponse_sq_eq_hyperbolicPartition_div_flux ht0 ht1).symm

/-- The source quotient's declared first radial jet is its actual derivative. -/
theorem hasDerivAt_thetaCuspCassiniInverseResponseProfile
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt thetaCuspCassiniInverseResponseProfile
      (thetaCuspCassiniInverseResponseProfileSlope t) t := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hsq : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hinverse : HasDerivAt xiShiftedCassiniInverseResponse
      (xiShiftedCassiniInverseResponseSlope (t ^ (2 : ℕ))) (t ^ (2 : ℕ)) :=
    hasDerivAt_xiShiftedCassiniInverseResponse hy
  have hcomp := hinverse.comp_of_eq t hsq rfl
  change HasDerivAt (fun s : ℝ =>
    xiShiftedCassiniInverseResponse (s ^ (2 : ℕ))) _ t at hcomp
  have hlocal : Filter.EventuallyEq (nhds t)
      thetaCuspCassiniInverseResponseProfile
      (fun s : ℝ => xiShiftedCassiniInverseResponse (s ^ (2 : ℕ))) := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
    exact thetaCuspCassiniInverseResponseProfile_eq hs.1 hs.2
  have hsource := hcomp.congr_of_eventuallyEq hlocal
  change HasDerivAt thetaCuspCassiniInverseResponseProfile
    (2 * t * xiShiftedCassiniInverseResponseSlope (t ^ (2 : ℕ))) t
  exact hsource.congr_deriv (by ring)

/-- The source quotient's second radial jet is its actual derivative. -/
theorem hasDerivAt_thetaCuspCassiniInverseResponseProfileSlope
    {t : ℝ} (ht0 : 0 < t) :
    HasDerivAt thetaCuspCassiniInverseResponseProfileSlope
      (thetaCuspCassiniInverseResponseProfileCurvature t) t := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hsq : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hslopeMass : HasDerivAt xiShiftedCassiniInverseResponseSlope
      (xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ))) (t ^ (2 : ℕ)) :=
    hasDerivAt_xiShiftedCassiniInverseResponseSlope hy
  have hslope := hslopeMass.comp_of_eq t hsq rfl
  change HasDerivAt (fun s : ℝ =>
    xiShiftedCassiniInverseResponseSlope (s ^ (2 : ℕ))) _ t at hslope
  have hprod := ((hasDerivAt_id t).const_mul 2).mul hslope
  simp only [id_eq] at hprod
  change HasDerivAt (fun s : ℝ =>
    2 * s * xiShiftedCassiniInverseResponseSlope (s ^ (2 : ℕ))) _ t at hprod
  change HasDerivAt
    (fun s : ℝ => 2 * s * xiShiftedCassiniInverseResponseSlope (s ^ (2 : ℕ)))
    (2 * xiShiftedCassiniInverseResponseSlope (t ^ (2 : ℕ)) +
      4 * t ^ (2 : ℕ) * xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ))) t
  convert hprod using 1 <;> ring

/-- The source quotient's third radial jet is its actual derivative. -/
theorem hasDerivAt_thetaCuspCassiniInverseResponseProfileCurvature
    {t : ℝ} (ht0 : 0 < t) :
    HasDerivAt thetaCuspCassiniInverseResponseProfileCurvature
      (thetaCuspCassiniInverseResponseProfileThirdJet t) t := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hsq : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hslopeMass : HasDerivAt xiShiftedCassiniInverseResponseSlope
      (xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ))) (t ^ (2 : ℕ)) :=
    hasDerivAt_xiShiftedCassiniInverseResponseSlope hy
  have hcurvatureMass : HasDerivAt xiShiftedCassiniInverseResponseCurvature
      (xiShiftedCassiniInverseResponseThirdJet (t ^ (2 : ℕ))) (t ^ (2 : ℕ)) :=
    hasDerivAt_xiShiftedCassiniInverseResponseCurvature hy
  have hslope := hslopeMass.comp_of_eq t hsq rfl
  have hcurvature := hcurvatureMass.comp_of_eq t hsq rfl
  change HasDerivAt (fun s : ℝ =>
    xiShiftedCassiniInverseResponseSlope (s ^ (2 : ℕ))) _ t at hslope
  change HasDerivAt (fun s : ℝ =>
    xiShiftedCassiniInverseResponseCurvature (s ^ (2 : ℕ))) _ t at hcurvature
  have hfirst := hslope.const_mul 2
  have hsquare := (hasDerivAt_pow 2 t).const_mul 4
  have hsecond := hsquare.mul hcurvature
  have hsum := hfirst.add hsecond
  change HasDerivAt
    (fun s : ℝ =>
      2 * xiShiftedCassiniInverseResponseSlope (s ^ (2 : ℕ)) +
        4 * s ^ (2 : ℕ) * xiShiftedCassiniInverseResponseCurvature (s ^ (2 : ℕ))) _ t at hsum
  change HasDerivAt
    (fun s : ℝ =>
      2 * xiShiftedCassiniInverseResponseSlope (s ^ (2 : ℕ)) +
        4 * s ^ (2 : ℕ) * xiShiftedCassiniInverseResponseCurvature (s ^ (2 : ℕ)))
    (12 * t * xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ)) +
      8 * t ^ (3 : ℕ) * xiShiftedCassiniInverseResponseThirdJet (t ^ (2 : ℕ))) t
  convert hsum using 1
  ring

/-- Degree-one genuine crossing becomes one explicit theta-source law: the Euler radial
inflection defect vanishes while the next radial jet points strictly downward. -/
theorem xiShiftedDegreeOne_flat_negative_forces_thetaProfileEulerContact
    {t : ℝ} (ht0 : 0 < t)
    (hflat : xiShiftedDegreeOneHankelMinor (t ^ (2 : ℕ)) = 0)
    (hterminal : xiShiftedDegreeOneTerminalFlux (t ^ (2 : ℕ)) < 0) :
    t * thetaCuspCassiniInverseResponseProfileCurvature t =
        thetaCuspCassiniInverseResponseProfileSlope t ∧
      thetaCuspCassiniInverseResponseProfileThirdJet t < 0 := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hdown :=
    xiShiftedDegreeOne_flat_negative_is_downwardInverseResponseInflection
      hy hflat hterminal
  constructor
  · rw [thetaCuspCassiniInverseResponseProfileCurvature,
      thetaCuspCassiniInverseResponseProfileSlope, hdown.1]
    ring
  · rw [thetaCuspCassiniInverseResponseProfileThirdJet, hdown.1]
    have ht3 : 0 < 8 * t ^ (3 : ℕ) := by positivity
    simpa using mul_neg_of_pos_of_neg ht3 hdown.2.1

/-- Exact degree-one source reduction: a flat negative Hankel event is equivalent to radial
Euler contact followed by a negative third jet of `t Z(t) / Z'(t)`. -/
theorem xiShiftedDegreeOne_flat_negative_iff_thetaProfileEulerContact
    {t : ℝ} (ht0 : 0 < t) :
    (xiShiftedDegreeOneHankelMinor (t ^ (2 : ℕ)) = 0 ∧
        xiShiftedDegreeOneTerminalFlux (t ^ (2 : ℕ)) < 0) ↔
      (t * thetaCuspCassiniInverseResponseProfileCurvature t =
          thetaCuspCassiniInverseResponseProfileSlope t ∧
        thetaCuspCassiniInverseResponseProfileThirdJet t < 0) := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  constructor
  · rintro ⟨hflat, hterminal⟩
    exact xiShiftedDegreeOne_flat_negative_forces_thetaProfileEulerContact
      ht0 hflat hterminal
  · rintro ⟨hcontact, hthirdProfile⟩
    have hfactor4 : 0 < 4 * t ^ (3 : ℕ) := by positivity
    have hcurvature :
        xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ)) = 0 := by
      have hproduct :
          (4 * t ^ (3 : ℕ)) * xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ)) = 0 := by
        calc
          (4 * t ^ (3 : ℕ)) * xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ)) =
              t * thetaCuspCassiniInverseResponseProfileCurvature t -
                thetaCuspCassiniInverseResponseProfileSlope t := by
            rw [thetaCuspCassiniInverseResponseProfileCurvature,
              thetaCuspCassiniInverseResponseProfileSlope]
            ring
          _ = 0 := sub_eq_zero.mpr hcontact
      exact (mul_eq_zero.mp hproduct).resolve_left hfactor4.ne'
    have hflat :=
      (xiShiftedDegreeOneHankelMinor_eq_zero_iff_inverseResponseCurvature_eq_zero
        hy).mpr hcurvature
    have hfactor8 : 0 < 8 * t ^ (3 : ℕ) := by positivity
    have hthirdProduct :
        (8 * t ^ (3 : ℕ)) * xiShiftedCassiniInverseResponseThirdJet (t ^ (2 : ℕ)) < 0 := by
      simpa [thetaCuspCassiniInverseResponseProfileThirdJet, hcurvature] using
        hthirdProfile
    have hthirdMass : xiShiftedCassiniInverseResponseThirdJet (t ^ (2 : ℕ)) < 0 := by
      rcases mul_neg_iff.mp hthirdProduct with hposneg | hnegpos
      · exact hposneg.2
      · exact (not_lt_of_ge hfactor8.le hnegpos.1).elim
    have hterminal :=
      (xiShiftedDegreeOneTerminalFlux_neg_iff_inverseResponseThirdJet_neg hy).mpr
        hthirdMass
    exact ⟨hflat, hterminal⟩

end

end RHTower
