import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniInverseResponseCurvature

/-!
# Route-U degree-one contact as a theta Esscher-cumulant barrier

On the theta strip put `Z(t)=thetaCuspHyperbolicPartition t` and
`A(t)=Z'(t)/Z(t)=thetaCuspHyperbolicFlux t / Z(t)`.  The first three derivatives of `A`
are the variance, third cumulant, and fourth cumulant of the inward Esscher state.  This file
constructs those jets without differentiating under a new integral: the fixed Cassini-source
moment recursion supplies all derivatives.

The degree-one Route-U Hankel minor is exactly the negative of the radial cumulant polynomial

`N(t) = -A² - t A A' - t² A A'' + 2 t² (A')²`

divided by `8 t⁶`.  Therefore a flat first face is the zero set `N=0`.  The derivative of
`N` is an explicit mean--variance--third--fourth-cumulant flow.  Excluding a negative derivative
at its zero set is the contact-only theta barrier needed to eliminate degree-one Route-U
crossings; global reciprocal concavity is stronger than necessary.
-/

open Complex Set Filter

namespace RHTower

noncomputable section

/-- Logarithmic slope of the theta hyperbolic partition. -/
def thetaCuspCassiniEsscherMean (t : ℝ) : ℝ :=
  thetaCuspHyperbolicFlux t / thetaCuspHyperbolicPartition t

/-- First theta Esscher cumulant (variance), in shifted-Cassini coordinates. -/
def thetaCuspCassiniEsscherVariance (t : ℝ) : ℝ :=
  xiShiftedCassiniResponse (t ^ (2 : ℕ)) -
    2 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re

/-- Second theta Esscher cumulant derivative (third cumulant). -/
def thetaCuspCassiniEsscherThirdCumulant (t : ℝ) : ℝ :=
  -6 * t * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re +
    8 * t ^ (3 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 2).re

/-- Third theta Esscher cumulant derivative (fourth cumulant). -/
def thetaCuspCassiniEsscherFourthCumulant (t : ℝ) : ℝ :=
  -6 * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re +
    48 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 2).re -
    48 * t ^ (4 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 3).re

/-- Cumulant polynomial whose zero set is the degree-one Route-U flat face. -/
def thetaCuspCassiniEulerContactNumerator (t : ℝ) : ℝ :=
  -thetaCuspCassiniEsscherMean t ^ (2 : ℕ) -
    t * thetaCuspCassiniEsscherMean t * thetaCuspCassiniEsscherVariance t -
    t ^ (2 : ℕ) * thetaCuspCassiniEsscherMean t *
      thetaCuspCassiniEsscherThirdCumulant t +
    2 * t ^ (2 : ℕ) * thetaCuspCassiniEsscherVariance t ^ (2 : ℕ)

/-- Derivative of the Euler-contact numerator in the first four Esscher cumulants. -/
def thetaCuspCassiniEulerContactFlow (t : ℝ) : ℝ :=
  -3 * thetaCuspCassiniEsscherMean t * thetaCuspCassiniEsscherVariance t +
    3 * t * thetaCuspCassiniEsscherVariance t ^ (2 : ℕ) -
    3 * t * thetaCuspCassiniEsscherMean t *
      thetaCuspCassiniEsscherThirdCumulant t +
    3 * t ^ (2 : ℕ) * thetaCuspCassiniEsscherVariance t *
      thetaCuspCassiniEsscherThirdCumulant t -
    t ^ (2 : ℕ) * thetaCuspCassiniEsscherMean t *
      thetaCuspCassiniEsscherFourthCumulant t

/-- On the theta strip the hyperbolic logarithmic slope is `t` times the fixed Cassini
response. -/
theorem thetaCuspCassiniEsscherMean_eq
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniEsscherMean t =
      t * xiShiftedCassiniResponse (t ^ (2 : ℕ)) := by
  have hq :=
    xiShiftedCassiniInverseResponse_sq_eq_hyperbolicPartition_div_flux ht0 ht1
  have hresponse : xiShiftedCassiniResponse (t ^ (2 : ℕ)) ≠ 0 :=
    (xiShiftedCassiniResponse_pos (sq_pos_of_pos ht0)).ne'
  have hflux : thetaCuspHyperbolicFlux t ≠ 0 :=
    (thetaCuspHyperbolicFlux_pos ht0 ht1).ne'
  have hpart : thetaCuspHyperbolicPartition t ≠ 0 :=
    (thetaCuspHyperbolicPartition_pos (by
      rw [abs_of_pos ht0]
      exact ht1)).ne'
  rw [xiShiftedCassiniInverseResponse] at hq
  unfold thetaCuspCassiniEsscherMean
  field_simp [hresponse, hflux, hpart] at hq ⊢
  simpa [mul_assoc, mul_comm, mul_left_comm] using hq

/-- The named Esscher variance is the actual derivative of the theta logarithmic slope. -/
theorem hasDerivAt_thetaCuspCassiniEsscherMean
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt thetaCuspCassiniEsscherMean
      (thetaCuspCassiniEsscherVariance t) t := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hsq : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hresponseMass : HasDerivAt xiShiftedCassiniResponse
      (-(xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re) (t ^ (2 : ℕ)) :=
    hasDerivAt_xiShiftedCassiniResponse hy
  have hresponse := hresponseMass.comp_of_eq t hsq rfl
  change HasDerivAt (fun s : ℝ => xiShiftedCassiniResponse (s ^ (2 : ℕ))) _ t at hresponse
  have hproduct := (hasDerivAt_id t).mul hresponse
  change HasDerivAt
    (fun s : ℝ => s * xiShiftedCassiniResponse (s ^ (2 : ℕ))) _ t at hproduct
  have hlocal : Filter.EventuallyEq (nhds t) thetaCuspCassiniEsscherMean
      (fun s : ℝ => s * xiShiftedCassiniResponse (s ^ (2 : ℕ))) := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
    exact thetaCuspCassiniEsscherMean_eq hs.1 hs.2
  have hsource := hproduct.congr_of_eventuallyEq hlocal
  change HasDerivAt thetaCuspCassiniEsscherMean
    (xiShiftedCassiniResponse (t ^ (2 : ℕ)) -
      2 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re) t
  exact hsource.congr_deriv (by simp only [id_eq]; ring)

/-- Third cumulant is the actual derivative of the Esscher variance. -/
theorem hasDerivAt_thetaCuspCassiniEsscherVariance
    {t : ℝ} (ht0 : 0 < t) :
    HasDerivAt thetaCuspCassiniEsscherVariance
      (thetaCuspCassiniEsscherThirdCumulant t) t := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hsq : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hresponseMass : HasDerivAt xiShiftedCassiniResponse
      (-(xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re) (t ^ (2 : ℕ)) :=
    hasDerivAt_xiShiftedCassiniResponse hy
  have hmOneMass : HasDerivAt
      (fun y : ℝ => (xiShiftedReciprocalMoment y 1).re)
      (-2 * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 2).re) (t ^ (2 : ℕ)) := by
    convert hasDerivAt_re_xiShiftedReciprocalMoment hy 1 using 1 <;> ring
  have hresponse := hresponseMass.comp_of_eq t hsq rfl
  have hmOne := hmOneMass.comp_of_eq t hsq rfl
  change HasDerivAt (fun s : ℝ => xiShiftedCassiniResponse (s ^ (2 : ℕ))) _ t at hresponse
  change HasDerivAt
    (fun s : ℝ => (xiShiftedReciprocalMoment (s ^ (2 : ℕ)) 1).re) _ t at hmOne
  have hfactor := (hasDerivAt_pow 2 t).const_mul 2
  have hraw := hresponse.sub (hfactor.mul hmOne)
  change HasDerivAt
    (fun s : ℝ => xiShiftedCassiniResponse (s ^ (2 : ℕ)) -
      2 * s ^ (2 : ℕ) * (xiShiftedReciprocalMoment (s ^ (2 : ℕ)) 1).re) _ t at hraw
  unfold thetaCuspCassiniEsscherVariance thetaCuspCassiniEsscherThirdCumulant
  exact hraw.congr_deriv (by ring)

/-- Fourth cumulant is the actual derivative of the third cumulant. -/
theorem hasDerivAt_thetaCuspCassiniEsscherThirdCumulant
    {t : ℝ} (ht0 : 0 < t) :
    HasDerivAt thetaCuspCassiniEsscherThirdCumulant
      (thetaCuspCassiniEsscherFourthCumulant t) t := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hsq : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hmOneMass : HasDerivAt
      (fun y : ℝ => (xiShiftedReciprocalMoment y 1).re)
      (-2 * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 2).re) (t ^ (2 : ℕ)) := by
    convert hasDerivAt_re_xiShiftedReciprocalMoment hy 1 using 1 <;> ring
  have hmTwoMass : HasDerivAt
      (fun y : ℝ => (xiShiftedReciprocalMoment y 2).re)
      (-3 * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 3).re) (t ^ (2 : ℕ)) := by
    convert hasDerivAt_re_xiShiftedReciprocalMoment hy 2 using 1 <;> ring
  have hmOne := hmOneMass.comp_of_eq t hsq rfl
  have hmTwo := hmTwoMass.comp_of_eq t hsq rfl
  change HasDerivAt
    (fun s : ℝ => (xiShiftedReciprocalMoment (s ^ (2 : ℕ)) 1).re) _ t at hmOne
  change HasDerivAt
    (fun s : ℝ => (xiShiftedReciprocalMoment (s ^ (2 : ℕ)) 2).re) _ t at hmTwo
  have hfirst := ((hasDerivAt_id t).mul hmOne).const_mul (-6)
  change HasDerivAt
    (fun s : ℝ => -6 * (s *
      (xiShiftedReciprocalMoment (s ^ (2 : ℕ)) 1).re)) _ t at hfirst
  have hfactor := (hasDerivAt_pow 3 t).const_mul 8
  have hsecond := hfactor.mul hmTwo
  change HasDerivAt
    (fun s : ℝ => 8 * s ^ (3 : ℕ) *
      (xiShiftedReciprocalMoment (s ^ (2 : ℕ)) 2).re) _ t at hsecond
  have hraw := hfirst.add hsecond
  have hlocal : Filter.EventuallyEq (nhds t)
      thetaCuspCassiniEsscherThirdCumulant
      ((fun s : ℝ => -6 * (s *
        (xiShiftedReciprocalMoment (s ^ (2 : ℕ)) 1).re)) +
      (fun s : ℝ => 8 * s ^ (3 : ℕ) *
        (xiShiftedReciprocalMoment (s ^ (2 : ℕ)) 2).re)) := by
    filter_upwards [] with s
    rw [thetaCuspCassiniEsscherThirdCumulant]
    simp only [Pi.add_apply]
    ring
  have hsource := hraw.congr_of_eventuallyEq hlocal
  change HasDerivAt thetaCuspCassiniEsscherThirdCumulant
    (-6 * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 1).re +
      48 * t ^ (2 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 2).re -
      48 * t ^ (4 : ℕ) * (xiShiftedReciprocalMoment (t ^ (2 : ℕ)) 3).re) t
  exact hsource.congr_deriv (by simp only [id_eq]; ring)

/-- The Euler-contact flow is the actual derivative of the cumulant numerator. -/
theorem hasDerivAt_thetaCuspCassiniEulerContactNumerator
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt thetaCuspCassiniEulerContactNumerator
      (thetaCuspCassiniEulerContactFlow t) t := by
  have hmean := hasDerivAt_thetaCuspCassiniEsscherMean ht0 ht1
  have hvariance := hasDerivAt_thetaCuspCassiniEsscherVariance ht0
  have hthird := hasDerivAt_thetaCuspCassiniEsscherThirdCumulant ht0
  have htermOne := (hmean.pow 2).neg
  have htermTwo := (((hasDerivAt_id t).mul hmean).mul hvariance).neg
  have htermThree :=
    ((((hasDerivAt_pow 2 t).mul hmean).mul hthird)).neg
  have htermFour :=
    (((hasDerivAt_pow 2 t).mul (hvariance.pow 2))).const_mul 2
  have hraw := ((htermOne.add htermTwo).add htermThree).add htermFour
  have hlocal : Filter.EventuallyEq (nhds t)
      thetaCuspCassiniEulerContactNumerator
      (-thetaCuspCassiniEsscherMean ^ (2 : ℕ) +
        -(id * thetaCuspCassiniEsscherMean *
          thetaCuspCassiniEsscherVariance) +
        -((fun x : ℝ => x ^ (2 : ℕ)) * thetaCuspCassiniEsscherMean *
          thetaCuspCassiniEsscherThirdCumulant) +
        fun y : ℝ => 2 * (((fun x : ℝ => x ^ (2 : ℕ)) *
          thetaCuspCassiniEsscherVariance ^ (2 : ℕ)) y)) := by
    filter_upwards [] with s
    rw [thetaCuspCassiniEulerContactNumerator]
    simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.neg_apply,
      Pi.pow_apply]
    ring
  have hsource := hraw.congr_of_eventuallyEq hlocal
  change HasDerivAt thetaCuspCassiniEulerContactNumerator
    (-3 * thetaCuspCassiniEsscherMean t *
        thetaCuspCassiniEsscherVariance t +
      3 * t * thetaCuspCassiniEsscherVariance t ^ (2 : ℕ) -
      3 * t * thetaCuspCassiniEsscherMean t *
        thetaCuspCassiniEsscherThirdCumulant t +
      3 * t ^ (2 : ℕ) * thetaCuspCassiniEsscherVariance t *
        thetaCuspCassiniEsscherThirdCumulant t -
      t ^ (2 : ℕ) * thetaCuspCassiniEsscherMean t *
        thetaCuspCassiniEsscherFourthCumulant t) t
  exact hsource.congr_deriv (by
    simp only [id_eq, Pi.mul_apply, Pi.pow_apply]
    ring)

/-- Exact cumulant form of inverse-response curvature. -/
theorem thetaCuspCassiniEulerContactNumerator_eq_curvature
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniEulerContactNumerator t =
      4 * t ^ (3 : ℕ) * thetaCuspCassiniEsscherMean t ^ (3 : ℕ) *
        xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ)) := by
  have hresponse : xiShiftedCassiniResponse (t ^ (2 : ℕ)) ≠ 0 :=
    (xiShiftedCassiniResponse_pos (sq_pos_of_pos ht0)).ne'
  rw [thetaCuspCassiniEulerContactNumerator,
    thetaCuspCassiniEsscherMean_eq ht0 ht1,
    thetaCuspCassiniEsscherVariance,
    thetaCuspCassiniEsscherThirdCumulant,
    xiShiftedCassiniInverseResponseCurvature]
  field_simp [hresponse]
  ring

/-- The first shifted-Hankel minor is exactly the negative normalized theta cumulant contact
numerator. -/
theorem thetaCuspCassiniEulerContactNumerator_eq_neg_eight_mul_minor
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniEulerContactNumerator t =
      -8 * t ^ (6 : ℕ) * xiShiftedDegreeOneHankelMinor (t ^ (2 : ℕ)) := by
  rw [thetaCuspCassiniEulerContactNumerator_eq_curvature ht0 ht1,
    thetaCuspCassiniEsscherMean_eq ht0 ht1,
    xiShiftedDegreeOneHankelMinor_eq_inverseResponseCurvature
      (sq_pos_of_pos ht0)]
  ring

/-- On the theta strip, a flat first Route-U face is exactly the zero set of the explicit
Esscher-cumulant contact numerator. -/
theorem thetaCuspCassiniEulerContactNumerator_eq_zero_iff_minor_eq_zero
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    thetaCuspCassiniEulerContactNumerator t = 0 ↔
      xiShiftedDegreeOneHankelMinor (t ^ (2 : ℕ)) = 0 := by
  rw [thetaCuspCassiniEulerContactNumerator_eq_neg_eight_mul_minor ht0 ht1,
    mul_eq_zero]
  exact or_iff_right (mul_ne_zero (by norm_num)
    (pow_ne_zero 6 ht0.ne'))

/-- At a flat first face, the full cumulant flow collapses to a positive radial factor times
the third jet of the inverse-response theta profile.  Terms containing curvature vanish exactly,
so this is a contact identity rather than a global shape hypothesis. -/
theorem thetaCuspCassiniEulerContactFlow_eq_profileThirdJet_of_contact
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcontact : thetaCuspCassiniEulerContactNumerator t = 0) :
    thetaCuspCassiniEulerContactFlow t =
      t * thetaCuspCassiniEsscherMean t ^ (3 : ℕ) *
        thetaCuspCassiniInverseResponseProfileThirdJet t := by
  have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
  have hminor : xiShiftedDegreeOneHankelMinor (t ^ (2 : ℕ)) = 0 :=
    (thetaCuspCassiniEulerContactNumerator_eq_zero_iff_minor_eq_zero
      ht0 ht1).mp hcontact
  have hcurvature :
      xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ)) = 0 :=
    (xiShiftedDegreeOneHankelMinor_eq_zero_iff_inverseResponseCurvature_eq_zero
      hy).mp hminor
  have hsq : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hcurvatureMass :=
    hasDerivAt_xiShiftedCassiniInverseResponseCurvature hy
  have hcurvatureRadial := hcurvatureMass.comp_of_eq t hsq rfl
  change HasDerivAt
    (fun s : ℝ => xiShiftedCassiniInverseResponseCurvature (s ^ (2 : ℕ)))
    (xiShiftedCassiniInverseResponseThirdJet (t ^ (2 : ℕ)) * (2 * t)) t at hcurvatureRadial
  have hfactor := (hasDerivAt_pow 3 t).const_mul 4
  change HasDerivAt (fun s : ℝ => 4 * s ^ (3 : ℕ)) _ t at hfactor
  have hmean := hasDerivAt_thetaCuspCassiniEsscherMean ht0 ht1
  have hraw := (hfactor.mul (hmean.pow 3)).mul hcurvatureRadial
  have hlocal : Filter.EventuallyEq (nhds t)
      thetaCuspCassiniEulerContactNumerator
      (((fun s : ℝ => 4 * s ^ (3 : ℕ)) *
          thetaCuspCassiniEsscherMean ^ (3 : ℕ)) *
        fun s : ℝ =>
          xiShiftedCassiniInverseResponseCurvature (s ^ (2 : ℕ))) := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
    simpa only [Pi.mul_apply, Pi.pow_apply] using
      thetaCuspCassiniEulerContactNumerator_eq_curvature hs.1 hs.2
  have hsource := hraw.congr_of_eventuallyEq hlocal
  have hnamed := hasDerivAt_thetaCuspCassiniEulerContactNumerator ht0 ht1
  have hunique := hnamed.unique hsource
  rw [thetaCuspCassiniInverseResponseProfileThirdJet, hcurvature]
  simp only [mul_zero, zero_add]
  simp only [id_eq, Pi.mul_apply, Pi.pow_apply, hcurvature,
    mul_zero, add_zero, zero_mul, zero_add] at hunique
  calc
    thetaCuspCassiniEulerContactFlow t =
        4 * t ^ (3 : ℕ) * thetaCuspCassiniEsscherMean t ^ (3 : ℕ) *
          (xiShiftedCassiniInverseResponseThirdJet (t ^ (2 : ℕ)) * (2 * t)) := hunique
    _ = t * thetaCuspCassiniEsscherMean t ^ (3 : ℕ) *
        (8 * t ^ (3 : ℕ) * xiShiftedCassiniInverseResponseThirdJet (t ^ (2 : ℕ))) := by
      ring

/-- Exact degree-one crossing barrier in theta cumulants: a flat Hankel face with negative
terminal square is precisely a zero of `N` at which its explicit cumulant flow points downward. -/
theorem xiShiftedDegreeOne_flat_negative_iff_thetaCumulantContactFlow
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (xiShiftedDegreeOneHankelMinor (t ^ (2 : ℕ)) = 0 ∧
        xiShiftedDegreeOneTerminalFlux (t ^ (2 : ℕ)) < 0) ↔
      (thetaCuspCassiniEulerContactNumerator t = 0 ∧
        thetaCuspCassiniEulerContactFlow t < 0) := by
  have hmeanPos : 0 < thetaCuspCassiniEsscherMean t := by
    rw [thetaCuspCassiniEsscherMean_eq ht0 ht1]
    exact mul_pos ht0 (xiShiftedCassiniResponse_pos (sq_pos_of_pos ht0))
  have hfactorPos :
      0 < t * thetaCuspCassiniEsscherMean t ^ (3 : ℕ) :=
    mul_pos ht0 (pow_pos hmeanPos 3)
  constructor
  · rintro ⟨hflat, hterminal⟩
    have hcontact :=
      (thetaCuspCassiniEulerContactNumerator_eq_zero_iff_minor_eq_zero
        ht0 ht1).mpr hflat
    have hprofileThird :
        thetaCuspCassiniInverseResponseProfileThirdJet t < 0 :=
      (xiShiftedDegreeOne_flat_negative_forces_thetaProfileEulerContact
        ht0 hflat hterminal).2
    have hflow :=
      thetaCuspCassiniEulerContactFlow_eq_profileThirdJet_of_contact
        ht0 ht1 hcontact
    exact ⟨hcontact, hflow.symm ▸
      mul_neg_of_pos_of_neg hfactorPos hprofileThird⟩
  · rintro ⟨hcontact, hflowNeg⟩
    have hflat :=
      (thetaCuspCassiniEulerContactNumerator_eq_zero_iff_minor_eq_zero
        ht0 ht1).mp hcontact
    have hflow :=
      thetaCuspCassiniEulerContactFlow_eq_profileThirdJet_of_contact
        ht0 ht1 hcontact
    have hprofileThird :
        thetaCuspCassiniInverseResponseProfileThirdJet t < 0 := by
      rw [hflow] at hflowNeg
      rcases mul_neg_iff.mp hflowNeg with hposneg | hnegpos
      · exact hposneg.2
      · exact (not_lt_of_ge hfactorPos.le hnegpos.1).elim
    have hy : 0 < t ^ (2 : ℕ) := sq_pos_of_pos ht0
    have hcurvature :
        xiShiftedCassiniInverseResponseCurvature (t ^ (2 : ℕ)) = 0 :=
      (xiShiftedDegreeOneHankelMinor_eq_zero_iff_inverseResponseCurvature_eq_zero
        hy).mp hflat
    have hEulerContact :
        t * thetaCuspCassiniInverseResponseProfileCurvature t =
          thetaCuspCassiniInverseResponseProfileSlope t := by
      rw [thetaCuspCassiniInverseResponseProfileCurvature,
        thetaCuspCassiniInverseResponseProfileSlope, hcurvature]
      ring
    exact (xiShiftedDegreeOne_flat_negative_iff_thetaProfileEulerContact
      ht0).mpr ⟨hEulerContact, hprofileThird⟩

end

end RHTower
