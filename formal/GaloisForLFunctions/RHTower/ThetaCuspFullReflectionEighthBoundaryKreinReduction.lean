import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveDrift

open Real

namespace HilbertMetric

noncomputable section

/-- Center derivative of the reflected even jet of order zero. -/
def reflectedProductZeroJetShift (f₀ f₁ : ℝ) : ℝ := 2 * f₀ * f₁

/-- Center derivative of the reflected product second jet. -/
def reflectedProductSecondJetShift (f₀ f₁ f₂ f₃ : ℝ) : ℝ :=
  2 * (f₀ * f₃ - f₁ * f₂)

/-- Center derivative of the reflected product fourth jet. -/
def reflectedProductFourthJetShift (f₀ f₁ f₂ f₃ f₄ f₅ : ℝ) : ℝ :=
  2 * f₀ * f₅ - 6 * f₁ * f₄ + 4 * f₂ * f₃

/-- Center derivative of the reflected product sixth jet. -/
def reflectedProductSixthJetShift (f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : ℝ) : ℝ :=
  2 * f₀ * f₇ - 10 * f₁ * f₆ + 18 * f₂ * f₅ - 10 * f₃ * f₄

/-- Center derivative of the reflected product eighth jet. -/
def reflectedProductEighthJetShift
    (f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : ℝ) : ℝ :=
  2 * f₀ * f₉ - 14 * f₁ * f₈ + 40 * f₂ * f₇ -
    56 * f₃ * f₆ + 28 * f₄ * f₅

/-- First variation of the signed rank-three Hankel determinant in arbitrary moment directions. -/
def signedEvenHankelThreeFirstVariation
    (p₀ p₂ p₄ p₆ p₈ q₀ q₂ q₄ q₆ q₈ : ℝ) : ℝ :=
  q₀ * p₄ * p₈ + p₀ * q₄ * p₈ + p₀ * p₄ * q₈ -
    (q₀ * p₆ ^ 2 + 2 * p₀ * p₆ * q₆) -
    (2 * p₂ * q₂ * p₈ + p₂ ^ 2 * q₈) +
    2 * (q₂ * p₄ * p₆ + p₂ * q₄ * p₆ + p₂ * p₄ * q₆) -
    3 * p₄ ^ 2 * q₄

/-- Canonical cofactor null vector of a singular rank-three Hankel face. -/
def signedEvenHankelThreeBoundaryVector
    (p₀ p₂ p₄ p₆ : ℝ) : Fin 3 → ℝ :=
  ![p₂ * p₆ - p₄ ^ 2, p₂ * p₄ - p₀ * p₆, p₀ * p₄ - p₂ ^ 2]

/-- Quadratic crossing form of a Hankel first variation on the canonical boundary vector. -/
def signedEvenHankelThreeBoundaryCrossing
    (p₀ p₂ p₄ p₆ q₀ q₂ q₄ q₆ q₈ : ℝ) : ℝ :=
  let a := p₂ * p₆ - p₄ ^ 2
  let b := p₂ * p₄ - p₀ * p₆
  let c := p₀ * p₄ - p₂ ^ 2
  q₀ * a ^ 2 + 2 * q₂ * a * b + q₄ * (2 * a * c + b ^ 2) +
    2 * q₆ * b * c + q₈ * c ^ 2

/-- Jacobi--Krein law: on a singular rank-three face, determinant variation is the canonical
null-line crossing form divided by the strict leading rank-two minor. -/
theorem signedEvenHankelThreeFirstVariation_eq_boundaryCrossing_div
    {p₀ p₂ p₄ p₆ p₈ q₀ q₂ q₄ q₆ q₈ : ℝ}
    (hdet : signedEvenHankelThreeDet p₀ p₂ p₄ p₆ p₈ = 0)
    (hhead : p₀ * p₄ - p₂ ^ 2 ≠ 0) :
    signedEvenHankelThreeFirstVariation p₀ p₂ p₄ p₆ p₈ q₀ q₂ q₄ q₆ q₈ =
      signedEvenHankelThreeBoundaryCrossing p₀ p₂ p₄ p₆ q₀ q₂ q₄ q₆ q₈ /
        (p₀ * p₄ - p₂ ^ 2) := by
  unfold signedEvenHankelThreeDet at hdet
  field_simp [hhead]
  unfold signedEvenHankelThreeFirstVariation
    signedEvenHankelThreeBoundaryCrossing
  linear_combination (q₀ * p₄ - 2 * q₂ * p₂ + q₄ * p₀) * hdet

/-- Pure center-shift first variation of the signed rank-three reflected Hankel determinant. -/
def signedEvenHankelThreeShiftVariation (f : ℕ → ℝ) : ℝ :=
  let p₀ := f 0 ^ 2
  let p₂ := reflectedProductSecondJet (f 0) (f 1) (f 2)
  let p₄ := reflectedProductFourthJet (f 0) (f 1) (f 2) (f 3) (f 4)
  let p₆ := reflectedProductSixthJet
    (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
  let p₈ := reflectedProductEighthJet
    (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8)
  let q₀ := reflectedProductZeroJetShift (f 0) (f 1)
  let q₂ := reflectedProductSecondJetShift (f 0) (f 1) (f 2) (f 3)
  let q₄ := reflectedProductFourthJetShift (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)
  let q₆ := reflectedProductSixthJetShift
    (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  let q₈ := reflectedProductEighthJetShift
    (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9)
  signedEvenHankelThreeFirstVariation p₀ p₂ p₄ p₆ p₈ q₀ q₂ q₄ q₆ q₈

/-- The pure shift variation becomes a canonical null-line crossing form on a singular face. -/
theorem signedEvenHankelThreeShiftVariation_eq_boundaryCrossing_div
    (f : ℕ → ℝ)
    (hdet : signedEvenHankelThreeDet
      (f 0 ^ 2)
      (reflectedProductSecondJet (f 0) (f 1) (f 2))
      (reflectedProductFourthJet (f 0) (f 1) (f 2) (f 3) (f 4))
      (reflectedProductSixthJet (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6))
      (reflectedProductEighthJet
        (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8)) = 0)
    (hhead :
      f 0 ^ 2 * reflectedProductFourthJet (f 0) (f 1) (f 2) (f 3) (f 4) -
        reflectedProductSecondJet (f 0) (f 1) (f 2) ^ 2 ≠ 0) :
    signedEvenHankelThreeShiftVariation f =
      signedEvenHankelThreeBoundaryCrossing
        (f 0 ^ 2)
        (reflectedProductSecondJet (f 0) (f 1) (f 2))
        (reflectedProductFourthJet (f 0) (f 1) (f 2) (f 3) (f 4))
        (reflectedProductSixthJet (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6))
        (reflectedProductZeroJetShift (f 0) (f 1))
        (reflectedProductSecondJetShift (f 0) (f 1) (f 2) (f 3))
        (reflectedProductFourthJetShift (f 0) (f 1) (f 2) (f 3) (f 4) (f 5))
        (reflectedProductSixthJetShift
          (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7))
        (reflectedProductEighthJetShift
          (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9)) /
      (f 0 ^ 2 * reflectedProductFourthJet (f 0) (f 1) (f 2) (f 3) (f 4) -
        reflectedProductSecondJet (f 0) (f 1) (f 2) ^ 2) := by
  simpa only [signedEvenHankelThreeShiftVariation] using
    signedEvenHankelThreeFirstVariation_eq_boundaryCrossing_div hdet hhead

end

end HilbertMetric

namespace RHTower

noncomputable section

/-- The theta-source rank-three reflected determinant differentiates by pure center shift. -/
theorem hasDerivAt_thetaCuspFullSourceReflectionEighthHankelCurvature_shiftVariation
    (x : ℝ) :
    HasDerivAt thetaCuspFullSourceReflectionEighthHankelCurvature
      (HilbertMetric.signedEvenHankelThreeShiftVariation
        (fun n => iteratedDeriv n thetaCuspFullSource x)) x := by
  let F : ℕ → ℝ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource
  let f : ℕ → ℝ := fun n => F n x
  have hj (n : ℕ) : HasDerivAt (F n) (f (n + 1)) x := by
    rw [show F n = thetaCuspFullDerivative n by
      simpa only [F] using iteratedDeriv_thetaCuspFullSource n]
    simpa only [F, f, iteratedDeriv_thetaCuspFullSource] using
      hasDerivAt_thetaCuspFullDerivative n x
  let p₀ : ℝ → ℝ := fun y => F 0 y ^ 2
  let p₂ : ℝ → ℝ := fun y => 2 * (F 0 y * F 2 y - F 1 y ^ 2)
  let p₄ : ℝ → ℝ := fun y => F 0 y * F 4 y * 2 - F 1 y * F 3 y * 8 +
    F 2 y ^ 2 * 6
  let p₆ : ℝ → ℝ := fun y => F 0 y * F 6 y * 2 - F 1 y * F 5 y * 12 +
    F 2 y * F 4 y * 30 - F 3 y ^ 2 * 20
  let p₈ : ℝ → ℝ := fun y => F 0 y * F 8 y * 2 - F 1 y * F 7 y * 16 +
    F 2 y * F 6 y * 56 - F 3 y * F 5 y * 112 + F 4 y ^ 2 * 70
  have hp₀ : HasDerivAt p₀
      (HilbertMetric.reflectedProductZeroJetShift (f 0) (f 1)) x := by
    change HasDerivAt (fun y => F 0 y ^ 2) (2 * f 0 * f 1) x
    convert (hj 0).pow 2 using 1
    all_goals first | rfl | (norm_num [f])
  have hp₂ : HasDerivAt p₂
      (HilbertMetric.reflectedProductSecondJetShift (f 0) (f 1) (f 2) (f 3)) x := by
    have h := ((hj 0).mul (hj 2)).sub ((hj 1).pow 2)
    change HasDerivAt (fun y => 2 * (F 0 y * F 2 y - F 1 y ^ 2))
      (2 * (f 0 * f 3 - f 1 * f 2)) x
    convert h.const_mul 2 using 1
    all_goals try rfl
    all_goals norm_num [f]
    all_goals ring
  have hp₄ : HasDerivAt p₄
      (HilbertMetric.reflectedProductFourthJetShift
        (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)) x := by
    dsimp only [p₄,
      HilbertMetric.reflectedProductFourthJetShift]
    convert (((hj 0).mul (hj 4)).const_mul 2).sub
      (((hj 1).mul (hj 3)).const_mul 8) |>.add (((hj 2).pow 2).const_mul 6) using 1
    all_goals try rfl
    · funext y
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
      ring
    · norm_num [f]
      ring
  have hp₆ : HasDerivAt p₆
      (HilbertMetric.reflectedProductSixthJetShift
        (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)) x := by
    dsimp only [p₆,
      HilbertMetric.reflectedProductSixthJetShift]
    convert (((((hj 0).mul (hj 6)).const_mul 2).sub
      (((hj 1).mul (hj 5)).const_mul 12)).add
      (((hj 2).mul (hj 4)).const_mul 30)).sub
      (((hj 3).pow 2).const_mul 20) using 1
    all_goals try rfl
    · funext y
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
      ring
    · norm_num [f]
      ring
  have hp₈ : HasDerivAt p₈
      (HilbertMetric.reflectedProductEighthJetShift
        (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9)) x := by
    dsimp only [p₈,
      HilbertMetric.reflectedProductEighthJetShift]
    convert ((((((hj 0).mul (hj 8)).const_mul 2).sub
      (((hj 1).mul (hj 7)).const_mul 16)).add
      (((hj 2).mul (hj 6)).const_mul 56)).sub
      (((hj 3).mul (hj 5)).const_mul 112)).add
      (((hj 4).pow 2).const_mul 70) using 1
    all_goals try rfl
    · funext y
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
      ring
    · norm_num [f]
      ring
  have hdet := ((((hp₀.mul hp₄).mul hp₈).sub
      (hp₀.mul (hp₆.pow 2))).sub
      ((hp₂.pow 2).mul hp₈)).add
      (((hp₂.mul hp₄).mul hp₆).const_mul 2) |>.sub (hp₄.pow 3)
  have hfun :
      ((p₀ * p₄ * p₈ - p₀ * p₆ ^ 2 - p₂ ^ 2 * p₈ +
          fun y => 2 * (p₂ * p₄ * p₆) y) - p₄ ^ 3) =
        thetaCuspFullSourceReflectionEighthHankelCurvature := by
    funext y
    simp only [thetaCuspFullSourceReflectionEighthHankelCurvature,
      HilbertMetric.signedEvenHankelThreeDet, p₀, p₂, p₄, p₆, p₈, F,
      HilbertMetric.reflectedProductSecondJet,
      HilbertMetric.reflectedProductFourthJet,
      HilbertMetric.reflectedProductSixthJet,
      HilbertMetric.reflectedProductEighthJet,
      Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
    ring
  rw [hfun] at hdet
  simp only [Pi.mul_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub] at hdet
  refine hdet.congr_deriv ?_
  dsimp only [HilbertMetric.signedEvenHankelThreeShiftVariation,
    HilbertMetric.signedEvenHankelThreeFirstVariation,
    HilbertMetric.reflectedProductSecondJet,
    HilbertMetric.reflectedProductFourthJet,
    HilbertMetric.reflectedProductSixthJet,
    HilbertMetric.reflectedProductEighthJet,
    p₀, p₂, p₄, p₆, p₈, f, F]
  ring

/-- Intrinsic numerator after quotienting the raw reflected determinant by source weight six. -/
def thetaCuspFullSourceReflectionEighthProjectiveShiftNumerator (x : ℝ) : ℝ :=
  let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource x
  f 0 * HilbertMetric.signedEvenHankelThreeShiftVariation f -
    6 * f 1 * thetaCuspFullSourceReflectionEighthHankelCurvature x

/-- Projective D1 differentiates by the intrinsic ninth-jet numerator. -/
theorem hasDerivAt_thetaCuspReflectedEighthSourceProjectiveValue_shiftNumerator
    (x : ℝ) :
    HasDerivAt thetaCuspReflectedEighthSourceProjectiveValue
      (thetaCuspFullSourceReflectionEighthProjectiveShiftNumerator x /
        thetaCuspFullSource x ^ 7) x := by
  have hraw :=
    hasDerivAt_thetaCuspFullSourceReflectionEighthHankelCurvature_shiftVariation x
  have hsource : HasDerivAt thetaCuspFullSource
      (iteratedDeriv 1 thetaCuspFullSource x) x := by
    have h := hasDerivAt_thetaCuspFullDerivative 0 x
    rw [← iteratedDeriv_thetaCuspFullSource 0,
      ← iteratedDeriv_thetaCuspFullSource 1] at h
    simpa using h
  have hpos := thetaCuspFullSource_pos_all x
  have hquot := hraw.div (hsource.pow 6) (pow_ne_zero 6 hpos.ne')
  have hfun :
      (fun y => thetaCuspFullSourceReflectionEighthHankelCurvature y /
        thetaCuspFullSource y ^ 6) =
      thetaCuspReflectedEighthSourceProjectiveValue := by
    funext y
    exact (thetaCuspReflectedEighthSourceProjectiveValue_eq_raw_div_source_pow_six y).symm
  change HasDerivAt
    (fun y => thetaCuspFullSourceReflectionEighthHankelCurvature y /
      thetaCuspFullSource y ^ 6) _ x at hquot
  rw [hfun] at hquot
  refine hquot.congr_deriv ?_
  unfold thetaCuspFullSourceReflectionEighthProjectiveShiftNumerator
  simp only [Pi.pow_apply, iteratedDeriv_zero]
  field_simp [hpos.ne']
  ring

/-- Modular projective drift and intrinsic ninth-jet drift have exactly the same sign. -/
theorem thetaCuspReflectedEighthSourceProjectiveDrift_pos_iff_shiftNumerator_pos
    (x : ℝ) :
    0 < thetaCuspReflectedEighthSourceProjectiveDrift x ↔
      0 < thetaCuspFullSourceReflectionEighthProjectiveShiftNumerator x := by
  have hmod := hasDerivAt_thetaCuspReflectedEighthSourceProjectiveValue x
  have hshift :=
    hasDerivAt_thetaCuspReflectedEighthSourceProjectiveValue_shiftNumerator x
  have heq := hmod.unique hshift
  have hqpos : 0 < (thetaCuspModularSourcePositiveState
      HTGeometry.ModularThetaSourcePositiveState.Q x).re := by
    rw [thetaCuspModularSourcePositiveState_Q_eq_sourceFactor]
    exact thetaCuspModularSourceFactor_re_pos x
  have hsource := thetaCuspFullSource_pos_all x
  have hq7 : 0 < (thetaCuspModularSourcePositiveState
      HTGeometry.ModularThetaSourcePositiveState.Q x).re ^ 7 := pow_pos hqpos 7
  have hs7 : 0 < thetaCuspFullSource x ^ 7 := pow_pos hsource 7
  constructor
  · intro h
    have hdiv : 0 < thetaCuspReflectedEighthSourceProjectiveDrift x /
        (thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.Q x).re ^ 7 := div_pos h hq7
    rw [heq] at hdiv
    exact (div_pos_iff_of_pos_right hs7).mp hdiv
  · intro h
    have hdiv : 0 < thetaCuspFullSourceReflectionEighthProjectiveShiftNumerator x /
        thetaCuspFullSource x ^ 7 := div_pos h hs7
    rw [← heq] at hdiv
    exact (div_pos_iff_of_pos_right hq7).mp hdiv

/-- At a singular rank-three face, projectivization removes every connection term: orientation is
the pure shifted null-face variation. -/
theorem thetaCuspReflectedEighthSourceProjectiveDrift_pos_iff_shiftVariation_pos_of_zero
    {x : ℝ} (hzero : thetaCuspFullSourceReflectionEighthHankelCurvature x = 0) :
    0 < thetaCuspReflectedEighthSourceProjectiveDrift x ↔
      0 < HilbertMetric.signedEvenHankelThreeShiftVariation
        (fun n => iteratedDeriv n thetaCuspFullSource x) := by
  rw [thetaCuspReflectedEighthSourceProjectiveDrift_pos_iff_shiftNumerator_pos]
  unfold thetaCuspFullSourceReflectionEighthProjectiveShiftNumerator
  rw [hzero]
  simp only [mul_zero, sub_zero, iteratedDeriv_zero]
  rw [mul_pos_iff_of_pos_left (thetaCuspFullSource_pos_all x)]

/-- Canonical null-line crossing form for the center shift of the theta rank-three face. -/
def thetaCuspFullSourceReflectionEighthBoundaryCrossing (x : ℝ) : ℝ :=
  let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource x
  HilbertMetric.signedEvenHankelThreeBoundaryCrossing
    (f 0 ^ 2)
    (HilbertMetric.reflectedProductSecondJet (f 0) (f 1) (f 2))
    (HilbertMetric.reflectedProductFourthJet (f 0) (f 1) (f 2) (f 3) (f 4))
    (HilbertMetric.reflectedProductSixthJet
      (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6))
    (HilbertMetric.reflectedProductZeroJetShift (f 0) (f 1))
    (HilbertMetric.reflectedProductSecondJetShift (f 0) (f 1) (f 2) (f 3))
    (HilbertMetric.reflectedProductFourthJetShift
      (f 0) (f 1) (f 2) (f 3) (f 4) (f 5))
    (HilbertMetric.reflectedProductSixthJetShift
      (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7))
    (HilbertMetric.reflectedProductEighthJetShift
      (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9))

/-- On a positive singular theta face, projective drift orientation is exactly orientation of
the canonical null-line crossing form. -/
theorem thetaCuspReflectedEighthSourceProjectiveDrift_pos_iff_boundaryCrossing_pos_of_zero
    {x : ℝ} (hx : 0 < x)
    (hzero : thetaCuspFullSourceReflectionEighthHankelCurvature x = 0) :
    0 < thetaCuspReflectedEighthSourceProjectiveDrift x ↔
      0 < thetaCuspFullSourceReflectionEighthBoundaryCrossing x := by
  rw [thetaCuspReflectedEighthSourceProjectiveDrift_pos_iff_shiftVariation_pos_of_zero
    hzero]
  let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource x
  have hdet : HilbertMetric.signedEvenHankelThreeDet
      (f 0 ^ 2)
      (HilbertMetric.reflectedProductSecondJet (f 0) (f 1) (f 2))
      (HilbertMetric.reflectedProductFourthJet (f 0) (f 1) (f 2) (f 3) (f 4))
      (HilbertMetric.reflectedProductSixthJet
        (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6))
      (HilbertMetric.reflectedProductEighthJet
        (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8)) = 0 := by
    simpa only [thetaCuspFullSourceReflectionEighthHankelCurvature, f] using hzero
  have hheadPos : 0 <
      f 0 ^ 2 * HilbertMetric.reflectedProductFourthJet
        (f 0) (f 1) (f 2) (f 3) (f 4) -
      HilbertMetric.reflectedProductSecondJet (f 0) (f 1) (f 2) ^ 2 := by
    simpa only [thetaCuspSourceReflectionJetZero,
      thetaCuspSourceReflectionJetTwo, thetaCuspSourceReflectionJetFour,
      HilbertMetric.reflectedProductSecondJet,
      HilbertMetric.reflectedProductFourthJet, iteratedDeriv_zero, f] using
        thetaCuspSourceReflectionFourthHankel_pos hx
  rw [HilbertMetric.signedEvenHankelThreeShiftVariation_eq_boundaryCrossing_div
    f hdet hheadPos.ne']
  change 0 < thetaCuspFullSourceReflectionEighthBoundaryCrossing x /
      (f 0 ^ 2 * HilbertMetric.reflectedProductFourthJet
        (f 0) (f 1) (f 2) (f 3) (f 4) -
      HilbertMetric.reflectedProductSecondJet (f 0) (f 1) (f 2) ^ 2) ↔ _
  rw [div_pos_iff_of_pos_right hheadPos]

end

end RHTower

