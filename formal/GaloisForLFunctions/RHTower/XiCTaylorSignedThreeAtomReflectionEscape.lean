import GaloisForLFunctions.RHTower.XiCTaylorSignedTwoAtomReflectionRigidity

/-!
# Three atoms are the sharp reflection-coherent scalar escape

Two active atoms are reflection-rigid.  This module proves that the arity bound is sharp.
At a full-turn point, atoms at `T, 2T, 3T` have positive real phases `r, r², r³`.  An explicit
nonzero ray lies in both value kernels at centered heights `y` and `-y`, while its derivative
charge is nonzero on both sides.  After a reflected `r³` rescaling, the two charges agree.

Explicit bounded corrections normalize both completion values to one and allow the connection
correction required by the scalar source law.  The resulting reflected pair has exact unit
anisotropic charge at every positive mesh width.  Normalized weights converge to projectively
equal nonzero rays off the centered line.

This is a sharpness theorem, not an RH construction: it proves that reflection-projective
coherence alone cannot exclude three active atoms.  Any further Route-J no-go must use stronger
source information than the two-atom theorem.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Point whose first source atom has full-turn phase. -/
def signedThreeAtomFullTurnPoint (T y : ℝ) : ℂ :=
  ⟨2 * Real.pi / T, y⟩

/-- Literal three-atom signed completion at source times `T,2T,3T`. -/
def signedThreeAtomCompletion
    (T a₁ a₂ a₃ : ℝ) (z : ℂ) : ℂ :=
  signedFourAtomCompletion T a₁ a₂ a₃ 0 z

/-- First spectral derivative of the three-atom completion. -/
def signedThreeAtomCompletionDerivative
    (T a₁ a₂ a₃ : ℝ) (z : ℂ) : ℂ :=
  signedFourAtomCompletionDerivative T a₁ a₂ a₃ 0 z

def signedThreeAtomFullTurnCoefficient (r : ℝ) (j : ℕ) : ℝ :=
  1 - r ^ j

/-- Real-coordinate value at a full-turn point. -/
def signedThreeAtomFullTurnValue
    (r a₁ a₂ a₃ : ℝ) : ℂ :=
  ⟨a₁ * signedThreeAtomFullTurnCoefficient r 1 +
      a₂ * signedThreeAtomFullTurnCoefficient r 2 +
      a₃ * signedThreeAtomFullTurnCoefficient r 3,
    0⟩

/-- Real-coordinate derivative at a full-turn point. -/
def signedThreeAtomFullTurnDerivative
    (T r a₁ a₂ a₃ : ℝ) : ℂ :=
  ⟨0, -T * r * a₁ - 2 * T * r ^ (2 : ℕ) * a₂ -
    3 * T * r ^ (3 : ℕ) * a₃⟩

theorem spectralTranslationPhase_fullTurn
    {T : ℝ} (hT : T ≠ 0) (y : ℝ) :
    spectralTranslationPhase T (signedThreeAtomFullTurnPoint T y) =
      (Real.exp (-T * y) : ℂ) := by
  apply Complex.ext
  · rw [spectralTranslationPhase_re_eq]
    simp only [signedThreeAtomFullTurnPoint, ofReal_re]
    rw [show T * (2 * Real.pi / T) = 2 * Real.pi by field_simp]
    rw [Real.cos_two_pi]
    simp
  · rw [spectralTranslationPhase_im_eq]
    simp only [signedThreeAtomFullTurnPoint, ofReal_im]
    rw [show T * (2 * Real.pi / T) = 2 * Real.pi by field_simp]
    rw [Real.sin_two_pi]
    simp

theorem signedThreeAtomCompletion_of_phase
    {T r a₁ a₂ a₃ : ℝ} {z : ℂ}
    (h₁ : spectralTranslationPhase T z = (r : ℂ))
    (h₂ : spectralTranslationPhase (2 * T) z = (r : ℂ) ^ (2 : ℕ))
    (h₃ : spectralTranslationPhase (3 * T) z = (r : ℂ) ^ (3 : ℕ)) :
    signedThreeAtomCompletion T a₁ a₂ a₃ z =
      signedThreeAtomFullTurnValue r a₁ a₂ a₃ := by
  rw [signedThreeAtomCompletion, signedFourAtomCompletion, h₁, h₂, h₃]
  apply Complex.ext <;>
    norm_num [signedThreeAtomFullTurnValue,
      signedThreeAtomFullTurnCoefficient, pow_succ,
      Complex.mul_re, Complex.mul_im]

theorem signedThreeAtomCompletionDerivative_of_phase
    {T r a₁ a₂ a₃ : ℝ} {z : ℂ}
    (h₁ : spectralTranslationPhase T z = (r : ℂ))
    (h₂ : spectralTranslationPhase (2 * T) z = (r : ℂ) ^ (2 : ℕ))
    (h₃ : spectralTranslationPhase (3 * T) z = (r : ℂ) ^ (3 : ℕ)) :
    signedThreeAtomCompletionDerivative T a₁ a₂ a₃ z =
      signedThreeAtomFullTurnDerivative T r a₁ a₂ a₃ := by
  rw [signedThreeAtomCompletionDerivative,
    signedFourAtomCompletionDerivative, h₁, h₂, h₃]
  apply Complex.ext
  · norm_num [signedThreeAtomFullTurnDerivative, pow_succ,
      Complex.mul_re, Complex.mul_im]
  · norm_num [signedThreeAtomFullTurnDerivative, pow_succ,
      Complex.mul_re, Complex.mul_im]
    ring

theorem signedThreeAtomCompletion_fullTurn_eq
    {T : ℝ} (hT : T ≠ 0) (y a₁ a₂ a₃ : ℝ) :
    signedThreeAtomCompletion T a₁ a₂ a₃
        (signedThreeAtomFullTurnPoint T y) =
      signedThreeAtomFullTurnValue (Real.exp (-T * y)) a₁ a₂ a₃ := by
  have hbase := spectralTranslationPhase_fullTurn hT y
  have htwo :
      spectralTranslationPhase (2 * T) (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (2 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (2 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 2 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  have hthree :
      spectralTranslationPhase (3 * T) (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (3 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (3 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 3 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  exact signedThreeAtomCompletion_of_phase hbase htwo hthree

theorem signedThreeAtomCompletionDerivative_fullTurn_eq
    {T : ℝ} (hT : T ≠ 0) (y a₁ a₂ a₃ : ℝ) :
    signedThreeAtomCompletionDerivative T a₁ a₂ a₃
        (signedThreeAtomFullTurnPoint T y) =
      signedThreeAtomFullTurnDerivative T
        (Real.exp (-T * y)) a₁ a₂ a₃ := by
  have hbase := spectralTranslationPhase_fullTurn hT y
  have htwo :
      spectralTranslationPhase (2 * T) (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (2 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (2 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 2 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  have hthree :
      spectralTranslationPhase (3 * T) (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (3 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (3 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 3 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  exact signedThreeAtomCompletionDerivative_of_phase hbase htwo hthree

/-- First coordinate of the common reflected value-kernel ray. -/
def signedThreeAtomReflectionRayOne (r : ℝ) : ℝ :=
  -(1 - r ^ (3 : ℕ))

/-- Second coordinate of the common reflected value-kernel ray. -/
def signedThreeAtomReflectionRayTwo (r : ℝ) : ℝ :=
  1 - r ^ (3 : ℕ)

/-- Third coordinate of the common reflected value-kernel ray. -/
def signedThreeAtomReflectionRayThree (r : ℝ) : ℝ :=
  -r * (1 - r)

/-- Derivative charge of the common ray at radius `r`. -/
def signedThreeAtomReflectionRayCharge (T r : ℝ) : ℝ :=
  T * r * (1 - r) ^ (2 : ℕ) * (1 - r ^ (2 : ℕ))

theorem signedThreeAtomReflectionRay_value_zero (r : ℝ) :
    signedThreeAtomFullTurnValue r
      (signedThreeAtomReflectionRayOne r)
      (signedThreeAtomReflectionRayTwo r)
      (signedThreeAtomReflectionRayThree r) = 0 := by
  apply Complex.ext
  · simp [signedThreeAtomFullTurnValue,
      signedThreeAtomFullTurnCoefficient,
      signedThreeAtomReflectionRayOne,
      signedThreeAtomReflectionRayTwo,
      signedThreeAtomReflectionRayThree]
    ring
  · simp [signedThreeAtomFullTurnValue]

theorem signedThreeAtomReflectionRay_derivative
    (T r : ℝ) :
    signedThreeAtomFullTurnDerivative T r
        (signedThreeAtomReflectionRayOne r)
        (signedThreeAtomReflectionRayTwo r)
        (signedThreeAtomReflectionRayThree r) =
      ⟨0, signedThreeAtomReflectionRayCharge T r⟩ := by
  apply Complex.ext
  · simp [signedThreeAtomFullTurnDerivative]
  · simp [signedThreeAtomFullTurnDerivative,
      signedThreeAtomReflectionRayOne,
      signedThreeAtomReflectionRayTwo,
      signedThreeAtomReflectionRayThree,
      signedThreeAtomReflectionRayCharge]
    ring

theorem signedThreeAtomReflectionRay_reflectedValue_zero
    {r : ℝ} (hr : r ≠ 0) :
    signedThreeAtomFullTurnValue (1 / r)
      (signedThreeAtomReflectionRayOne r)
      (signedThreeAtomReflectionRayTwo r)
      (signedThreeAtomReflectionRayThree r) = 0 := by
  apply Complex.ext
  · simp [signedThreeAtomFullTurnValue,
      signedThreeAtomFullTurnCoefficient,
      signedThreeAtomReflectionRayOne,
      signedThreeAtomReflectionRayTwo,
      signedThreeAtomReflectionRayThree]
    field_simp [hr]
    ring
  · simp [signedThreeAtomFullTurnValue]

/-- Rescaling the reflected copy by `r³` makes its derivative charge equal to the original. -/
theorem signedThreeAtomReflectionRay_reflectedDerivative
    {T r : ℝ} (hr : r ≠ 0) :
    signedThreeAtomFullTurnDerivative T (1 / r)
        (r ^ (3 : ℕ) * signedThreeAtomReflectionRayOne r)
        (r ^ (3 : ℕ) * signedThreeAtomReflectionRayTwo r)
        (r ^ (3 : ℕ) * signedThreeAtomReflectionRayThree r) =
      ⟨0, signedThreeAtomReflectionRayCharge T r⟩ := by
  apply Complex.ext
  · simp [signedThreeAtomFullTurnDerivative]
  · simp [signedThreeAtomFullTurnDerivative,
      signedThreeAtomReflectionRayOne,
      signedThreeAtomReflectionRayTwo,
      signedThreeAtomReflectionRayThree,
      signedThreeAtomReflectionRayCharge]
    field_simp [hr]
    ring

theorem signedThreeAtomReflectionRayCharge_ne_zero
    {T r : ℝ} (hT : T ≠ 0) (hrpos : 0 < r) (hr1 : r ≠ 1) :
    signedThreeAtomReflectionRayCharge T r ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero hT hrpos.ne')
      (pow_ne_zero 2 (sub_ne_zero.mpr hr1.symm)))
    (by
      have : 1 - r ^ (2 : ℕ) ≠ 0 := by
        intro hs
        have hrsq : r ^ (2 : ℕ) = 1 := by linarith
        have hrsq' : r ^ (2 : ℕ) = (1 : ℝ) ^ (2 : ℕ) := by simpa using hrsq
        rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hrsq' with h | h
        · exact hr1 h
        · nlinarith
      exact this)

/-- Determinant of the first two value/derivative columns. -/
def signedThreeAtomCorrectionDet (T r : ℝ) : ℝ :=
  T * r * (1 - r) ^ (2 : ℕ)

def signedThreeAtomCorrectionOne (T r c : ℝ) : ℝ :=
  (-2 * T * r ^ (2 : ℕ) - (1 - r ^ (2 : ℕ)) * c) /
    signedThreeAtomCorrectionDet T r

def signedThreeAtomCorrectionTwo (T r c : ℝ) : ℝ :=
  ((1 - r) * c + T * r) /
    signedThreeAtomCorrectionDet T r

theorem signedThreeAtomCorrectionDet_ne_zero
    {T r : ℝ} (hT : T ≠ 0) (hr : r ≠ 0) (hr1 : r ≠ 1) :
    signedThreeAtomCorrectionDet T r ≠ 0 :=
  mul_ne_zero (mul_ne_zero hT hr)
    (pow_ne_zero 2 (sub_ne_zero.mpr hr1.symm))

theorem signedThreeAtomCorrection_value
    {T r : ℝ} (hT : T ≠ 0) (hr : r ≠ 0) (hr1 : r ≠ 1)
    (c : ℝ) :
    (1 - r) * signedThreeAtomCorrectionOne T r c +
      (1 - r ^ (2 : ℕ)) * signedThreeAtomCorrectionTwo T r c = 1 := by
  have hdet := signedThreeAtomCorrectionDet_ne_zero hT hr hr1
  simp only [signedThreeAtomCorrectionOne,
    signedThreeAtomCorrectionTwo, signedThreeAtomCorrectionDet]
  field_simp [hdet]
  ring

theorem signedThreeAtomCorrection_derivative
    {T r : ℝ} (hT : T ≠ 0) (hr : r ≠ 0) (hr1 : r ≠ 1)
    (c : ℝ) :
    (-T * r) * signedThreeAtomCorrectionOne T r c +
      (-2 * T * r ^ (2 : ℕ)) * signedThreeAtomCorrectionTwo T r c = c := by
  have hdet := signedThreeAtomCorrectionDet_ne_zero hT hr hr1
  simp only [signedThreeAtomCorrectionOne,
    signedThreeAtomCorrectionTwo, signedThreeAtomCorrectionDet]
  field_simp [hdet]
  ring

def signedThreeAtomPlusWeightOne (T r δ c : ℝ) : ℝ :=
  signedThreeAtomReflectionRayOne r /
      signedThreeAtomReflectionRayCharge T r / δ +
    signedThreeAtomCorrectionOne T r c

def signedThreeAtomPlusWeightTwo (T r δ c : ℝ) : ℝ :=
  signedThreeAtomReflectionRayTwo r /
      signedThreeAtomReflectionRayCharge T r / δ +
    signedThreeAtomCorrectionTwo T r c

def signedThreeAtomPlusWeightThree (T r δ : ℝ) : ℝ :=
  signedThreeAtomReflectionRayThree r /
    signedThreeAtomReflectionRayCharge T r / δ

def signedThreeAtomMinusWeightOne (T r δ c : ℝ) : ℝ :=
  r ^ (3 : ℕ) * signedThreeAtomReflectionRayOne r /
      signedThreeAtomReflectionRayCharge T r / δ +
    signedThreeAtomCorrectionOne T (1 / r) c

def signedThreeAtomMinusWeightTwo (T r δ c : ℝ) : ℝ :=
  r ^ (3 : ℕ) * signedThreeAtomReflectionRayTwo r /
      signedThreeAtomReflectionRayCharge T r / δ +
    signedThreeAtomCorrectionTwo T (1 / r) c

def signedThreeAtomMinusWeightThree (T r δ : ℝ) : ℝ :=
  r ^ (3 : ℕ) * signedThreeAtomReflectionRayThree r /
    signedThreeAtomReflectionRayCharge T r / δ

/-- Exact scalar jet at the positive centered height. -/
theorem signedThreeAtomPlusJet
    {T r δ : ℝ} (hT : T ≠ 0) (hrpos : 0 < r) (hr1 : r ≠ 1)
    (hδ : δ ≠ 0) (c : ℝ) :
    signedThreeAtomFullTurnValue r
        (signedThreeAtomPlusWeightOne T r δ c)
        (signedThreeAtomPlusWeightTwo T r δ c)
        (signedThreeAtomPlusWeightThree T r δ) = 1 ∧
      signedThreeAtomFullTurnDerivative T r
        (signedThreeAtomPlusWeightOne T r δ c)
        (signedThreeAtomPlusWeightTwo T r δ c)
        (signedThreeAtomPlusWeightThree T r δ) =
          ⟨0, 1 / δ + c⟩ := by
  have hr := hrpos.ne'
  have hm := signedThreeAtomReflectionRayCharge_ne_zero hT hrpos hr1
  have hg₂ : 1 - r ^ (2 : ℕ) ≠ 0 := by
    intro h
    have hrsq : r ^ (2 : ℕ) = (1 : ℝ) ^ (2 : ℕ) := by nlinarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hrsq with hEq | hNeg
    · exact hr1 hEq
    · nlinarith
  constructor
  · apply Complex.ext
    · simp [signedThreeAtomFullTurnValue,
        signedThreeAtomFullTurnCoefficient,
        signedThreeAtomPlusWeightOne,
        signedThreeAtomPlusWeightTwo,
        signedThreeAtomPlusWeightThree,
        signedThreeAtomReflectionRayOne,
        signedThreeAtomReflectionRayTwo,
        signedThreeAtomReflectionRayThree,
        signedThreeAtomReflectionRayCharge,
        signedThreeAtomCorrectionOne,
        signedThreeAtomCorrectionTwo,
        signedThreeAtomCorrectionDet]
      field_simp [hδ, hT, hr, hr1, hm, hg₂]
      ring
    · simp [signedThreeAtomFullTurnValue]
  · apply Complex.ext
    · simp [signedThreeAtomFullTurnDerivative]
    · simp [signedThreeAtomFullTurnDerivative,
        signedThreeAtomPlusWeightOne,
        signedThreeAtomPlusWeightTwo,
        signedThreeAtomPlusWeightThree,
        signedThreeAtomReflectionRayOne,
        signedThreeAtomReflectionRayTwo,
        signedThreeAtomReflectionRayThree,
        signedThreeAtomReflectionRayCharge,
        signedThreeAtomCorrectionOne,
        signedThreeAtomCorrectionTwo,
        signedThreeAtomCorrectionDet]
      field_simp [hδ, hT, hr, hr1, hm, hg₂]
      ring

/-- Exact scalar jet at the reflected centered height, with the same unit leading charge. -/
theorem signedThreeAtomMinusJet
    {T r δ : ℝ} (hT : T ≠ 0) (hrpos : 0 < r) (hr1 : r ≠ 1)
    (hδ : δ ≠ 0) (c : ℝ) :
    signedThreeAtomFullTurnValue (1 / r)
        (signedThreeAtomMinusWeightOne T r δ c)
        (signedThreeAtomMinusWeightTwo T r δ c)
        (signedThreeAtomMinusWeightThree T r δ) = 1 ∧
      signedThreeAtomFullTurnDerivative T (1 / r)
        (signedThreeAtomMinusWeightOne T r δ c)
        (signedThreeAtomMinusWeightTwo T r δ c)
        (signedThreeAtomMinusWeightThree T r δ) =
          ⟨0, 1 / δ + c⟩ := by
  have hr := hrpos.ne'
  have hm := signedThreeAtomReflectionRayCharge_ne_zero hT hrpos hr1
  have hg₂ : 1 - r ^ (2 : ℕ) ≠ 0 := by
    intro h
    have hrsq : r ^ (2 : ℕ) = (1 : ℝ) ^ (2 : ℕ) := by nlinarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hrsq with hEq | hNeg
    · exact hr1 hEq
    · nlinarith
  constructor
  · apply Complex.ext
    · simp [signedThreeAtomFullTurnValue,
        signedThreeAtomFullTurnCoefficient,
        signedThreeAtomMinusWeightOne,
        signedThreeAtomMinusWeightTwo,
        signedThreeAtomMinusWeightThree,
        signedThreeAtomReflectionRayOne,
        signedThreeAtomReflectionRayTwo,
        signedThreeAtomReflectionRayThree,
        signedThreeAtomReflectionRayCharge,
        signedThreeAtomCorrectionOne,
        signedThreeAtomCorrectionTwo,
        signedThreeAtomCorrectionDet]
      field_simp [hδ, hT, hr, hr1, hm, hg₂]
      ring
    · simp [signedThreeAtomFullTurnValue]
  · apply Complex.ext
    · simp [signedThreeAtomFullTurnDerivative]
    · simp [signedThreeAtomFullTurnDerivative,
        signedThreeAtomMinusWeightOne,
        signedThreeAtomMinusWeightTwo,
        signedThreeAtomMinusWeightThree,
        signedThreeAtomReflectionRayOne,
        signedThreeAtomReflectionRayTwo,
        signedThreeAtomReflectionRayThree,
        signedThreeAtomReflectionRayCharge,
        signedThreeAtomCorrectionOne,
        signedThreeAtomCorrectionTwo,
        signedThreeAtomCorrectionDet]
      field_simp [hδ, hT, hr, hr1, hm, hg₂]
      ring

theorem atomicSourceConnection_exactUnitScaledCharge
    {δ : ℝ} (hδ : δ ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    δ * (atomicSourceConnectionDerivative 1
      (I * ((1 / δ + (1 / z).im : ℝ) : ℂ)) z /
        atomicSourceConnectionValue 1 z).im = 1 := by
  rw [atomicSourceConnection_logDerivative_eq one_ne_zero hz]
  rw [div_one, sub_im]
  simp only [mul_im, I_re, ofReal_im, mul_zero, I_im,
    ofReal_re, one_mul]
  field_simp [hδ]
  ring

/-- Exact off-center reflected pair.  It has value one and exact unit connection charge on both
sides, without placing a target multiplicity into the leading ray. -/
theorem signedThreeAtomFullTurn_reflectionExactPair
    {T δ y : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hy : y ≠ 0) :
    let r := Real.exp (-T * y)
    let zp := signedThreeAtomFullTurnPoint T y
    let zm := signedThreeAtomFullTurnPoint T (-y)
    signedThreeAtomCompletion T
        (signedThreeAtomPlusWeightOne T r δ (1 / zp).im)
        (signedThreeAtomPlusWeightTwo T r δ (1 / zp).im)
        (signedThreeAtomPlusWeightThree T r δ) zp = 1 ∧
      signedThreeAtomCompletionDerivative T
        (signedThreeAtomPlusWeightOne T r δ (1 / zp).im)
        (signedThreeAtomPlusWeightTwo T r δ (1 / zp).im)
        (signedThreeAtomPlusWeightThree T r δ) zp =
          I * ((1 / δ + (1 / zp).im : ℝ) : ℂ) ∧
      δ * (atomicSourceConnectionDerivative 1
        (I * ((1 / δ + (1 / zp).im : ℝ) : ℂ)) zp /
          atomicSourceConnectionValue 1 zp).im = 1 ∧
      signedThreeAtomCompletion T
        (signedThreeAtomMinusWeightOne T r δ (1 / zm).im)
        (signedThreeAtomMinusWeightTwo T r δ (1 / zm).im)
        (signedThreeAtomMinusWeightThree T r δ) zm = 1 ∧
      signedThreeAtomCompletionDerivative T
        (signedThreeAtomMinusWeightOne T r δ (1 / zm).im)
        (signedThreeAtomMinusWeightTwo T r δ (1 / zm).im)
        (signedThreeAtomMinusWeightThree T r δ) zm =
          I * ((1 / δ + (1 / zm).im : ℝ) : ℂ) ∧
      δ * (atomicSourceConnectionDerivative 1
        (I * ((1 / δ + (1 / zm).im : ℝ) : ℂ)) zm /
          atomicSourceConnectionValue 1 zm).im = 1 := by
  dsimp only
  have hT0 := hT.ne'
  let r := Real.exp (-T * y)
  have hrpos : 0 < r := Real.exp_pos _
  have hr1 : r ≠ 1 := by
    intro hr
    dsimp only [r] at hr
    have hr' : Real.exp (-(T * y)) = 1 := by
      simpa only [neg_mul] using hr
    have harg : -(T * y) = 0 :=
      (Real.exp_eq_one_iff (-(T * y))).mp hr'
    exact hy (by nlinarith)
  let zp := signedThreeAtomFullTurnPoint T y
  let zm := signedThreeAtomFullTurnPoint T (-y)
  have hzp : zp ≠ 0 := by
    intro hz
    have hre : zp.re = 0 := by rw [hz]; rfl
    have hrePos : 0 < zp.re := by
      dsimp only [zp, signedThreeAtomFullTurnPoint]
      positivity
    linarith
  have hzm : zm ≠ 0 := by
    intro hz
    have hre : zm.re = 0 := by rw [hz]; rfl
    have hrePos : 0 < zm.re := by
      dsimp only [zm, signedThreeAtomFullTurnPoint]
      positivity
    linarith
  have hplus :=
    signedThreeAtomPlusJet hT0 hrpos hr1 hδ.ne' (1 / zp).im
  have hminus :=
    signedThreeAtomMinusJet hT0 hrpos hr1 hδ.ne' (1 / zm).im
  have hrminus :
      Real.exp (-T * (-y)) = 1 / r := by
    dsimp only [r]
    rw [show -T * -y = T * y by ring, one_div, ← Real.exp_neg]
    congr 1
    ring
  refine ⟨?_, ?_, atomicSourceConnection_exactUnitScaledCharge hδ.ne' hzp,
    ?_, ?_, atomicSourceConnection_exactUnitScaledCharge hδ.ne' hzm⟩
  · rw [signedThreeAtomCompletion_fullTurn_eq hT0]
    simpa only [r, zp] using hplus.1
  · rw [signedThreeAtomCompletionDerivative_fullTurn_eq hT0]
    simpa [r, zp, Complex.ext_iff, Complex.mul_re,
      Complex.mul_im] using hplus.2
  · rw [signedThreeAtomCompletion_fullTurn_eq hT0, hrminus]
    simpa only [r, zm] using hminus.1
  · rw [signedThreeAtomCompletionDerivative_fullTurn_eq hT0, hrminus]
    simpa [r, zm, Complex.ext_iff, Complex.mul_re,
      Complex.mul_im] using hminus.2

theorem tendsto_scaledSingular_plus_bounded
    {δ : ℕ → ℝ} (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδne : ∀ n, δ n ≠ 0) (b v : ℝ) :
    Filter.Tendsto (fun n => δ n * (b / δ n + v))
      Filter.atTop (nhds b) := by
  have hform :
      (fun n => δ n * (b / δ n + v)) =
        (fun n => b + δ n * v) := by
    funext n
    field_simp [hδne n]
  rw [hform]
  simpa only [zero_mul, add_zero] using
    tendsto_const_nhds.add (hδ.mul_const v)

/-- Mesh-normalized exact weights converge to the two common reflected rays. -/
theorem tendsto_signedThreeAtomNormalizedWeights
    {δ : ℕ → ℝ} (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδne : ∀ n, δ n ≠ 0)
    (T r c cm : ℝ) :
    Filter.Tendsto
        (fun n => δ n * signedThreeAtomPlusWeightOne T r (δ n) c)
        Filter.atTop
        (nhds (signedThreeAtomReflectionRayOne r /
          signedThreeAtomReflectionRayCharge T r)) ∧
      Filter.Tendsto
        (fun n => δ n * signedThreeAtomPlusWeightTwo T r (δ n) c)
        Filter.atTop
        (nhds (signedThreeAtomReflectionRayTwo r /
          signedThreeAtomReflectionRayCharge T r)) ∧
      Filter.Tendsto
        (fun n => δ n * signedThreeAtomPlusWeightThree T r (δ n))
        Filter.atTop
        (nhds (signedThreeAtomReflectionRayThree r /
          signedThreeAtomReflectionRayCharge T r)) ∧
      Filter.Tendsto
        (fun n => δ n * signedThreeAtomMinusWeightOne T r (δ n) cm)
        Filter.atTop
        (nhds (r ^ (3 : ℕ) * signedThreeAtomReflectionRayOne r /
          signedThreeAtomReflectionRayCharge T r)) ∧
      Filter.Tendsto
        (fun n => δ n * signedThreeAtomMinusWeightTwo T r (δ n) cm)
        Filter.atTop
        (nhds (r ^ (3 : ℕ) * signedThreeAtomReflectionRayTwo r /
          signedThreeAtomReflectionRayCharge T r)) ∧
      Filter.Tendsto
        (fun n => δ n * signedThreeAtomMinusWeightThree T r (δ n))
        Filter.atTop
        (nhds (r ^ (3 : ℕ) * signedThreeAtomReflectionRayThree r /
          signedThreeAtomReflectionRayCharge T r)) := by
  constructor
  · simpa only [signedThreeAtomPlusWeightOne] using
      tendsto_scaledSingular_plus_bounded hδ hδne
        (signedThreeAtomReflectionRayOne r /
          signedThreeAtomReflectionRayCharge T r)
        (signedThreeAtomCorrectionOne T r c)
  constructor
  · simpa only [signedThreeAtomPlusWeightTwo] using
      tendsto_scaledSingular_plus_bounded hδ hδne
        (signedThreeAtomReflectionRayTwo r /
          signedThreeAtomReflectionRayCharge T r)
        (signedThreeAtomCorrectionTwo T r c)
  constructor
  · have h := tendsto_scaledSingular_plus_bounded hδ hδne
        (signedThreeAtomReflectionRayThree r /
          signedThreeAtomReflectionRayCharge T r) 0
    simpa only [signedThreeAtomPlusWeightThree, add_zero] using h
  constructor
  · simpa only [signedThreeAtomMinusWeightOne] using
      tendsto_scaledSingular_plus_bounded hδ hδne
        (r ^ (3 : ℕ) * signedThreeAtomReflectionRayOne r /
          signedThreeAtomReflectionRayCharge T r)
        (signedThreeAtomCorrectionOne T (1 / r) cm)
  constructor
  · simpa only [signedThreeAtomMinusWeightTwo] using
      tendsto_scaledSingular_plus_bounded hδ hδne
        (r ^ (3 : ℕ) * signedThreeAtomReflectionRayTwo r /
          signedThreeAtomReflectionRayCharge T r)
        (signedThreeAtomCorrectionTwo T (1 / r) cm)
  · have h := tendsto_scaledSingular_plus_bounded hδ hδne
        (r ^ (3 : ℕ) * signedThreeAtomReflectionRayThree r /
          signedThreeAtomReflectionRayCharge T r) 0
    simpa only [signedThreeAtomMinusWeightThree, add_zero] using h

/-- All three projective minors vanish: reflected limiting weights are the same ray. -/
theorem signedThreeAtomLimitDirections_projective
    {T r : ℝ} (hT : T ≠ 0) (hrpos : 0 < r) (hr1 : r ≠ 1) :
    let b₁ := signedThreeAtomReflectionRayOne r /
      signedThreeAtomReflectionRayCharge T r
    let b₂ := signedThreeAtomReflectionRayTwo r /
      signedThreeAtomReflectionRayCharge T r
    let b₃ := signedThreeAtomReflectionRayThree r /
      signedThreeAtomReflectionRayCharge T r
    let c₁ := r ^ (3 : ℕ) * signedThreeAtomReflectionRayOne r /
      signedThreeAtomReflectionRayCharge T r
    let c₂ := r ^ (3 : ℕ) * signedThreeAtomReflectionRayTwo r /
      signedThreeAtomReflectionRayCharge T r
    let c₃ := r ^ (3 : ℕ) * signedThreeAtomReflectionRayThree r /
      signedThreeAtomReflectionRayCharge T r
    b₁ * c₂ = c₁ * b₂ ∧
      b₁ * c₃ = c₁ * b₃ ∧
      b₂ * c₃ = c₂ * b₃ := by
  dsimp only
  have hm :=
    signedThreeAtomReflectionRayCharge_ne_zero hT hrpos hr1
  field_simp [hm]
  simp

end

end RHTower
