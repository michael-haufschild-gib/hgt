import GaloisForLFunctions.RHTower.SelbergGeometricBlend

/-!
# Recovering four boundary channels from moments and two heights

The logarithms of quarter half-densities based at infinity, zero, one, and minus
one have four distinct gradient directions at the imaginary unit. Their first
moment nevertheless misses a nonconstant, mean-zero coefficient vector.

The trace-free directional second moment supplies exactly the missing channel.
Together with the first moment, it gives the complete squared norm after
centering coefficients. The same extra channel is recovered from the vertical
first derivatives at heights one and two. These are exact identities for the
actual Frechet derivatives of the explicit fields, not assumed derivative data.

The result concerns this finite boundary configuration. It does not assert an
automorphic descent or a uniform estimate over congruence levels.
-/

open UpperHalfPlane

namespace GaloisForLFunctions.RHTower.SelbergBoundaryMomentChannels
open SelbergGeometricBlend
noncomputable section

/-- The four boundary points used for the local recovery identity. -/
inductive Boundary
  | infinity | zero | one | negOne

/-- The interpolation endpoint selecting the infinity or a finite boundary kernel. -/
def boundaryWeight : Boundary → ℝ
  | .infinity => 0
  | _ => 1

/-- Real translation placing a finite boundary kernel at its labeled point. -/
def boundaryAnchor : Boundary → ℝ
  | .one => 1
  | .negOne => -1
  | _ => 0

/-- The logarithm of the corresponding translated quarter half-density. -/
def logChannel (j : Boundary) (w : ℂ) : ℝ :=
  Real.log (realField (boundaryWeight j) (w - (boundaryAnchor j : ℂ)))

/-- The four logarithmic differentials at the imaginary unit. -/
def channelGradient : Boundary → ℂ →L[ℝ] ℝ
  | .infinity => (1 / 2 : ℝ) • Complex.imCLM
  | .zero => (-1 / 2 : ℝ) • Complex.imCLM
  | .one => (1 / 2 : ℝ) • Complex.reCLM
  | .negOne => (-1 / 2 : ℝ) • Complex.reCLM

private theorem shiftedLog_hasFDerivAt (a t : ℝ) (z : ℍ) :
    HasFDerivAt (fun w : ℂ => Real.log (realField a (w - (t : ℂ))))
      (gradient a ((z : ℂ) - (t : ℂ))) (z : ℂ) := by
  let u : ℍ := ⟨(z : ℂ) - (t : ℂ), by simpa using z.im_pos⟩
  have hg := log_realField_hasFDerivAt a u
  have hs : HasFDerivAt (fun w : ℂ => w - (t : ℂ))
      (ContinuousLinearMap.id ℝ ℂ) (z : ℂ) := (hasFDerivAt_id _).sub_const _
  have h := hg.comp (z : ℂ) hs
  simpa only [u, ContinuousLinearMap.comp_id, Function.comp_def] using h

/-- The four displayed directions are actual Frechet derivatives. -/
theorem logChannel_hasFDerivAt (j : Boundary) :
    HasFDerivAt (logChannel j) (channelGradient j) Complex.I := by
  have h := shiftedLog_hasFDerivAt (boundaryWeight j) (boundaryAnchor j) basePoint
  convert h using 1 <;> try rfl
  cases j <;> ext w <;>
    simp [channelGradient, gradient, logX, logY, radiusSq, boundaryWeight, boundaryAnchor,
      basePoint] <;> try simp
  all_goals ring_nf <;> simp

/-- The upper-half-plane point at height two above zero. -/
def doublePoint : ℍ := ⟨(2 : ℂ) * Complex.I, by simp⟩

/-- Logarithmic differentials of the four channels at height two. -/
def doubleChannelGradient : Boundary → ℂ →L[ℝ] ℝ
  | .infinity => (1 / 4 : ℝ) • Complex.imCLM
  | .zero => (-1 / 4 : ℝ) • Complex.imCLM
  | .one => (1 / 5 : ℝ) • Complex.reCLM + (-3 / 20 : ℝ) • Complex.imCLM
  | .negOne => (-1 / 5 : ℝ) • Complex.reCLM + (-3 / 20 : ℝ) • Complex.imCLM

/-- The height-two directions are actual Frechet derivatives. -/
theorem logChannel_hasFDerivAt_double (j : Boundary) :
    HasFDerivAt (logChannel j) (doubleChannelGradient j) (doublePoint : ℂ) := by
  have h := shiftedLog_hasFDerivAt (boundaryWeight j) (boundaryAnchor j) doublePoint
  convert h using 1 <;> try rfl
  cases j <;> ext w <;>
    simp [doubleChannelGradient, gradient, logX, logY, radiusSq, boundaryWeight,
      boundaryAnchor, doublePoint] <;> try simp
  all_goals ring_nf <;> simp

/-- Arbitrary real coefficients on the four labeled boundary points. -/
structure Coefficients where
  atInfinity : ℝ
  atZero : ℝ
  atOne : ℝ
  atNegOne : ℝ

/-- The signed sum of the four actual logarithmic fields. -/
def combinedLog (c : Coefficients) (w : ℂ) : ℝ :=
  c.atInfinity * logChannel .infinity w + c.atZero * logChannel .zero w +
    c.atOne * logChannel .one w + c.atNegOne * logChannel .negOne w

/-- First gradient moment at the imaginary unit. -/
def combinedGradient (c : Coefficients) : ℂ →L[ℝ] ℝ :=
  ((c.atOne - c.atNegOne) / 2) • Complex.reCLM +
    ((c.atInfinity - c.atZero) / 2) • Complex.imCLM

/-- The first moment is the differential of the combined logarithmic field. -/
theorem combinedLog_hasFDerivAt (c : Coefficients) :
    HasFDerivAt (combinedLog c) (combinedGradient c) Complex.I := by
  have h := ((((logChannel_hasFDerivAt .infinity).const_mul c.atInfinity).add
    ((logChannel_hasFDerivAt .zero).const_mul c.atZero)).add
    ((logChannel_hasFDerivAt .one).const_mul c.atOne)).add
    ((logChannel_hasFDerivAt .negOne).const_mul c.atNegOne)
  convert h using 1 <;> try rfl
  ext w
  simp [combinedGradient, channelGradient]
  ring

/-- First gradient moment at height two. -/
def combinedDoubleGradient (c : Coefficients) : ℂ →L[ℝ] ℝ :=
  ((c.atOne - c.atNegOne) / 5) • Complex.reCLM +
    ((c.atInfinity - c.atZero) / 4 - 3 * (c.atOne + c.atNegOne) / 20) • Complex.imCLM

/-- The height-two first moment is the actual differential. -/
theorem combinedLog_hasFDerivAt_double (c : Coefficients) :
    HasFDerivAt (combinedLog c) (combinedDoubleGradient c) (doublePoint : ℂ) := by
  have h := ((((logChannel_hasFDerivAt_double .infinity).const_mul c.atInfinity).add
    ((logChannel_hasFDerivAt_double .zero).const_mul c.atZero)).add
    ((logChannel_hasFDerivAt_double .one).const_mul c.atOne)).add
    ((logChannel_hasFDerivAt_double .negOne).const_mul c.atNegOne)
  convert h using 1 <;> try rfl
  ext w
  simp [combinedDoubleGradient, doubleChannelGradient]
  ring

/-- Squared Euclidean norm of the actual first derivative at the imaginary unit. -/
def firstEnergy (c : Coefficients) : ℝ :=
  (fderiv ℝ (combinedLog c) Complex.I 1) ^ (2 : ℕ) +
    (fderiv ℝ (combinedLog c) Complex.I Complex.I) ^ (2 : ℕ)

/-- Trace-free second moment of the individual logarithmic gradients. -/
def directionalSecondMoment (c : Coefficients) : ℝ :=
  let t := fun j => (fderiv ℝ (logChannel j) Complex.I Complex.I) ^ (2 : ℕ) -
    (fderiv ℝ (logChannel j) Complex.I 1) ^ (2 : ℕ)
  c.atInfinity * t .infinity + c.atZero * t .zero +
    c.atOne * t .one + c.atNegOne * t .negOne

/-- Sum of the four coefficients. -/
def totalMass (c : Coefficients) : ℝ := c.atInfinity + c.atZero + c.atOne + c.atNegOne

/-- Sum of the four squared coefficients. -/
def squaredNorm (c : Coefficients) : ℝ :=
  c.atInfinity ^ (2 : ℕ) + c.atZero ^ (2 : ℕ) + c.atOne ^ (2 : ℕ) + c.atNegOne ^ (2 : ℕ)

/-- Squared coefficient norm after removing the common coefficient channel. -/
def centeredNorm (c : Coefficients) : ℝ := squaredNorm c - totalMass c ^ (2 : ℕ) / 4

/-- The first-gradient energy sees only the two opposite-point differences. -/
theorem firstEnergy_eq (c : Coefficients) :
    firstEnergy c = ((c.atInfinity - c.atZero) ^ (2 : ℕ) + (c.atOne - c.atNegOne) ^ (2 : ℕ)) / 4 := by
  simp [firstEnergy, (combinedLog_hasFDerivAt c).fderiv, combinedGradient]
  ring

/-- The trace-free second moment sees the missing alternating channel. -/
theorem directionalSecondMoment_eq (c : Coefficients) :
    directionalSecondMoment c = (c.atInfinity + c.atZero - c.atOne - c.atNegOne) / 4 := by
  simp [directionalSecondMoment, (logChannel_hasFDerivAt _).fderiv, channelGradient]
  ring

/-- Exact recovery of the centered coefficient norm from the first two moments. -/
theorem centeredNorm_eq_moments (c : Coefficients) :
    centeredNorm c = 2 * firstEnergy c + 4 * directionalSecondMoment c ^ (2 : ℕ) := by
  rw [firstEnergy_eq, directionalSecondMoment_eq]
  unfold centeredNorm squaredNorm totalMass
  ring

/-- The first moment loses exactly coefficients equal within each opposite pair. -/
theorem firstEnergy_eq_zero_iff (c : Coefficients) :
    firstEnergy c = 0 ↔ c.atInfinity = c.atZero ∧ c.atOne = c.atNegOne := by
  rw [firstEnergy_eq]
  constructor
  · intro h
    have ha := sq_nonneg (c.atInfinity - c.atZero)
    have hb := sq_nonneg (c.atOne - c.atNegOne)
    constructor <;> nlinarith
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]
    ring

/-- The centered coefficient norm is nonnegative. -/
theorem centeredNorm_nonneg (c : Coefficients) : 0 ≤ centeredNorm c := by
  rw [centeredNorm_eq_moments, firstEnergy_eq]
  positivity

/-- Together the two moments lose exactly the common coefficient channel. -/
theorem centeredNorm_eq_zero_iff (c : Coefficients) :
    centeredNorm c = 0 ↔
      c.atInfinity = c.atZero ∧ c.atZero = c.atOne ∧ c.atOne = c.atNegOne := by
  rw [centeredNorm_eq_moments, firstEnergy_eq, directionalSecondMoment_eq]
  constructor
  · intro h
    have ha := sq_nonneg (c.atInfinity - c.atZero)
    have hb := sq_nonneg (c.atOne - c.atNegOne)
    have hc := sq_nonneg (c.atInfinity + c.atZero - c.atOne - c.atNegOne)
    have h₁ : c.atInfinity = c.atZero := by nlinarith
    have h₂ : c.atOne = c.atNegOne := by nlinarith
    refine ⟨h₁, ?_, h₂⟩
    rw [h₁, h₂] at h
    nlinarith
  · rintro ⟨h₁, h₂, h₃⟩
    rw [h₁, h₂, h₃]
    ring

/-- A nonconstant coefficient vector invisible to the first moment. -/
def alternating : Coefficients := ⟨1, 1, -1, -1⟩

/-- Explicit mean-zero cancellation, with its nonzero second moment retained. -/
theorem alternating_blind_first_moment :
    totalMass alternating = 0 ∧ firstEnergy alternating = 0 ∧
      directionalSecondMoment alternating = 1 ∧ centeredNorm alternating = 4 := by
  rw [firstEnergy_eq, directionalSecondMoment_eq]
  dsimp [alternating, totalMass, centeredNorm, squaredNorm]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Remove the arithmetic mean from every coefficient. -/
def center (c : Coefficients) : Coefficients :=
  ⟨c.atInfinity - totalMass c / 4, c.atZero - totalMass c / 4,
    c.atOne - totalMass c / 4, c.atNegOne - totalMass c / 4⟩

/-- Centering gives zero total coefficient mass. -/
theorem totalMass_center (c : Coefficients) : totalMass (center c) = 0 := by
  simp only [totalMass, center]
  ring

/-- The centered norm is literally the squared norm of centered coefficients. -/
theorem squaredNorm_center (c : Coefficients) : squaredNorm (center c) = centeredNorm c := by
  simp only [squaredNorm, center, centeredNorm, totalMass]
  ring

/-- Vertical first-derivative difference at heights two and one for centered data. -/
def heightDifference (c : Coefficients) : ℝ :=
  fderiv ℝ (combinedLog (center c)) (doublePoint : ℂ) Complex.I -
    fderiv ℝ (combinedLog (center c)) Complex.I Complex.I / 2

/-- Two spatial observations detect the alternating channel exactly. -/
theorem heightDifference_eq (c : Coefficients) :
    heightDifference c = 3 * (c.atInfinity + c.atZero - c.atOne - c.atNegOne) / 40 := by
  unfold heightDifference
  rw [(combinedLog_hasFDerivAt_double _).fderiv, (combinedLog_hasFDerivAt _).fderiv]
  simp [combinedDoubleGradient, combinedGradient, center, totalMass]
  ring

/-- The second directional moment is recovered from two spatial first derivatives. -/
theorem directionalSecondMoment_eq_heightDifference (c : Coefficients) :
    directionalSecondMoment c = (10 / 3 : ℝ) * heightDifference c := by
  rw [directionalSecondMoment_eq, heightDifference_eq]
  ring

/-- Exact recovery of every centered coefficient from two heights of first derivatives. -/
theorem centeredNorm_eq_twoHeight (c : Coefficients) :
    centeredNorm c = 2 * firstEnergy c + (400 / 9 : ℝ) * heightDifference c ^ (2 : ℕ) := by
  rw [centeredNorm_eq_moments, directionalSecondMoment_eq_heightDifference]
  ring

/-- No positive constant makes the first moment control the centered coefficient norm. -/
theorem no_positive_firstEnergy_bound :
    ¬ ∃ k : ℝ, 0 < k ∧ ∀ c : Coefficients, k * centeredNorm c ≤ firstEnergy c := by
  rintro ⟨k, hk, hbound⟩
  have h := hbound alternating
  rw [alternating_blind_first_moment.2.1, alternating_blind_first_moment.2.2.2] at h
  nlinarith

end
end GaloisForLFunctions.RHTower.SelbergBoundaryMomentChannels
