import Mathlib

/-!
# Oriented reflection quotient and projective flow

An ordered pair of reflected analytic channels has two natural coordinates. The quotient `B/A`
is projective. The Cayley coordinate `(A+B)/(A-B)` is odd under channel exchange, and its zero is
the anti-phase collision `A+B=0`. Every even reader of this odd coordinate loses its first jet.

The quotient also has a canonical division-free flow. If

`W = B' A - B A'` and `V = A² conjugate(W)`,

then the derivative of `B/A` in direction `V` is exactly `|W|²`. Thus every regular projective
collision carries a canonical orientation before any reflection-invariant scalarization.
-/

open Complex

namespace HTGeometry

noncomputable section

/-- Projective quotient of an ordered channel pair. -/
def reflectedChannelProjectiveRatio (A B : ℂ → ℂ) (z : ℂ) : ℂ :=
  B z / A z

/-- Division-free derivative numerator of the projective quotient. -/
def reflectedChannelProjectiveWronskian
    (A B : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv B z * A z - B z * deriv A z

/-- Canonically oriented division-free projective flow. -/
def reflectedChannelProjectiveFlow
    (A B : ℂ → ℂ) (z : ℂ) : ℂ :=
  A z ^ (2 : ℕ) * starRingEnd ℂ (reflectedChannelProjectiveWronskian A B z)

/-- Odd Cayley coordinate of an ordered reflected pair. Its zero is the anti-phase collision. -/
def reflectedChannelOddCoordinate (A B : ℂ → ℂ) (z : ℂ) : ℂ :=
  (A z + B z) / (A z - B z)

/-- Exchanging the two reflected channels reverses the Cayley orientation. -/
theorem reflectedChannelOddCoordinate_swap
    (A B : ℂ → ℂ) (z : ℂ) :
    reflectedChannelOddCoordinate B A z =
      -reflectedChannelOddCoordinate A B z := by
  unfold reflectedChannelOddCoordinate
  rw [show B z - A z = -(A z - B z) by ring, div_neg]
  ring

/-- On the regular chart, the odd coordinate vanishes exactly at channel anti-phase. -/
theorem reflectedChannelOddCoordinate_eq_zero_iff
    {A B : ℂ → ℂ} {z : ℂ} (hden : A z - B z ≠ 0) :
    reflectedChannelOddCoordinate A B z = 0 ↔ A z + B z = 0 := by
  unfold reflectedChannelOddCoordinate
  constructor
  · intro h
    exact (div_eq_zero_iff.mp h).resolve_right hden
  · intro h
    rw [h]
    simp

/-- The odd coordinate is the Cayley transform of the projective quotient. -/
theorem reflectedChannelOddCoordinate_eq_cayleyRatio
    {A B : ℂ → ℂ} {z : ℂ} (hA : A z ≠ 0) :
    reflectedChannelOddCoordinate A B z =
      (1 + reflectedChannelProjectiveRatio A B z) /
        (1 - reflectedChannelProjectiveRatio A B z) := by
  unfold reflectedChannelOddCoordinate reflectedChannelProjectiveRatio
  field_simp [hA]

/-- Every differentiable even reader of an oriented coordinate loses its first jet at the
reflection-fixed value. -/
theorem evenReader_firstJet_zero
    {phi : ℂ → ℂ} {d : ℂ} (heven : Function.Even phi)
    (hphi : HasDerivAt phi d 0) :
    d = 0 := by
  have hneg : HasDerivAt (phi ∘ fun z : ℂ => -z) (-d) 0 := by
    have hinner : HasDerivAt (fun z : ℂ => -z) (-1) 0 :=
      (hasDerivAt_id (0 : ℂ)).neg
    have hcomp := hphi.comp_of_eq (0 : ℂ) hinner (by simp)
    simpa only [mul_neg, mul_one] using hcomp
  have hsame : (phi ∘ fun z : ℂ => -z) = phi := by
    funext z
    exact heven z
  rw [hsame] at hneg
  have hd : d = -d := hphi.unique hneg
  have htwo : (2 : ℂ) * d = 0 := by
    linear_combination hd
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Quotient rule for the projective channel coordinate. -/
theorem hasDerivAt_reflectedChannelProjectiveRatio
    {A B : ℂ → ℂ} {z a' b' : ℂ}
    (hA : HasDerivAt A a' z) (hB : HasDerivAt B b' z)
    (hA0 : A z ≠ 0) :
    HasDerivAt (reflectedChannelProjectiveRatio A B)
      ((b' * A z - B z * a') / A z ^ (2 : ℕ)) z := by
  change HasDerivAt (fun w => B w / A w)
    ((b' * A z - B z * a') / A z ^ (2 : ℕ)) z
  exact hB.div hA hA0

/-- Universal projective flow law: the quotient derivative along its canonical flow is the
nonnegative Wronskian norm-square. -/
theorem reflectedChannelProjectiveDerivative_mul_flow
    {A B : ℂ → ℂ} {z : ℂ} (hA0 : A z ≠ 0) :
    (reflectedChannelProjectiveWronskian A B z / A z ^ (2 : ℕ)) *
        reflectedChannelProjectiveFlow A B z =
      (Complex.normSq
        (reflectedChannelProjectiveWronskian A B z) : ℂ) := by
  unfold reflectedChannelProjectiveFlow
  field_simp [hA0]
  simp only [Complex.normSq_apply, Complex.ofReal_add, Complex.ofReal_mul]
  apply Complex.ext <;> simp
  ring

/-- Along any integral curve of the canonical flow, the projective ratio has real nonnegative
derivative equal to the Wronskian norm-square. -/
theorem hasDerivAt_reflectedChannelProjectiveRatio_comp_flow
    {A B : ℂ → ℂ} {gamma : ℝ → ℂ} {t : ℝ}
    (hA : HasDerivAt A (deriv A (gamma t)) (gamma t))
    (hB : HasDerivAt B (deriv B (gamma t)) (gamma t))
    (hA0 : A (gamma t) ≠ 0)
    (hgamma : HasDerivAt gamma
      (reflectedChannelProjectiveFlow A B (gamma t)) t) :
    HasDerivAt
      (fun u : ℝ => reflectedChannelProjectiveRatio A B (gamma u))
      (Complex.normSq
        (reflectedChannelProjectiveWronskian A B (gamma t)) : ℂ) t := by
  have hratio :=
    hasDerivAt_reflectedChannelProjectiveRatio hA hB hA0
  have hcomp := hratio.comp t hgamma
  have heq := reflectedChannelProjectiveDerivative_mul_flow
    (A := A) (B := B) hA0
  apply hcomp.congr_deriv
  simpa only [reflectedChannelProjectiveWronskian, Function.comp_apply] using heq

/-- Every affine channel collision is one projective level set. -/
theorem reflectedAffineCollision_iff_projectiveLevel
    {a b alpha beta : ℂ} (ha : a ≠ 0) (hbeta : beta ≠ 0) :
    alpha * a + beta * b = 0 ↔ b / a = -alpha / beta := by
  constructor
  · intro h
    rw [div_eq_iff ha]
    field_simp [hbeta]
    linear_combination h
  · intro h
    rw [div_eq_iff ha] at h
    field_simp [hbeta] at h
    linear_combination h

/-- The symmetric midpoint collision is the projective anti-phase value `-1`. -/
theorem reflectedMidpointCollision_iff_antiphase
    {a b : ℂ} (ha : a ≠ 0) :
    a + b = 0 ↔ b / a = -1 := by
  constructor
  · intro h
    rw [div_eq_iff ha]
    linear_combination h
  · intro h
    rw [div_eq_iff ha] at h
    linear_combination h

end

end HTGeometry
