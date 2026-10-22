import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureHolomorphicSectorCoercivity

/-!
# Holomorphic affine-companion determinant on one Xi height fibre

For a reflection-complete packet with common centered ordinate `x`, write its strict-right
representatives as `x + i y_j` and let `P_j` be the holomorphic envelope square.  The first three
reflection-paired affine moments are

`2 A`, `2 (x A - S)`, and `2 (x^(2 : ℕ) A - U - 2 x S)`,

where `A = sum m_j Re P_j`, `S = sum m_j Im P_j y_j`, and
`U = sum m_j Re P_j y_j^(2 : ℕ)`.  Their central two-by-two determinant is exactly

`-4 (A U + S^(2 : ℕ))`.

Thus envelope phase cannot cancel transverse charge inside one height fibre: it contributes the
additional nonpositive square `-4 S^(2 : ℕ)`.  No RH or zero-separation hypothesis is used.
-/

open scoped BigOperators
open Complex

namespace RHTower

noncomputable section

/-- Real part of the reflection-paired zeroth affine moment, divided by two. -/
def holomorphicAffineFibreMass {ι : Type*}
    (s : Finset ι) (m : ι → ℝ) (P : ι → ℂ) : ℝ :=
  ∑ i ∈ s, m i * (P i).re

/-- Phase--transverse mixed term in the reflection-paired first affine moment. -/
def holomorphicAffineFibrePhaseSkew {ι : Type*}
    (s : Finset ι) (y m : ι → ℝ) (P : ι → ℂ) : ℝ :=
  ∑ i ∈ s, m i * (P i).im * y i

/-- Positive transverse second moment when all weights and envelope real parts are nonnegative. -/
def holomorphicAffineFibreTransverseMoment {ι : Type*}
    (s : Finset ι) (y m : ι → ℝ) (P : ι → ℂ) : ℝ :=
  ∑ i ∈ s, m i * (P i).re * y i ^ (2 : ℕ)

/-- Reflection-paired zeroth affine moment. -/
def holomorphicAffineFibreMomentZero {ι : Type*}
    (s : Finset ι) (m : ι → ℝ) (P : ι → ℂ) : ℝ :=
  2 * holomorphicAffineFibreMass s m P

/-- Reflection-paired first affine moment on a common ordinate `x`. -/
def holomorphicAffineFibreMomentOne {ι : Type*}
    (s : Finset ι) (x : ℝ) (y m : ι → ℝ) (P : ι → ℂ) : ℝ :=
  2 * (x * holomorphicAffineFibreMass s m P -
    holomorphicAffineFibrePhaseSkew s y m P)

/-- Reflection-paired second affine moment on a common ordinate `x`. -/
def holomorphicAffineFibreMomentTwo {ι : Type*}
    (s : Finset ι) (x : ℝ) (y m : ι → ℝ) (P : ι → ℂ) : ℝ :=
  2 * (x ^ (2 : ℕ) * holomorphicAffineFibreMass s m P -
    holomorphicAffineFibreTransverseMoment s y m P -
    2 * x * holomorphicAffineFibrePhaseSkew s y m P)

/-- Central two-by-two determinant of the first three reflection-paired affine moments. -/
def holomorphicAffineFibreCentralDet {ι : Type*}
    (s : Finset ι) (x : ℝ) (y m : ι → ℝ) (P : ι → ℂ) : ℝ :=
  holomorphicAffineFibreMomentZero s m P *
      holomorphicAffineFibreMomentTwo s x y m P -
    holomorphicAffineFibreMomentOne s x y m P ^ (2 : ℕ)

/-- Atomic real-part identity behind the first reflection-paired affine moment. -/
theorem re_envelope_mul_verticalPoint (P : ℂ) (x y : ℝ) :
    (P * ((x : ℂ) + (y : ℂ) * I)).re = P.re * x - P.im * y := by
  simp [Complex.mul_re, Complex.mul_im]

/-- Atomic real-part identity behind the second reflection-paired affine moment. -/
theorem re_envelope_mul_verticalPoint_sq (P : ℂ) (x y : ℝ) :
    (P * ((x : ℂ) + (y : ℂ) * I) ^ (2 : ℕ)).re =
      P.re * (x ^ (2 : ℕ) - y ^ (2 : ℕ)) - 2 * P.im * x * y := by
  simp [Complex.mul_re, Complex.mul_im, pow_two]
  ring

/-- Exact phase-safe fibre law: phase contributes a square with the same negative sign as the
transverse moment. -/
theorem holomorphicAffineFibreCentralDet_eq
    {ι : Type*} (s : Finset ι) (x : ℝ) (y m : ι → ℝ) (P : ι → ℂ) :
    holomorphicAffineFibreCentralDet s x y m P =
      -4 * (holomorphicAffineFibreMass s m P *
          holomorphicAffineFibreTransverseMoment s y m P +
        holomorphicAffineFibrePhaseSkew s y m P ^ (2 : ℕ)) := by
  rw [holomorphicAffineFibreCentralDet, holomorphicAffineFibreMomentZero,
    holomorphicAffineFibreMomentOne, holomorphicAffineFibreMomentTwo]
  ring

/-- Nonnegative envelope mass and transverse moment force a nonpositive fibre determinant. -/
theorem holomorphicAffineFibreCentralDet_nonpos
    {ι : Type*} (s : Finset ι) (x : ℝ) (y m : ι → ℝ) (P : ι → ℂ)
    (hA : 0 ≤ holomorphicAffineFibreMass s m P)
    (hU : 0 ≤ holomorphicAffineFibreTransverseMoment s y m P) :
    holomorphicAffineFibreCentralDet s x y m P ≤ 0 := by
  rw [holomorphicAffineFibreCentralDet_eq]
  nlinarith [sq_nonneg (holomorphicAffineFibrePhaseSkew s y m P)]

/-- A positive envelope mass and one positive transverse moment make the determinant strictly
negative, however small the transverse displacement is. -/
theorem holomorphicAffineFibreCentralDet_neg
    {ι : Type*} (s : Finset ι) (x : ℝ) (y m : ι → ℝ) (P : ι → ℂ)
    (hA : 0 < holomorphicAffineFibreMass s m P)
    (hU : 0 < holomorphicAffineFibreTransverseMoment s y m P) :
    holomorphicAffineFibreCentralDet s x y m P < 0 := by
  rw [holomorphicAffineFibreCentralDet_eq]
  nlinarith [sq_nonneg (holomorphicAffineFibrePhaseSkew s y m P)]

/-- Critical-line fibres lie in the exact radical of the affine-companion determinant. -/
theorem holomorphicAffineFibreCentralDet_eq_zero_of_forall_eq_zero
    {ι : Type*} (s : Finset ι) (x : ℝ) (y m : ι → ℝ) (P : ι → ℂ)
    (hy : ∀ i ∈ s, y i = 0) :
    holomorphicAffineFibreCentralDet s x y m P = 0 := by
  have hS : holomorphicAffineFibrePhaseSkew s y m P = 0 := by
    rw [holomorphicAffineFibrePhaseSkew]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hy i hi]
    ring
  have hU : holomorphicAffineFibreTransverseMoment s y m P = 0 := by
    rw [holomorphicAffineFibreTransverseMoment]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hy i hi]
    ring
  rw [holomorphicAffineFibreCentralDet_eq, hS, hU]
  ring

end

end RHTower
