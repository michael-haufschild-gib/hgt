import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Four-dimensional conformal clock diffusion identity

This file isolates the algebra behind conformal conjugation of a four-dimensional wave operator.
`SecondOrderClockCalculus` records only the second-order product rule and the two first-order
Leibniz rules for its carré du champ. No differential-geometric, analytic, or field-equation axiom
is introduced.

For an invertible conformal weight represented by `weight * weightInv = 1`, the rescaled operator

`weightInv² * (L f + 2 * weightInv * Γ weight f)`

is the algebraic form of the wave operator for `weight² g` in four dimensions. Conjugating by
`weightInv` cancels every carré-du-champ term and leaves the single scalar defect
`weightInv * L weight`.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

/-- Minimal algebraic data of a second-order scalar operator and its carré du champ. -/
structure SecondOrderClockCalculus (A : Type u) [CommRing A] where
  laplacian : A → A
  gamma : A → A → A
  laplacian_one : laplacian 1 = 0
  laplacian_mul :
    ∀ f h, laplacian (f * h) =
      f * laplacian h + h * laplacian f + 2 * gamma f h
  gamma_one_left : ∀ h, gamma 1 h = 0
  gamma_one_right : ∀ f, gamma f 1 = 0
  gamma_mul_left :
    ∀ f h k, gamma (f * h) k = f * gamma h k + h * gamma f k
  gamma_mul_right :
    ∀ f h k, gamma f (h * k) = h * gamma f k + k * gamma f h

namespace SecondOrderClockCalculus

variable {A : Type u} [CommRing A]

/-- Algebraic inverse rule for the first argument of the carré du champ. -/
theorem gamma_inverse_left
    (C : SecondOrderClockCalculus A)
    {weight weightInv : A} (hinv : weight * weightInv = 1)
    (u : A) :
    C.gamma weightInv u =
      -(weightInv ^ 2) * C.gamma weight u := by
  have hinv' : weightInv * weight = 1 := by
    simpa [mul_comm] using hinv
  have hproduct := C.gamma_mul_left weight weightInv u
  rw [hinv, C.gamma_one_left] at hproduct
  have hsolve :
      weight * C.gamma weightInv u =
        -weightInv * C.gamma weight u := by
    linear_combination -hproduct
  calc
    C.gamma weightInv u =
        (weightInv * weight) * C.gamma weightInv u := by simp [hinv']
    _ = weightInv * (weight * C.gamma weightInv u) := by ring
    _ = weightInv * (-weightInv * C.gamma weight u) := by rw [hsolve]
    _ = -(weightInv ^ 2) * C.gamma weight u := by ring

/-- Algebraic inverse rule for the second argument of the carré du champ. -/
theorem gamma_inverse_right
    (C : SecondOrderClockCalculus A)
    {weight weightInv : A} (hinv : weight * weightInv = 1)
    (u : A) :
    C.gamma u weightInv =
      -(weightInv ^ 2) * C.gamma u weight := by
  have hinv' : weightInv * weight = 1 := by
    simpa [mul_comm] using hinv
  have hproduct := C.gamma_mul_right u weight weightInv
  rw [hinv, C.gamma_one_right] at hproduct
  have hsolve :
      weight * C.gamma u weightInv =
        -weightInv * C.gamma u weight := by
    linear_combination -hproduct
  calc
    C.gamma u weightInv =
        (weightInv * weight) * C.gamma u weightInv := by simp [hinv']
    _ = weightInv * (weight * C.gamma u weightInv) := by ring
    _ = weightInv * (-weightInv * C.gamma u weight) := by rw [hsolve]
    _ = -(weightInv ^ 2) * C.gamma u weight := by ring

/-- Algebraic inverse rule for a second-order operator. -/
theorem laplacian_inverse
    (C : SecondOrderClockCalculus A)
    {weight weightInv : A} (hinv : weight * weightInv = 1) :
    C.laplacian weightInv =
      -(weightInv ^ 2) * C.laplacian weight +
        2 * weightInv ^ 3 * C.gamma weight weight := by
  have hinv' : weightInv * weight = 1 := by
    simpa [mul_comm] using hinv
  have hproduct := C.laplacian_mul weight weightInv
  rw [hinv, C.laplacian_one, C.gamma_inverse_right hinv weight] at hproduct
  have hsolve :
      weight * C.laplacian weightInv =
        -weightInv * C.laplacian weight +
          2 * weightInv ^ 2 * C.gamma weight weight := by
    linear_combination -hproduct
  calc
    C.laplacian weightInv =
        (weightInv * weight) * C.laplacian weightInv := by simp [hinv']
    _ = weightInv * (weight * C.laplacian weightInv) := by ring
    _ = weightInv *
        (-weightInv * C.laplacian weight +
          2 * weightInv ^ 2 * C.gamma weight weight) := by rw [hsolve]
    _ = -(weightInv ^ 2) * C.laplacian weight +
        2 * weightInv ^ 3 * C.gamma weight weight := by ring

/-- Four-dimensional conformal transform of the scalar second-order operator. -/
def conformalWave
    (C : SecondOrderClockCalculus A)
    (weight weightInv f : A) : A :=
  weightInv ^ 2 *
    (C.laplacian f + 2 * weightInv * C.gamma weight f)

/-- **Four-dimensional conformal clock conjugation.**

Conjugation of the conformally transformed wave operator by the inverse weight cancels all
first-order and carré-du-champ terms. The only surviving geometric coefficient is
`weightInv * C.laplacian weight`.
-/
theorem conformalWave_conjugation
    (C : SecondOrderClockCalculus A)
    {weight weightInv : A} (hinv : weight * weightInv = 1)
    (u : A) :
    weight ^ 3 * C.conformalWave weight weightInv (weightInv * u) =
      C.laplacian u -
        (weightInv * C.laplacian weight) * u := by
  have hscale : weight ^ 3 * weightInv ^ 2 = weight := by
    calc
      weight ^ 3 * weightInv ^ 2 =
          weight * (weight * weightInv) ^ 2 := by ring
      _ = weight := by rw [hinv]; ring
  rw [conformalWave, ← mul_assoc, hscale, C.laplacian_mul,
    C.gamma_mul_right, C.laplacian_inverse hinv,
    C.gamma_inverse_left hinv, C.gamma_inverse_right hinv]
  calc
    weight *
        (weightInv * C.laplacian u +
          u *
            (-(weightInv ^ 2) * C.laplacian weight +
              2 * weightInv ^ 3 * C.gamma weight weight) +
          2 * (-(weightInv ^ 2) * C.gamma weight u) +
          2 * weightInv *
            (weightInv * C.gamma weight u +
              u * (-(weightInv ^ 2) * C.gamma weight weight))) =
        weight *
          (weightInv * C.laplacian u -
            weightInv ^ 2 * C.laplacian weight * u) := by ring
    _ = C.laplacian u -
        (weightInv * C.laplacian weight) * u := by
      calc
        weight *
            (weightInv * C.laplacian u -
              weightInv ^ 2 * C.laplacian weight * u) =
            (weight * weightInv) * C.laplacian u -
              (weight * weightInv) * weightInv *
                C.laplacian weight * u := by ring
        _ = C.laplacian u -
            (weightInv * C.laplacian weight) * u := by rw [hinv]; ring

/-- **Massive four-dimensional conformal clock law.**

A calibrated squared mass multiplies the conformal scale `weight²`; the geometric defect is
species-independent.
-/
theorem conformalKleinGordon_conjugation
    (C : SecondOrderClockCalculus A)
    {weight weightInv : A} (hinv : weight * weightInv = 1)
    (massSq u : A) :
    weight ^ 3 *
        (C.conformalWave weight weightInv (weightInv * u) +
          massSq * (weightInv * u)) =
      C.laplacian u +
        (massSq * weight ^ 2 -
          weightInv * C.laplacian weight) * u := by
  rw [mul_add, C.conformalWave_conjugation hinv]
  have hmass :
      weight ^ 3 * (massSq * (weightInv * u)) =
        massSq * weight ^ 2 * u := by
    calc
      weight ^ 3 * (massSq * (weightInv * u)) =
          massSq * weight ^ 2 * (weight * weightInv) * u := by ring
      _ = massSq * weight ^ 2 * u := by rw [hinv]; ring
  rw [hmass]
  ring

end SecondOrderClockCalculus

end GaloisForLFunctions.HTGeometry
