import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
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

/-- Second-order clock calculus equipped with the exact exponential chain rules. -/
structure ExponentialSecondOrderClockCalculus
    (A : Type u) [CommRing A] [Algebra ℝ A] where
  toSecondOrder : SecondOrderClockCalculus A
  expSmul : ℝ → A → A
  expSmul_zero : ∀ sigma, expSmul 0 sigma = 1
  expSmul_add : ∀ c d sigma,
    expSmul (c + d) sigma = expSmul c sigma * expSmul d sigma
  laplacian_expSmul : ∀ c sigma,
    toSecondOrder.laplacian (expSmul c sigma) =
      expSmul c sigma *
        (c • toSecondOrder.laplacian sigma +
          c ^ 2 • toSecondOrder.gamma sigma sigma)
  gamma_expSmul_left : ∀ c sigma u,
    toSecondOrder.gamma (expSmul c sigma) u =
      expSmul c sigma * (c • toSecondOrder.gamma sigma u)
  gamma_expSmul_right : ∀ c sigma u,
    toSecondOrder.gamma u (expSmul c sigma) =
      expSmul c sigma * (c • toSecondOrder.gamma u sigma)

namespace ExponentialSecondOrderClockCalculus

variable {A : Type u} [CommRing A] [Algebra ℝ A]

/-- Conformal wave operator in dimension parameter `a = (d - 2) / 2`. -/
def conformalWaveSigma
    (C : ExponentialSecondOrderClockCalculus A)
    (a : ℝ) (sigma f : A) : A :=
  C.expSmul (-2) sigma *
    (C.toSecondOrder.laplacian f +
      2 * (a • C.toSecondOrder.gamma sigma f))

theorem expSmul_weight_cancellation
    (C : ExponentialSecondOrderClockCalculus A)
    (a : ℝ) (sigma : A) :
    C.expSmul (a + 2) sigma * C.expSmul (-2) sigma *
        C.expSmul (-a) sigma = 1 := by
  rw [← C.expSmul_add, ← C.expSmul_add]
  convert C.expSmul_zero sigma using 2
  ring

/-- Exact general-dimensional conformal conjugation. -/
theorem conformalWaveSigma_conjugation
    (C : ExponentialSecondOrderClockCalculus A)
    (a : ℝ) (sigma u : A) :
    C.expSmul (a + 2) sigma *
        C.conformalWaveSigma a sigma (C.expSmul (-a) sigma * u) =
      C.toSecondOrder.laplacian u +
        ((-a) • C.toSecondOrder.laplacian sigma -
          a ^ 2 • C.toSecondOrder.gamma sigma sigma) * u := by
  rw [conformalWaveSigma, C.toSecondOrder.laplacian_mul,
    C.toSecondOrder.gamma_mul_right, C.laplacian_expSmul,
    C.gamma_expSmul_left, C.gamma_expSmul_right]
  simp only [Algebra.smul_def]
  have hweight := C.expSmul_weight_cancellation a sigma
  calc
    C.expSmul (a + 2) sigma *
        (C.expSmul (-2) sigma *
          (C.expSmul (-a) sigma * C.toSecondOrder.laplacian u +
            u *
              (C.expSmul (-a) sigma *
                ((algebraMap ℝ A (-a)) * C.toSecondOrder.laplacian sigma +
                  algebraMap ℝ A ((-a) ^ 2) *
                    C.toSecondOrder.gamma sigma sigma)) +
            2 *
              (C.expSmul (-a) sigma *
                ((algebraMap ℝ A (-a)) * C.toSecondOrder.gamma sigma u)) +
            2 * (algebraMap ℝ A a *
              (C.expSmul (-a) sigma * C.toSecondOrder.gamma sigma u +
                u *
                  (C.expSmul (-a) sigma *
                    (algebraMap ℝ A (-a) *
                      C.toSecondOrder.gamma sigma sigma)))))) =
      (C.expSmul (a + 2) sigma * C.expSmul (-2) sigma *
          C.expSmul (-a) sigma) *
        (C.toSecondOrder.laplacian u +
          (algebraMap ℝ A (-a) * C.toSecondOrder.laplacian sigma -
            algebraMap ℝ A (a ^ 2) * C.toSecondOrder.gamma sigma sigma) * u) := by
      push_cast
      ring
    _ = _ := by rw [hweight, one_mul]

/-- Massive general-dimensional conformal clock law. -/
theorem conformalKleinGordonSigma_conjugation
    (C : ExponentialSecondOrderClockCalculus A)
    (a massSq : ℝ) (sigma u : A) :
    C.expSmul (a + 2) sigma *
        (C.conformalWaveSigma a sigma (C.expSmul (-a) sigma * u) +
          massSq • (C.expSmul (-a) sigma * u)) =
      C.toSecondOrder.laplacian u +
        (massSq • C.expSmul 2 sigma +
          (-a) • C.toSecondOrder.laplacian sigma -
          a ^ 2 • C.toSecondOrder.gamma sigma sigma) * u := by
  rw [mul_add, C.conformalWaveSigma_conjugation]
  have hmassWeight :
      C.expSmul (a + 2) sigma * C.expSmul (-a) sigma =
        C.expSmul 2 sigma := by
    rw [← C.expSmul_add]
    congr 2
    ring
  simp only [Algebra.smul_def]
  calc
    C.toSecondOrder.laplacian u +
          ((algebraMap ℝ A) (-a) * C.toSecondOrder.laplacian sigma -
            (algebraMap ℝ A) (a ^ 2) * C.toSecondOrder.gamma sigma sigma) * u +
        C.expSmul (a + 2) sigma *
          ((algebraMap ℝ A) massSq * (C.expSmul (-a) sigma * u)) =
      C.toSecondOrder.laplacian u +
          ((algebraMap ℝ A) (-a) * C.toSecondOrder.laplacian sigma -
            (algebraMap ℝ A) (a ^ 2) * C.toSecondOrder.gamma sigma sigma) * u +
        (algebraMap ℝ A) massSq *
          (C.expSmul (a + 2) sigma * C.expSmul (-a) sigma) * u := by ring
    _ = _ := by rw [hmassWeight]; ring

/-- Conformal conjugation weight `a = (d - 2) / 2` in dimension `d`. -/
noncomputable def conformalDimensionWeight (d : ℕ) : ℝ :=
  ((d : ℝ) - 2) / 2

/-- Literal `d ≥ 3` specialization of the general conformal conjugation law. -/
theorem conformalWaveSigma_dimension_conjugation
    (C : ExponentialSecondOrderClockCalculus A)
    (d : ℕ) (_hd : 3 ≤ d) (sigma u : A) :
    C.expSmul (conformalDimensionWeight d + 2) sigma *
        C.conformalWaveSigma (conformalDimensionWeight d) sigma
          (C.expSmul (-conformalDimensionWeight d) sigma * u) =
      C.toSecondOrder.laplacian u +
        ((-conformalDimensionWeight d) • C.toSecondOrder.laplacian sigma -
          conformalDimensionWeight d ^ 2 •
            C.toSecondOrder.gamma sigma sigma) * u :=
  C.conformalWaveSigma_conjugation (conformalDimensionWeight d) sigma u

/-- Literal massive `d ≥ 3` conformal clock law. -/
theorem conformalKleinGordonSigma_dimension_conjugation
    (C : ExponentialSecondOrderClockCalculus A)
    (d : ℕ) (_hd : 3 ≤ d) (massSq : ℝ) (sigma u : A) :
    C.expSmul (conformalDimensionWeight d + 2) sigma *
        (C.conformalWaveSigma (conformalDimensionWeight d) sigma
            (C.expSmul (-conformalDimensionWeight d) sigma * u) +
          massSq • (C.expSmul (-conformalDimensionWeight d) sigma * u)) =
      C.toSecondOrder.laplacian u +
        (massSq • C.expSmul 2 sigma +
          (-conformalDimensionWeight d) • C.toSecondOrder.laplacian sigma -
          conformalDimensionWeight d ^ 2 •
            C.toSecondOrder.gamma sigma sigma) * u :=
  C.conformalKleinGordonSigma_conjugation
    (conformalDimensionWeight d) massSq sigma u

end ExponentialSecondOrderClockCalculus

end GaloisForLFunctions.HTGeometry
