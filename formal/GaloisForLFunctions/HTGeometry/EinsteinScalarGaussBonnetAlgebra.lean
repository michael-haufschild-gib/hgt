import GaloisForLFunctions.HTGeometry.KerrNewmanStationaryLimitAlgebra

/-!
# Exact Einstein--scalar--Gauss--Bonnet algebra

Coupling jets, Kerr Gauss--Bonnet curvature identities, and quasinormal damping from
arXiv:2609.03983.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex
open scoped ENNReal

noncomputable section

/-- Dilatonic Einstein--Gauss--Bonnet coupling `α exp (-γ φ) / 4`. -/
def edgbDilatonicCoupling (alpha gamma phi : ℝ) : ℝ :=
  alpha / 4 * Real.exp (-gamma * phi)

/-- Pure quadratic scalarization coupling `η φ² / 8`. -/
def esgbQuadraticCoupling (eta phi : ℝ) : ℝ :=
  eta / 8 * phi ^ 2

/-- Jet criterion separating spontaneous scalarization couplings from dilatonic ones. -/
def esgbScalarizationJetCriterion (f : ℝ → ℝ) : Prop :=
  deriv f 0 = 0 ∧ deriv (deriv f) 0 ≠ 0

theorem edgbDilatonicCoupling_zero (alpha gamma : ℝ) :
    edgbDilatonicCoupling alpha gamma 0 = alpha / 4 := by
  simp [edgbDilatonicCoupling]

theorem edgbDilatonicCoupling_hasDerivAt (alpha gamma phi : ℝ) :
    HasDerivAt (edgbDilatonicCoupling alpha gamma)
      ((alpha / 4) * (Real.exp (-gamma * phi) * (-gamma))) phi := by
  have hinner : HasDerivAt (fun x : ℝ => -gamma * x) (-gamma) phi := by
    simpa using (hasDerivAt_id phi).const_mul (-gamma)
  have hexp := (Real.hasDerivAt_exp (-gamma * phi)).comp phi hinner
  change HasDerivAt (fun x : ℝ => alpha / 4 * Real.exp (-gamma * x))
    ((alpha / 4) * (Real.exp (-gamma * phi) * (-gamma))) phi
  exact hexp.const_mul (alpha / 4)

theorem deriv_edgbDilatonicCoupling (alpha gamma phi : ℝ) :
    deriv (edgbDilatonicCoupling alpha gamma) phi =
      -(alpha * gamma) / 4 * Real.exp (-gamma * phi) := by
  rw [(edgbDilatonicCoupling_hasDerivAt alpha gamma phi).deriv]
  ring

theorem deriv_edgbDilatonicCoupling_zero (alpha gamma : ℝ) :
    deriv (edgbDilatonicCoupling alpha gamma) 0 = -(alpha * gamma) / 4 := by
  rw [deriv_edgbDilatonicCoupling]
  simp

theorem deriv_edgbDilatonicCoupling_zero_eq_zero_iff (alpha gamma : ℝ) :
    deriv (edgbDilatonicCoupling alpha gamma) 0 = 0 ↔
      alpha = 0 ∨ gamma = 0 := by
  rw [deriv_edgbDilatonicCoupling_zero]
  constructor
  · intro h
    have : alpha * gamma = 0 := by linarith
    exact mul_eq_zero.mp this
  · rintro (rfl | rfl) <;> simp

theorem esgbQuadraticCoupling_hasDerivAt (eta phi : ℝ) :
    HasDerivAt (esgbQuadraticCoupling eta) (eta / 8 * (2 * phi)) phi := by
  have h := ((hasDerivAt_id phi).pow 2).const_mul (eta / 8)
  change HasDerivAt (fun x : ℝ => eta / 8 * x ^ 2) (eta / 8 * (2 * phi)) phi
  simpa using h

theorem deriv_esgbQuadraticCoupling (eta phi : ℝ) :
    deriv (esgbQuadraticCoupling eta) phi = eta / 4 * phi := by
  rw [(esgbQuadraticCoupling_hasDerivAt eta phi).deriv]
  ring

theorem deriv_esgbQuadraticCoupling_zero (eta : ℝ) :
    deriv (esgbQuadraticCoupling eta) 0 = 0 := by
  simp [deriv_esgbQuadraticCoupling]

theorem deriv_deriv_esgbQuadraticCoupling_zero (eta : ℝ) :
    deriv (deriv (esgbQuadraticCoupling eta)) 0 = eta / 4 := by
  have hfun : deriv (esgbQuadraticCoupling eta) = fun phi => eta / 4 * phi := by
    funext phi
    exact deriv_esgbQuadraticCoupling eta phi
  rw [hfun]
  simpa only [id_eq, mul_one] using
    ((hasDerivAt_id (0 : ℝ)).const_mul (eta / 4)).deriv

theorem esgbQuadraticCoupling_scalarizationJetCriterion_iff (eta : ℝ) :
    esgbScalarizationJetCriterion (esgbQuadraticCoupling eta) ↔ eta ≠ 0 := by
  rw [esgbScalarizationJetCriterion, deriv_esgbQuadraticCoupling_zero,
    deriv_deriv_esgbQuadraticCoupling_zero]
  simp

theorem not_edgbDilatonicCoupling_unitGamma_scalarizationJetCriterion (alpha : ℝ) :
    ¬ esgbScalarizationJetCriterion (edgbDilatonicCoupling alpha 1) := by
  intro h
  have hfirst := h.1
  rw [deriv_edgbDilatonicCoupling_zero] at hfirst
  have halpha : alpha = 0 := by linarith
  subst alpha
  have hz : edgbDilatonicCoupling 0 1 = fun _ : ℝ => 0 := by
    funext phi
    simp [edgbDilatonicCoupling]
  rw [hz] at h
  have hsecond := h.2
  change deriv (deriv (0 : ℝ → ℝ)) 0 ≠ 0 at hsecond
  rw [deriv_zero, deriv_zero] at hsecond
  exact hsecond rfl

/-- Numerator of the Kerr Gauss--Bonnet invariant after setting `χ = a cos θ`. -/
def kerrGaussBonnetNumerator (radius chi : ℝ) : ℝ :=
  radius ^ 6 - 15 * radius ^ 4 * chi ^ 2 +
    15 * radius ^ 2 * chi ^ 4 - chi ^ 6

/-- Kerr Gauss--Bonnet invariant in the algebraic form quoted in arXiv:2609.03983. -/
def kerrGaussBonnetInvariant (mass radius chi : ℝ) : ℝ :=
  48 * mass ^ 2 * kerrGaussBonnetNumerator radius chi /
    (radius ^ 2 + chi ^ 2) ^ 6

def kerrGaussBonnetPolarInvariant
    (mass spin radius polar : ℝ) : ℝ :=
  kerrGaussBonnetInvariant mass radius (spin * Real.cos polar)

theorem kerrGaussBonnetNumerator_factor (radius chi : ℝ) :
    kerrGaussBonnetNumerator radius chi =
      (radius ^ 2 - chi ^ 2) *
        (radius ^ 4 - 14 * radius ^ 2 * chi ^ 2 + chi ^ 4) := by
  unfold kerrGaussBonnetNumerator
  ring

theorem kerrGaussBonnetNumerator_radicalFactor (radius chi : ℝ) :
    kerrGaussBonnetNumerator radius chi =
      (radius ^ 2 - chi ^ 2) *
        (radius ^ 2 - (7 + 4 * Real.sqrt 3) * chi ^ 2) *
        (radius ^ 2 - (7 - 4 * Real.sqrt 3) * chi ^ 2) := by
  rw [kerrGaussBonnetNumerator_factor]
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by positivity)
  ring_nf
  rw [hsqrt]
  ring

theorem kerrGaussBonnetNumerator_swap (radius chi : ℝ) :
    kerrGaussBonnetNumerator chi radius =
      -kerrGaussBonnetNumerator radius chi := by
  unfold kerrGaussBonnetNumerator
  ring

theorem kerrGaussBonnetNumerator_neg_radius (radius chi : ℝ) :
    kerrGaussBonnetNumerator (-radius) chi =
      kerrGaussBonnetNumerator radius chi := by
  unfold kerrGaussBonnetNumerator
  ring

theorem kerrGaussBonnetNumerator_neg_chi (radius chi : ℝ) :
    kerrGaussBonnetNumerator radius (-chi) =
      kerrGaussBonnetNumerator radius chi := by
  unfold kerrGaussBonnetNumerator
  ring

theorem kerrGaussBonnetNumerator_diagonal (radius : ℝ) :
    kerrGaussBonnetNumerator radius radius = 0 := by
  simp [kerrGaussBonnetNumerator_factor]

theorem kerrGaussBonnetNumerator_antidiagonal (radius : ℝ) :
    kerrGaussBonnetNumerator radius (-radius) = 0 := by
  rw [kerrGaussBonnetNumerator_neg_chi,
    kerrGaussBonnetNumerator_diagonal]

theorem kerrGaussBonnetNumerator_axis (radius : ℝ) :
    kerrGaussBonnetNumerator radius 0 = radius ^ 6 := by
  simp [kerrGaussBonnetNumerator]

theorem kerrGaussBonnetNumerator_center (chi : ℝ) :
    kerrGaussBonnetNumerator 0 chi = -chi ^ 6 := by
  simp [kerrGaussBonnetNumerator]

theorem kerrGaussBonnetInvariant_swap (mass radius chi : ℝ) :
    kerrGaussBonnetInvariant mass chi radius =
      -kerrGaussBonnetInvariant mass radius chi := by
  rw [kerrGaussBonnetInvariant, kerrGaussBonnetInvariant,
    kerrGaussBonnetNumerator_swap]
  ring

theorem kerrGaussBonnetInvariant_diagonal (mass radius : ℝ) :
    kerrGaussBonnetInvariant mass radius radius = 0 := by
  simp [kerrGaussBonnetInvariant, kerrGaussBonnetNumerator_diagonal]

theorem kerrGaussBonnetInvariant_axis (mass radius : ℝ) :
    kerrGaussBonnetInvariant mass radius 0 = 48 * mass ^ 2 / radius ^ 6 := by
  by_cases hr : radius = 0
  · subst radius
    simp [kerrGaussBonnetInvariant, kerrGaussBonnetNumerator]
  · rw [kerrGaussBonnetInvariant, kerrGaussBonnetNumerator_axis]
    field_simp
    ring

theorem kerrGaussBonnetPolarInvariant_equator (mass spin radius : ℝ) :
    kerrGaussBonnetPolarInvariant mass spin radius (Real.pi / 2) =
      48 * mass ^ 2 / radius ^ 6 := by
  rw [kerrGaussBonnetPolarInvariant]
  simp [kerrGaussBonnetInvariant_axis]

theorem kerrGaussBonnetPolarInvariant_axis (mass spin radius : ℝ) :
    kerrGaussBonnetPolarInvariant mass spin radius 0 =
      kerrGaussBonnetInvariant mass radius spin := by
  simp [kerrGaussBonnetPolarInvariant]

theorem kerrGaussBonnetPolarInvariant_neg_spin
    (mass spin radius polar : ℝ) :
    kerrGaussBonnetPolarInvariant mass (-spin) radius polar =
      kerrGaussBonnetPolarInvariant mass spin radius polar := by
  simp [kerrGaussBonnetPolarInvariant, kerrGaussBonnetInvariant,
    kerrGaussBonnetNumerator_neg_chi]

/-- Physically extended damping time: a real frequency has infinite lifetime. -/
def qnmDampingTime (omega : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal |omega.im|)⁻¹

theorem qnmDampingTime_neg (omega : ℂ) :
    qnmDampingTime (-omega) = qnmDampingTime omega := by
  simp [qnmDampingTime]

theorem qnmDampingTime_conj (omega : ℂ) :
    qnmDampingTime (starRingEnd ℂ omega) = qnmDampingTime omega := by
  simp [qnmDampingTime]

theorem qnmDampingTime_realShift (omega : ℂ) (shift : ℝ) :
    qnmDampingTime (omega + shift) = qnmDampingTime omega := by
  simp [qnmDampingTime]

theorem qnmDampingTime_ofReal (frequency : ℝ) :
    qnmDampingTime frequency = ⊤ := by
  simp [qnmDampingTime]

theorem qnmDampingTime_I : qnmDampingTime Complex.I = 1 := by
  simp only [qnmDampingTime, Complex.I_im, abs_one, ENNReal.ofReal_one, inv_one]

end
end GaloisForLFunctions.HTGeometry
