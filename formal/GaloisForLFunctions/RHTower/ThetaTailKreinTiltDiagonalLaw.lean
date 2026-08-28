import GaloisForLFunctions.RHTower.ThetaTailKreinXiCentTiltCollapse

/-!
# Diagonal law of the tilt channels

The pointwise (rank-one) law of the two tilt channels: the difference of their squared moduli is
`4c` times the horizontal modulus derivative pairing `Re(ξc′·conj ξc)`.  On the critical boundary
`Re w = 0` the completed transform is real and its derivative is purely imaginary, so this pairing
vanishes identically: the diagonal form of losslessness, and the exact reason the modulus of the
completed transform is critical at the wall in the horizontal direction.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- On the critical boundary the completed transform is real. -/
theorem conj_xiCent_I_mul_ofReal (τ : ℝ) :
    conj (xiCent (Complex.I * τ)) = xiCent (Complex.I * τ) := by
  have hconj : conj (Complex.I * (τ : ℂ)) = -(Complex.I * (τ : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [← xiCent_conj, hconj, xiCent_even]

/-- On the critical boundary the derivative of the completed transform is purely imaginary. -/
theorem conj_deriv_xiCent_I_mul_ofReal (τ : ℝ) :
    conj (deriv xiCent (Complex.I * τ)) = -deriv xiCent (Complex.I * τ) := by
  have hconj : conj (Complex.I * (τ : ℂ)) = -(Complex.I * (τ : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [← deriv_xiCent_conj, hconj, deriv_xiCent_neg]

/-- **Wall vanishing of the horizontal modulus pairing.**  On the critical boundary the pairing
`Re(ξc′·conj ξc)` — half the horizontal derivative of the squared modulus — is zero. -/
theorem re_deriv_xiCent_mul_conj_xiCent_I_mul (τ : ℝ) :
    (deriv xiCent (Complex.I * τ) * conj (xiCent (Complex.I * τ))).re = 0 := by
  set z := deriv xiCent (Complex.I * τ)
  set f := xiCent (Complex.I * τ)
  have hz : conj z = -z := conj_deriv_xiCent_I_mul_ofReal τ
  have hf : conj f = f := conj_xiCent_I_mul_ofReal τ
  have hsum : z * conj f + conj (z * conj f) = 0 := by
    rw [map_mul, hz, Complex.conj_conj, hf]
    ring
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hre
  linarith

/-- **Rank-one tilt law.**  The difference of the squared channel moduli is `4c` times the
horizontal modulus pairing; positivity of the diagonal Bezoutian is exactly the sign of
`Re(ξc′·conj ξc)`. -/
theorem normSq_xiCentTiltPlus_sub_normSq_xiCentTiltMinus (c : ℝ) (w : ℂ) :
    Complex.normSq (xiCentTiltPlus c w) - Complex.normSq (xiCentTiltMinus c w) =
      4 * c * (deriv xiCent w * conj (xiCent w)).re := by
  have hplus : Complex.normSq (xiCentTiltPlus c w) =
      Complex.normSq (deriv xiCent w) + Complex.normSq ((c : ℂ) * xiCent w) +
        2 * (deriv xiCent w * conj ((c : ℂ) * xiCent w)).re := by
    unfold xiCentTiltPlus
    exact Complex.normSq_add _ _
  have hminus : Complex.normSq (xiCentTiltMinus c w) =
      Complex.normSq (deriv xiCent w) + Complex.normSq ((c : ℂ) * xiCent w) +
        2 * (deriv xiCent w * conj (-((c : ℂ) * xiCent w))).re := by
    unfold xiCentTiltMinus
    rw [sub_eq_add_neg, Complex.normSq_add, Complex.normSq_neg]
  have hconj : conj (-((c : ℂ) * xiCent w)) = -((c : ℂ) * conj (xiCent w)) := by
    rw [map_neg, map_mul, Complex.conj_ofReal]
  have hplusre : (deriv xiCent w * conj ((c : ℂ) * xiCent w)).re =
      c * (deriv xiCent w * conj (xiCent w)).re := by
    rw [map_mul, Complex.conj_ofReal,
      show deriv xiCent w * ((c : ℂ) * conj (xiCent w)) =
        (c : ℂ) * (deriv xiCent w * conj (xiCent w)) by ring, Complex.re_ofReal_mul]
  have hminusre : (deriv xiCent w * conj (-((c : ℂ) * xiCent w))).re =
      -(c * (deriv xiCent w * conj (xiCent w)).re) := by
    rw [hconj,
      show deriv xiCent w * -((c : ℂ) * conj (xiCent w)) =
        -((c : ℂ) * (deriv xiCent w * conj (xiCent w))) by ring, Complex.neg_re,
      Complex.re_ofReal_mul]
  rw [hplus, hminus, hplusre, hminusre]
  ring

/-- Diagonal wall losslessness in squared-modulus form: on the critical boundary the two tilt
channels have equal `normSq`. -/
theorem normSq_xiCentTiltMinus_I_mul (c τ : ℝ) :
    Complex.normSq (xiCentTiltMinus c (Complex.I * τ)) =
      Complex.normSq (xiCentTiltPlus c (Complex.I * τ)) := by
  have h := normSq_xiCentTiltPlus_sub_normSq_xiCentTiltMinus c (Complex.I * τ)
  rw [re_deriv_xiCent_mul_conj_xiCent_I_mul] at h
  linarith [h]

end

end RHTower
