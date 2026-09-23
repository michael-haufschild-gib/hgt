import GaloisForLFunctions.RHTower.FZZCigarParityFullLinearRieszStabilityCone
import GaloisForLFunctions.RHTower.FZZCigarParityHermitianReflectionDetectorCone

/-!
# Full Hermitian Riesz stability hypersurface for the FZZ parity block

The four real coefficients of a Hermitian reporter exhaust all local quadratic interactions on
the literal two-scale source block.  This module constructs their source-metric Riesz chart and
classifies actual spectral reality by one exact real discriminant.  Its strongest no-go is a
unique cone-valued reporter whose Riesz interaction annihilates the canonical generator exactly.
-/

open Complex

namespace RHTower

noncomputable section

/-- Sesquilinear polarization of the complete Hermitian reporter. -/
def fzzCigarParityHermitianQuadraticPairing
    (a b c d : ℝ) (u v : ℂ × ℂ) : ℂ :=
  star u.1 * ((a : ℂ) * v.1 + ((b : ℂ) + Complex.I * (c : ℂ)) * v.2) +
    star u.2 * (((b : ℂ) - Complex.I * (c : ℂ)) * v.1 + (d : ℂ) * v.2)

theorem fzzCigarParityHermitianQuadraticPairing_self
    (a b c d : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticPairing a b c d u u =
      fzzCigarParityHermitianQuadraticObservable a b c d u := by
  rfl

/-- Complete source-metric Riesz representative of an arbitrary Hermitian reporter. -/
def fzzCigarParityDilatedFullHermitianRieszOperator
    (beta a b c d : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  let E := fzzCigarParityDilatedTwoScaleKreinGap beta
  ((((-fzzKreinRAt beta * a + fzzKreinQAt beta * b) / E : ℝ) : ℂ) * u.1 -
      Complex.I * (((fzzKreinQAt beta * c) / E : ℝ) : ℂ) * u.1 +
      (((-fzzKreinRAt beta * b + fzzKreinQAt beta * d) / E : ℝ) : ℂ) * u.2 -
      Complex.I * (((fzzKreinRAt beta * c) / E : ℝ) : ℂ) * u.2,
    ((((fzzKreinQAt beta * a - fzzKreinPAt beta * b) / E : ℝ) : ℂ) * u.1 +
      Complex.I * (((fzzKreinPAt beta * c) / E : ℝ) : ℂ) * u.1 +
      (((fzzKreinQAt beta * b - fzzKreinPAt beta * d) / E : ℝ) : ℂ) * u.2 +
      Complex.I * (((fzzKreinQAt beta * c) / E : ℝ) : ℂ) * u.2))

theorem fzzCigarParityDilatedFullHermitianRieszOperator_represents
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta u
        (fzzCigarParityDilatedFullHermitianRieszOperator beta a b c d v) =
      fzzCigarParityHermitianQuadraticPairing a b c d u v := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have hgapC :
      (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) =
        (fzzKreinQAt beta : ℂ) ^ (2 : ℕ) -
          (fzzKreinPAt beta : ℂ) * (fzzKreinRAt beta : ℂ) := by
    rw [fzzCigarParityDilatedTwoScaleKreinGap]
    push_cast
    ring
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedFullHermitianRieszOperator,
    fzzCigarParityHermitianQuadraticPairing]
  field_simp [hEC]
  rw [hgapC]
  ring

/-- Canonical source generator plus the complete Hermitian Riesz interaction. -/
def fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator
    (beta a b c d : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  let Au := fzzCigarParityDilatedTwoScaleKreinOperator beta u
  let Bu := fzzCigarParityDilatedFullHermitianRieszOperator beta a b c d u
  (Au.1 + Bu.1, Au.2 + Bu.2)

def fzzCigarParityDilatedFullHermitianRieszDiagOne
    (beta a b c : ℝ) : ℂ :=
  (fzzKreinPAt beta : ℂ) +
    (((-fzzKreinRAt beta * a + fzzKreinQAt beta * b) /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ) -
    Complex.I * (((fzzKreinQAt beta * c) /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ)

def fzzCigarParityDilatedFullHermitianRieszUpper
    (beta b c d : ℝ) : ℂ :=
  (fzzKreinQAt beta : ℂ) +
    (((-fzzKreinRAt beta * b + fzzKreinQAt beta * d) /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ) -
    Complex.I * (((fzzKreinRAt beta * c) /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ)

def fzzCigarParityDilatedFullHermitianRieszLower
    (beta a b c : ℝ) : ℂ :=
  -((fzzKreinPAt beta * fzzKreinQAt beta /
      fzzKreinRAt beta : ℝ) : ℂ) +
    ((((fzzKreinQAt beta * a - fzzKreinPAt beta * b) /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ)) +
    Complex.I * (((fzzKreinPAt beta * c) /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ)

def fzzCigarParityDilatedFullHermitianRieszDiagTwo
    (beta b c d : ℝ) : ℂ :=
  -(fzzKreinPAt beta : ℂ) +
    (((fzzKreinQAt beta * b - fzzKreinPAt beta * d) /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ) +
    Complex.I * (((fzzKreinQAt beta * c) /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ)

theorem fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_matrix
    (beta a b c d : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator beta a b c d u =
      (fzzCigarParityDilatedFullHermitianRieszDiagOne beta a b c * u.1 +
          fzzCigarParityDilatedFullHermitianRieszUpper beta b c d * u.2,
        fzzCigarParityDilatedFullHermitianRieszLower beta a b c * u.1 +
          fzzCigarParityDilatedFullHermitianRieszDiagTwo beta b c d * u.2) := by
  rcases u with ⟨u₁, u₂⟩
  apply Prod.ext <;>
    simp [fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator,
      fzzCigarParityDilatedFullHermitianRieszOperator,
      fzzCigarParityDilatedTwoScaleKreinOperator,
      fzzCigarParityDilatedFullHermitianRieszDiagOne,
      fzzCigarParityDilatedFullHermitianRieszUpper,
      fzzCigarParityDilatedFullHermitianRieszLower,
      fzzCigarParityDilatedFullHermitianRieszDiagTwo] <;>
    ring

/-- Real trace of the complete Hermitian Riesz perturbation. -/
def fzzCigarParityDilatedFullHermitianRieszTrace
    (beta a b d : ℝ) : ℝ :=
  (-fzzKreinRAt beta * a + 2 * fzzKreinQAt beta * b -
      fzzKreinPAt beta * d) /
    fzzCigarParityDilatedTwoScaleKreinGap beta

/-- Real determinant exposed by `G(A+B)=G A+H`. -/
def fzzCigarParityDilatedFullHermitianRieszDeterminant
    (beta a b c d : ℝ) : ℝ :=
  (b ^ (2 : ℕ) + c ^ (2 : ℕ) -
      (a - fzzKreinPAt beta * fzzCigarParityDilatedTwoScaleKreinGap beta /
          fzzKreinRAt beta) *
        (d + fzzCigarParityDilatedTwoScaleKreinGap beta)) /
    fzzCigarParityDilatedTwoScaleKreinGap beta

def fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
    (beta a b c d : ℝ) : ℝ :=
  fzzCigarParityDilatedFullHermitianRieszTrace beta a b d ^ (2 : ℕ) -
    4 * fzzCigarParityDilatedFullHermitianRieszDeterminant beta a b c d

theorem fzzCigarParityDilatedFullHermitianRiesz_trace_eq
    (beta a b c d : ℝ) :
    fzzCigarParityDilatedFullHermitianRieszDiagOne beta a b c +
        fzzCigarParityDilatedFullHermitianRieszDiagTwo beta b c d =
      (fzzCigarParityDilatedFullHermitianRieszTrace beta a b d : ℂ) := by
  simp [fzzCigarParityDilatedFullHermitianRieszDiagOne,
    fzzCigarParityDilatedFullHermitianRieszDiagTwo,
    fzzCigarParityDilatedFullHermitianRieszTrace]
  ring

theorem fzzCigarParityDilatedFullHermitianRiesz_determinant_eq
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) :
    fzzCigarParityDilatedFullHermitianRieszDiagOne beta a b c *
          fzzCigarParityDilatedFullHermitianRieszDiagTwo beta b c d -
        fzzCigarParityDilatedFullHermitianRieszUpper beta b c d *
          fzzCigarParityDilatedFullHermitianRieszLower beta a b c =
      (fzzCigarParityDilatedFullHermitianRieszDeterminant beta a b c d : ℂ) := by
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hR := (fzzKreinRAt_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have hRC : (fzzKreinRAt beta : ℂ) ≠ 0 := by exact_mod_cast hR
  simp [fzzCigarParityDilatedFullHermitianRieszDiagOne,
    fzzCigarParityDilatedFullHermitianRieszUpper,
    fzzCigarParityDilatedFullHermitianRieszLower,
    fzzCigarParityDilatedFullHermitianRieszDiagTwo,
    fzzCigarParityDilatedFullHermitianRieszDeterminant]
  field_simp [hE, hR, hEC, hRC]
  rw [fzzCigarParityDilatedTwoScaleKreinGap]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_formallySelfAdjoint
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
        (fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator beta a b c d u) v =
      fzzCigarParityDilatedTwoScaleKreinPairing beta u
        (fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator beta a b c d v) := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hR := (fzzKreinRAt_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have hRC : (fzzKreinRAt beta : ℂ) ≠ 0 := by exact_mod_cast hR
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator,
    fzzCigarParityDilatedFullHermitianRieszOperator,
    fzzCigarParityDilatedTwoScaleKreinOperator,
    Complex.conj_ofReal]
  field_simp [hE, hR, hEC, hRC]
  ring

private theorem hc36_twoByTwoComplexEigenvalue_quadratic
    {a b c d lambda : ℂ} {v : ℂ × ℂ}
    (hv : v ≠ 0)
    (heigen :
      (a * v.1 + b * v.2, c * v.1 + d * v.2) = lambda • v) :
    lambda ^ (2 : ℕ) - (a + d) * lambda + (a * d - b * c) = 0 := by
  rcases v with ⟨x, y⟩
  have hfirst := congrArg Prod.fst heigen
  have hsecond := congrArg Prod.snd heigen
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hfirst hsecond
  have hfirstZero : a * x + b * y - lambda * x = 0 := sub_eq_zero.mpr hfirst
  have hsecondZero : c * x + d * y - lambda * y = 0 := sub_eq_zero.mpr hsecond
  have hxprod :
      (lambda ^ (2 : ℕ) - (a + d) * lambda + (a * d - b * c)) * x = 0 := by
    calc
      (lambda ^ (2 : ℕ) - (a + d) * lambda + (a * d - b * c)) * x =
          -((lambda - d) * (a * x + b * y - lambda * x) +
            b * (c * x + d * y - lambda * y)) := by ring
      _ = 0 := by rw [hfirstZero, hsecondZero]; ring
  have hyprod :
      (lambda ^ (2 : ℕ) - (a + d) * lambda + (a * d - b * c)) * y = 0 := by
    calc
      (lambda ^ (2 : ℕ) - (a + d) * lambda + (a * d - b * c)) * y =
          -(c * (a * x + b * y - lambda * x) +
            (lambda - a) * (c * x + d * y - lambda * y)) := by ring
      _ = 0 := by rw [hfirstZero, hsecondZero]; ring
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy
      apply hv
      simp [hx, hy]
    exact (mul_eq_zero.mp hyprod).resolve_right hy
  · exact (mul_eq_zero.mp hxprod).resolve_right hx

private theorem hc36_twoByTwoComplex_eigenpair_of_quadratic_root
    {a b c d lambda : ℂ}
    (hroot : lambda ^ (2 : ℕ) - (a + d) * lambda + (a * d - b * c) = 0) :
    (a * b + b * (lambda - a), c * b + d * (lambda - a)) =
      lambda • (b, lambda - a) := by
  apply Prod.ext
  · simp only [Prod.smul_fst, smul_eq_mul]
    ring
  · simp only [Prod.smul_snd, smul_eq_mul]
    linear_combination -hroot

private theorem hc36_complexQuadraticRoot_eq_star_of_real_discriminant_nonneg
    {T D : ℝ} {lambda : ℂ}
    (hdisc : 0 ≤ T ^ (2 : ℕ) - 4 * D)
    (hroot : lambda ^ (2 : ℕ) - (T : ℂ) * lambda + (D : ℂ) = 0) :
    lambda = star lambda := by
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  norm_num [Complex.mul_re, Complex.mul_im, pow_two] at hre him
  by_cases hli : lambda.im = 0
  · apply Complex.ext <;> simp [hli]
  · have hreal : lambda.re = T / 2 := by
      have hfactor : (2 * lambda.re - T) * lambda.im = 0 := by nlinarith
      have := (mul_eq_zero.mp hfactor).resolve_right hli
      linarith
    have hdiscEq : T ^ (2 : ℕ) - 4 * D = -4 * lambda.im ^ (2 : ℕ) := by nlinarith
    nlinarith [sq_pos_of_ne_zero hli]

theorem fzzCigarParityDilatedFullHermitianRiesz_eigenvalue_characteristic
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ)
    {lambda : ℂ} {v : ℂ × ℂ} (hv : v ≠ 0)
    (heigen :
      fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator beta a b c d v =
        lambda • v) :
    lambda ^ (2 : ℕ) -
        (fzzCigarParityDilatedFullHermitianRieszTrace beta a b d : ℂ) * lambda +
        (fzzCigarParityDilatedFullHermitianRieszDeterminant beta a b c d : ℂ) = 0 := by
  rw [fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_matrix] at heigen
  have hroot := hc36_twoByTwoComplexEigenvalue_quadratic hv heigen
  rw [fzzCigarParityDilatedFullHermitianRiesz_trace_eq,
    fzzCigarParityDilatedFullHermitianRiesz_determinant_eq hbeta] at hroot
  exact hroot

/-- Actual spectral reality of complete Hermitian Riesz dynamics. -/
def FZZCigarParityDilatedFullHermitianRieszSpectrallyReal
    (beta a b c d : ℝ) : Prop :=
  ∀ lambda : ℂ, ∀ v : ℂ × ℂ,
    v ≠ 0 →
    fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator beta a b c d v =
      lambda • v →
    lambda = star lambda

theorem fzzCigarParityDilatedFullHermitianRieszSpectrallyReal_of_discriminant_nonneg
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ)
    (hdisc : 0 ≤
      fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant beta a b c d) :
    FZZCigarParityDilatedFullHermitianRieszSpectrallyReal beta a b c d := by
  intro lambda v hv heigen
  apply hc36_complexQuadraticRoot_eq_star_of_real_discriminant_nonneg
  · simpa [fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant] using hdisc
  · exact fzzCigarParityDilatedFullHermitianRiesz_eigenvalue_characteristic
      hbeta a b c d hv heigen

/-- Positive-imaginary root in negative complete discriminant chamber. -/
def fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue
    (beta a b c d : ℝ) : ℂ :=
  (fzzCigarParityDilatedFullHermitianRieszTrace beta a b d / 2 : ℝ) +
    Complex.I *
      (Real.sqrt
        (-fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
          beta a b c d) / 2 : ℝ)

def fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector
    (beta a b c d : ℝ) : ℂ × ℂ :=
  (fzzCigarParityDilatedFullHermitianRieszUpper beta b c d,
    fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d -
      fzzCigarParityDilatedFullHermitianRieszDiagOne beta a b c)

theorem fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue_root
    {beta a b c d : ℝ}
    (hdisc :
      fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
        beta a b c d < 0) :
    fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d ^ (2 : ℕ) -
        (fzzCigarParityDilatedFullHermitianRieszTrace beta a b d : ℂ) *
          fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d +
        (fzzCigarParityDilatedFullHermitianRieszDeterminant beta a b c d : ℂ) = 0 := by
  let T := fzzCigarParityDilatedFullHermitianRieszTrace beta a b d
  let D := fzzCigarParityDilatedFullHermitianRieszDeterminant beta a b c d
  let disc :=
    fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant beta a b c d
  let y := Real.sqrt (-disc) / 2
  have hdiscEq : disc = T ^ (2 : ℕ) - 4 * D := by rfl
  have hnonneg : 0 ≤ -disc := by dsimp [disc]; linarith
  have hy2 : y ^ (2 : ℕ) = -disc / 4 := by
    dsimp [y]
    rw [div_pow, Real.sq_sqrt hnonneg]
    norm_num
  have heigenvalue :
      fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d =
        (T / 2 : ℝ) + Complex.I * (y : ℝ) := by rfl
  rw [heigenvalue]
  apply Complex.ext
  · norm_num [Complex.mul_re, Complex.mul_im, pow_two]
    nlinarith [hy2, hdiscEq]
  · norm_num [Complex.mul_re, Complex.mul_im, pow_two]
    ring

theorem fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue_im_pos
    {beta a b c d : ℝ}
    (hdisc :
      fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
        beta a b c d < 0) :
    0 < (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue
      beta a b c d).im := by
  rw [fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue]
  simp only [add_im, ofReal_im, zero_add, mul_im, I_re, mul_zero, I_im, ofReal_re]
  have hsqrt := Real.sqrt_pos.2 (neg_pos.mpr hdisc)
  nlinarith

theorem fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue_not_real
    {beta a b c d : ℝ}
    (hdisc :
      fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
        beta a b c d < 0) :
    fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d ≠
      star (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue
        beta a b c d) := by
  intro h
  have him := congrArg Complex.im h
  have hstar :
      (star (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue
        beta a b c d)).im =
        -(fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue
          beta a b c d).im := by
    change ((starRingEnd ℂ)
      (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue
        beta a b c d)).im = _
    exact Complex.conj_im _
  rw [hstar] at him
  linarith [fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue_im_pos hdisc]

theorem fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) {a b c d : ℝ}
    (hdisc :
      fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
        beta a b c d < 0) :
    fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d ≠ 0 := by
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  have hsecond := congrArg Prod.snd hzero
  simp only [fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector,
    Prod.fst_zero, Prod.snd_zero] at hfirst hsecond
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hR := (fzzKreinRAt_pos hbeta).ne'
  have himUpper := congrArg Complex.im hfirst
  norm_num [fzzCigarParityDilatedFullHermitianRieszUpper,
    Complex.mul_re, Complex.mul_im] at himUpper
  have hc : c = 0 := by
    field_simp [hE, hR] at himUpper
    rcases himUpper with (hRzero | hczero) | hEzero
    · exact False.elim (hR hRzero)
    · exact hczero
    · exact False.elim (hE hEzero)
  have himSecond := congrArg Complex.im hsecond
  norm_num [fzzCigarParityDilatedFullHermitianRieszDiagOne, hc,
    Complex.mul_re, Complex.mul_im] at himSecond
  have himPos :=
    fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue_im_pos hdisc
  rw [hc] at himPos
  linarith

theorem fzzCigarParityDilatedFullHermitianRieszInstabilityEigenpair
    {beta : ℝ} (hbeta : 0 < beta) {a b c d : ℝ}
    (hdisc :
      fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
        beta a b c d < 0) :
    fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator beta a b c d
        (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d) =
      fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d •
        fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d := by
  have hroot :=
    fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue_root hdisc
  rw [← fzzCigarParityDilatedFullHermitianRiesz_trace_eq beta a b c d,
    ← fzzCigarParityDilatedFullHermitianRiesz_determinant_eq hbeta a b c d] at hroot
  have hp := hc36_twoByTwoComplex_eigenpair_of_quadratic_root hroot
  rw [fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_matrix]
  simpa [fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector] using hp

/-- Every negative-discriminant full-Hermitian mode is neutral in the literal source metric. -/
theorem fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector_null
    {beta : ℝ} (hbeta : 0 < beta) {a b c d : ℝ}
    (hdisc :
      fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
        beta a b c d < 0) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
        (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d)
        (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d) = 0 := by
  have hself :=
    fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_formallySelfAdjoint
      hbeta a b c d
      (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d)
      (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d)
  rw [fzzCigarParityDilatedFullHermitianRieszInstabilityEigenpair hbeta hdisc] at hself
  rw [fzzCigarParityDilatedTwoScaleKreinPairing_smul_left,
    fzzCigarParityDilatedTwoScaleKreinPairing_smul_right] at hself
  have hfactor :
      (star (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue
          beta a b c d) -
          fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d) *
        fzzCigarParityDilatedTwoScaleKreinPairing beta
          (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d)
          (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d) = 0 := by
    calc
      (star (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue
            beta a b c d) -
            fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d) *
          fzzCigarParityDilatedTwoScaleKreinPairing beta
            (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d)
            (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d) =
        star (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue
            beta a b c d) *
            fzzCigarParityDilatedTwoScaleKreinPairing beta
              (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d)
              (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d) -
          fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d *
            fzzCigarParityDilatedTwoScaleKreinPairing beta
              (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d)
              (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d) := by ring
      _ = 0 := sub_eq_zero.mpr hself
  exact (mul_eq_zero.mp hfactor).resolve_left
    (sub_ne_zero.mpr
      (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue_not_real hdisc).symm)

theorem not_fzzCigarParityDilatedFullHermitianRieszSpectrallyReal_of_discriminant_neg
    {beta : ℝ} (hbeta : 0 < beta) {a b c d : ℝ}
    (hdisc :
      fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
        beta a b c d < 0) :
    ¬ FZZCigarParityDilatedFullHermitianRieszSpectrallyReal beta a b c d := by
  intro hreal
  exact fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue_not_real hdisc
    (hreal
      (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvalue beta a b c d)
      (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector beta a b c d)
      (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector_ne_zero hbeta hdisc)
      (fzzCigarParityDilatedFullHermitianRieszInstabilityEigenpair hbeta hdisc))

/-- Complete four-parameter spectral classification. -/
theorem fzzCigarParityDilatedFullHermitianRieszSpectrallyReal_iff_discriminant_nonneg
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) :
    FZZCigarParityDilatedFullHermitianRieszSpectrallyReal beta a b c d ↔
      0 ≤ fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
        beta a b c d := by
  constructor
  · intro hreal
    by_contra hnot
    have hneg :
        fzzCigarParityDilatedFullHermitianRieszCharacteristicDiscriminant
          beta a b c d < 0 := lt_of_not_ge hnot
    exact (not_fzzCigarParityDilatedFullHermitianRieszSpectrallyReal_of_discriminant_neg
      hbeta hneg) hreal
  · exact fzzCigarParityDilatedFullHermitianRieszSpectrallyReal_of_discriminant_nonneg
      hbeta a b c d

/-- First coefficient of the source-defined reporter that cancels the canonical generator. -/
def fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst
    (beta : ℝ) : ℝ :=
  fzzKreinPAt beta * fzzCigarParityDilatedTwoScaleKreinGap beta /
    fzzKreinRAt beta

/-- Second diagonal coefficient of the exact generator-annihilating reporter. -/
def fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth
    (beta : ℝ) : ℝ :=
  -fzzCigarParityDilatedTwoScaleKreinGap beta

/-- The complete Hermitian Riesz interaction contains an exact source-defined annihilator. -/
theorem fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_annihilator
    {beta : ℝ} (hbeta : 0 < beta) (u : ℂ × ℂ) :
    fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator beta
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) u = 0 := by
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hR := (fzzKreinRAt_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have h11 :
      fzzCigarParityDilatedFullHermitianRieszDiagOne beta
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0 = 0 := by
    simp [fzzCigarParityDilatedFullHermitianRieszDiagOne,
      fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst]
    field_simp [hE, hR]
    ring
  have h12 :
      fzzCigarParityDilatedFullHermitianRieszUpper beta 0 0
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) = 0 := by
    simp [fzzCigarParityDilatedFullHermitianRieszUpper,
      fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth]
    field_simp [hEC]
    ring
  have h21 :
      fzzCigarParityDilatedFullHermitianRieszLower beta
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0 = 0 := by
    simp [fzzCigarParityDilatedFullHermitianRieszLower,
      fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst]
    field_simp [hE, hR]
    ring
  have h22 :
      fzzCigarParityDilatedFullHermitianRieszDiagTwo beta 0 0
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) = 0 := by
    simp [fzzCigarParityDilatedFullHermitianRieszDiagTwo,
      fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth, hE]
  rw [fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_matrix]
  simp [h11, h12, h21, h22]

theorem fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta ≠ 0 := by
  exact neg_ne_zero.mpr (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'

theorem fzzCigarParityDilatedFullHermitianRieszAnnihilator_strictCone
    {beta : ℝ} (hbeta : 0 < beta) :
    (0 : ℝ) ^ (2 : ℕ) + 0 ^ (2 : ℕ) <
      fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta ^ (2 : ℕ) := by
  have hE := fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta
  simp [fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth]
  positivity

/-- The annihilator is simultaneously a universal reciprocal-radius reflection detector. -/
theorem fzzCigarParityDilatedFullHermitianRieszAnnihilator_universalDetector
    {beta : ℝ} (hbeta : 0 < beta) :
    FZZCigarParityHermitianUniversalRadialReflectionSeparating
      (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0
      (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) := by
  exact fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_cone
    _ _ _ _
    (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth_ne_zero hbeta)
    (le_of_lt
      (fzzCigarParityDilatedFullHermitianRieszAnnihilator_strictCone hbeta))

/-- Despite annihilating local dynamics, the same reporter remains an exact pointwise critical-line
detector under functional-equation reflection. -/
theorem fzzCigarParityDilatedFullHermitianRieszAnnihilatorMellinReading_eq_reflection_iff
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParityMellinCharacterHermitianReading
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) rho =
      fzzCigarParityMellinCharacterHermitianReading
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta)
        (criticalLineReflectionPoint rho) ↔
      rho.re = 1 / 2 := by
  exact fzzCigarParityMellinCharacterHermitianReading_eq_reflection_iff
    _ _ _ _
    (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth_ne_zero hbeta)
    (le_of_lt
      (fzzCigarParityDilatedFullHermitianRieszAnnihilator_strictCone hbeta)) rho

/-- Riesz injectivity makes the source-defined annihilator unique in all four Hermitian
coordinates. -/
theorem fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_all_zero_iff
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) :
    (∀ u : ℂ × ℂ,
      fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator beta a b c d u = 0) ↔
      a = fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta ∧
      b = 0 ∧ c = 0 ∧
      d = fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta := by
  constructor
  · intro hall
    have hB : ∀ v : ℂ × ℂ,
        fzzCigarParityDilatedFullHermitianRieszOperator beta a b c d v =
          fzzCigarParityDilatedFullHermitianRieszOperator beta
            (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0
            (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) v := by
      intro v
      have heq := (hall v).trans
        (fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_annihilator
          hbeta v).symm
      rcases v with ⟨v₁, v₂⟩
      simp [fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator] at heq
      exact Prod.ext heq.1 heq.2
    have hpair : ∀ u v : ℂ × ℂ,
        fzzCigarParityHermitianQuadraticPairing a b c d u v =
          fzzCigarParityHermitianQuadraticPairing
            (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0
            (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) u v := by
      intro u v
      rw [← fzzCigarParityDilatedFullHermitianRieszOperator_represents
          hbeta a b c d u v,
        hB v,
        fzzCigarParityDilatedFullHermitianRieszOperator_represents
          hbeta
          (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0
          (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) u v]
    have haC := hpair (1, 0) (1, 0)
    have hbcC := hpair (1, 0) (0, 1)
    have hdC := hpair (0, 1) (0, 1)
    simp [fzzCigarParityHermitianQuadraticPairing] at haC hbcC hdC
    have hb := congrArg Complex.re hbcC
    have hc := congrArg Complex.im hbcC
    norm_num [Complex.mul_re, Complex.mul_im] at hb hc
    exact ⟨by exact_mod_cast haC, hb, hc, by exact_mod_cast hdC⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩ u
    exact fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_annihilator
      hbeta u

/-- Strong detector-annihilator no-go: a unique strict-cone RH detector has identically zero local
generator, while retaining the pointwise critical-line reflection law. -/
theorem fzzCigarParityDilatedFullHermitianRiesz_detectorAnnihilatorNoGo
    {beta : ℝ} (hbeta : 0 < beta) :
    (∀ u : ℂ × ℂ,
      fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator beta
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) u = 0) ∧
      FZZCigarParityHermitianUniversalRadialReflectionSeparating
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFirst beta) 0 0
        (fzzCigarParityDilatedFullHermitianRieszAnnihilatorFourth beta) := by
  exact ⟨fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_annihilator hbeta,
    fzzCigarParityDilatedFullHermitianRieszAnnihilator_universalDetector hbeta⟩

end

end RHTower
