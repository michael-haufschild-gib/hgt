import GaloisForLFunctions.RHTower.ThetaCuspHawkingSelfDualEinsteinDilationCarrier

/-!
# General unequal-charge Plebanski Mellin vertex

The self-dual Einstein--AdS4 plane-wave vertex has an exact unequal-exponent, unequal-charge
Mellin kernel. The existing equal-charge computation does not determine that kernel.

For beta exponents `a,b`, charges `h,k`, and curvature `c`, exact Gamma normalization reduces the
full curvature-corrected convolution to

`1/2 * ((a*k-b*h)^(2 : ℕ) + a*k^(2 : ℕ) + b*h^(2 : ℕ) - c*(h-k)*(a+b+1)*(a*k-b*h))`.

This evaluates the universal Plebanski Mellin kernel. It does not identify the exact BM `++`
hypergeometric Green response with a single Mellin monomial, does not extend the chiral Plebanski
restriction to the full `++-` Einstein source, and does not assume a target Xi coefficient or the
remaining augmented response projection.

`[NEW] [PLEBANSKI] [UNEQUAL CHARGES] [THIRD-ORDER SOURCE] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Unequal-exponent Mellin convolution of the same-charge Plebanski vertex. -/
def ads4SelfDualMixedMellinPolynomialMoment (a b : ℂ) : ℂ :=
  4 * Complex.betaIntegral (a + 2) b -
    4 * Complex.betaIntegral (a + 1) b +
      Complex.betaIntegral a b

theorem ads4SelfDualMixedMellinPolynomialMoment_eq
    {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ads4SelfDualMixedMellinPolynomialMoment a b =
      (((a - b) ^ (2 : ℕ) + a + b) / ((a + b) * (a + b + 1))) *
        Complex.betaIntegral a b := by
  have ha1 : 0 < (a + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hab0 : a + b ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hab10 : a + b + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [ads4SelfDualMixedMellinPolynomialMoment,
    show a + 2 = (a + 1) + 1 by ring,
    betaIntegral_add_one_left (a := a + 1) (b := b) ha1 hb,
    betaIntegral_add_one_left (a := a) (b := b) ha hb]
  rw [show a + 1 + b = a + b + 1 by ring]
  field_simp [hab0, hab10]
  ring

/-- Gamma-normalized unequal-exponent Plebanski source coefficient. -/
def ads4SelfDualNormalizedMixedMellinSourceCoefficient
    (a b h : ℂ) : ℂ :=
  (h ^ (2 : ℕ) / 2) * ads4SelfDualMixedMellinPolynomialMoment a b *
    Complex.Gamma (a + b + 2) /
      (Complex.Gamma a * Complex.Gamma b)

theorem ads4SelfDualNormalizedMixedMellinSourceCoefficient_eq
    {a b h : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ads4SelfDualNormalizedMixedMellinSourceCoefficient a b h =
      (h ^ (2 : ℕ) / 2) * ((a - b) ^ (2 : ℕ) + a + b) := by
  have habpos : 0 < (a + b).re := by
    simp only [Complex.add_re]
    linarith
  have hab0 : a + b ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hab10 : a + b + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hga : Complex.Gamma a ≠ 0 := complexGamma_ne_zero_of_re_pos ha
  have hgb : Complex.Gamma b ≠ 0 := complexGamma_ne_zero_of_re_pos hb
  have hgab : Complex.Gamma (a + b) ≠ 0 :=
    complexGamma_ne_zero_of_re_pos habpos
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  rw [ads4SelfDualNormalizedMixedMellinSourceCoefficient,
    ads4SelfDualMixedMellinPolynomialMoment_eq ha hb,
    show a + b + 2 = (a + b + 1) + 1 by ring,
    Complex.Gamma_add_one (a + b + 1) hab10,
    Complex.Gamma_add_one (a + b) hab0]
  field_simp [hga, hgb, hgab, hab0, hab10]
  rw [show
    h ^ (2 : ℕ) * ((a - b) ^ (2 : ℕ) + a + b) * Complex.Gamma a * Complex.Gamma b =
      (h ^ (2 : ℕ) * ((a - b) ^ (2 : ℕ) + a + b)) *
        (Complex.Gamma a * Complex.Gamma b) by ring,
    hbeta]
  ring

theorem ads4SelfDualNormalizedMixedMellinSourceCoefficient_self
    {a h : ℂ} (ha : 0 < a.re) :
    ads4SelfDualNormalizedMixedMellinSourceCoefficient a a h = a * h ^ (2 : ℕ) := by
  rw [ads4SelfDualNormalizedMixedMellinSourceCoefficient_eq ha ha]
  ring

/-- Closed numerator of the unequal-charge, curvature-corrected Plebanski Mellin vertex. -/
def ads4SelfDualGeneralMellinVertexNumerator
    (curvature a b h k : ℂ) : ℂ :=
  (a * k - b * h) ^ (2 : ℕ) + a * k ^ (2 : ℕ) + b * h ^ (2 : ℕ) -
    curvature * (h - k) * (a + b + 1) * (a * k - b * h)

/-- Unequal-exponent, unequal-charge Mellin convolution of the full AdS Plebanski vertex. -/
def ads4SelfDualGeneralMellinVertexMoment
    (curvature a b h k : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    ((h + k) ^ (2 : ℕ) * Complex.betaIntegral (a + 2) b +
      (-2 * h * (h + k) - curvature * (h - k) * (h + k)) *
        Complex.betaIntegral (a + 1) b +
      (h ^ (2 : ℕ) + curvature * (h - k) * h) * Complex.betaIntegral a b)

theorem ads4SelfDualGeneralMellinVertexMoment_eq
    {curvature a b h k : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ads4SelfDualGeneralMellinVertexMoment curvature a b h k =
      ((1 / 2 : ℂ) *
        ads4SelfDualGeneralMellinVertexNumerator curvature a b h k /
          ((a + b) * (a + b + 1))) * Complex.betaIntegral a b := by
  have ha1 : 0 < (a + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hab0 : a + b ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hab10 : a + b + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  rw [ads4SelfDualGeneralMellinVertexMoment,
    show a + 2 = (a + 1) + 1 by ring,
    betaIntegral_add_one_left (a := a + 1) (b := b) ha1 hb,
    betaIntegral_add_one_left (a := a) (b := b) ha hb]
  rw [show a + 1 + b = a + b + 1 by ring]
  unfold ads4SelfDualGeneralMellinVertexNumerator
  field_simp [hab0, hab10]
  ring

/-- Gamma-normalized full AdS Plebanski source coefficient for arbitrary positive-real Mellin
exponents and arbitrary transverse charges. -/
def ads4SelfDualNormalizedGeneralMellinVertexCoefficient
    (curvature a b h k : ℂ) : ℂ :=
  ads4SelfDualGeneralMellinVertexMoment curvature a b h k *
    Complex.Gamma (a + b + 2) /
      (Complex.Gamma a * Complex.Gamma b)

theorem ads4SelfDualNormalizedGeneralMellinVertexCoefficient_eq
    {curvature a b h k : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ads4SelfDualNormalizedGeneralMellinVertexCoefficient curvature a b h k =
      (1 / 2 : ℂ) *
        ads4SelfDualGeneralMellinVertexNumerator curvature a b h k := by
  have habpos : 0 < (a + b).re := by
    simp only [Complex.add_re]
    linarith
  have hab0 : a + b ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hab10 : a + b + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hga : Complex.Gamma a ≠ 0 := complexGamma_ne_zero_of_re_pos ha
  have hgb : Complex.Gamma b ≠ 0 := complexGamma_ne_zero_of_re_pos hb
  have hgab : Complex.Gamma (a + b) ≠ 0 :=
    complexGamma_ne_zero_of_re_pos habpos
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  rw [ads4SelfDualNormalizedGeneralMellinVertexCoefficient,
    ads4SelfDualGeneralMellinVertexMoment_eq ha hb,
    show a + b + 2 = (a + b + 1) + 1 by ring,
    Complex.Gamma_add_one (a + b + 1) hab10,
    Complex.Gamma_add_one (a + b) hab0]
  field_simp [hga, hgb, hgab, hab0, hab10]
  rw [show
    ads4SelfDualGeneralMellinVertexNumerator curvature a b h k *
        Complex.Gamma a * Complex.Gamma b =
      ads4SelfDualGeneralMellinVertexNumerator curvature a b h k *
        (Complex.Gamma a * Complex.Gamma b) by ring,
    hbeta]
  ring

theorem ads4SelfDualNormalizedGeneralMellinVertexCoefficient_sameCharge
    {curvature a b h : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ads4SelfDualNormalizedGeneralMellinVertexCoefficient curvature a b h h =
      (h ^ (2 : ℕ) / 2) * ((a - b) ^ (2 : ℕ) + a + b) := by
  rw [ads4SelfDualNormalizedGeneralMellinVertexCoefficient_eq ha hb]
  unfold ads4SelfDualGeneralMellinVertexNumerator
  ring

end

end RHTower
