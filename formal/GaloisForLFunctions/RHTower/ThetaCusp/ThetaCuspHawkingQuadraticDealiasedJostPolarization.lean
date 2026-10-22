import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMECrossBranchTeukolskyResidue

/-!
# Quadratically dealiased Hawking--Teukolsky Jost polarization

The raw Birmingham--Mokhtari channel carries half the completed-theta weight:
its angular momentum is centered at the wrong reflection point for the Xi
functional equation.  The affine radial lift
`L(z) = 2 z - i/2` realizes the doubled Weyl weight inside the same exact
hypergeometric scattering problem.  It sends angular momentum to `z`,
angular eigenvalue to `1/4 + z^(2 : ℕ)`, and the physical optical shadow to
`z ↦ -z`.

At each Xi divisor copy the lifted full boundary determinant has a simple
negative-branch QNM zero, while the unit chiral AIME response has the
corresponding scattering pole.  Multiplication of the two functional-equation
mirror residues cancels every Gamma factor and leaves
`-(576/pi) P(i z)`, where

`P(x) = (x^(2 : ℕ) - 1/4)/(x (9/4 - x^(2 : ℕ))^(2 : ℕ)) cot(pi x)`.

Inside the Xi strip, the imaginary part of `P` is nonzero at every tilted
point and vanishes exactly on the critical line.  This is an ordered chiral
Hawking/Teukolsky polarization; Schwarz closure erases it by conjugation.

Second-order Einstein--Teukolsky frequency addition cannot reach this lifted
QNM channel. The first same-sector charge-compatible resonance instead occurs
on the sixth-order Hawking charge-decay ladder.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

def d4ThetaCuspHawkingQuadraticDealiasedLift (z : ℂ) : ℂ := 2 * z - Complex.I / 2

def d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus (z : ℂ) : ℂ :=
  d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus 0 (d4ThetaCuspHawkingQuadraticDealiasedLift z)

lemma d4ThetaCuspHawkingQuadraticDealiased_momentum (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum (d4ThetaCuspHawkingQuadraticDealiasedLift z) = z := by
  unfold thetaCuspHawkingTopologicalBlackHoleAngularMomentum d4ThetaCuspHawkingQuadraticDealiasedLift
  ring

lemma d4ThetaCuspHawkingQuadraticDealiased_shadow (z : ℂ) :
    thetaCuspHawkingOpticalCuspShadow (d4ThetaCuspHawkingQuadraticDealiasedLift z) = d4ThetaCuspHawkingQuadraticDealiasedLift (-z) := by
  unfold thetaCuspHawkingOpticalCuspShadow d4ThetaCuspHawkingQuadraticDealiasedLift
  ring

lemma d4ThetaCuspHawkingQuadraticDealiased_q (z : ℂ) :
    d4ThetaTeukolskyAngularQ (d4ThetaCuspHawkingQuadraticDealiasedLift z) = 1 / 4 + z ^ (2 : ℕ) := by
  unfold d4ThetaTeukolskyAngularQ
    thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue
  rw [d4ThetaCuspHawkingQuadraticDealiased_momentum]

/-- The lifted channel is an actual zero of the full Birmingham--Mokhtari boundary Jost
determinant at its negative fundamental QNM. -/
theorem d4ThetaCuspHawkingQuadraticDealiased_boundaryJost_qnmMinus_eq_zero (z : ℂ) :
    d4GravitationalHypergeometricBoundaryJost
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (d4ThetaCuspHawkingQuadraticDealiasedLift z))
        (d4ThetaCuspHawkingQuadraticDealiasedLift z) = 0 := by
  unfold d4GravitationalHypergeometricBoundaryJost
    thetaCuspHawkingHypergeometricPhysicalBoundaryJost
    thetaCuspHawkingHypergeometricJost
  rw [thetaCuspHawkingHypergeometricJostMinus_qnm_zero]
  ring

lemma d4ThetaCuspHawkingQuadraticDealiased_radialC_qnmMinus (z : ℂ) :
    thetaCuspHawkingHypergeometricRadialC
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (d4ThetaCuspHawkingQuadraticDealiasedLift z)) =
      Complex.I * z - 1 / 2 := by
  unfold thetaCuspHawkingHypergeometricRadialC
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
  rw [d4ThetaCuspHawkingQuadraticDealiased_momentum]
  norm_num
  calc
    1 - Complex.I * (-z - Complex.I * (3 / 2)) =
        1 + Complex.I * z + (Complex.I * Complex.I) * (3 / 2) := by ring
    _ = Complex.I * z - 1 / 2 := by
      rw [Complex.I_mul_I]
      ring

/-- The closed expression `d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus` is the derivative of the actual full boundary determinant,
not a formal normalization. -/
theorem d4ThetaCuspHawkingQuadraticDealiased_boundaryJost_hasDerivAt (z : ℂ)
    (hpole : ∀ m : ℕ, Complex.I * z - 1 / 2 ≠ -(m : ℂ)) :
    HasDerivAt
      (fun omega : ℂ =>
        d4GravitationalHypergeometricBoundaryJost omega (d4ThetaCuspHawkingQuadraticDealiasedLift z))
      (d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus z)
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (d4ThetaCuspHawkingQuadraticDealiasedLift z)) := by
  let zl := d4ThetaCuspHawkingQuadraticDealiasedLift z
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 zl
  let pref : ℂ → ℂ := fun w =>
    Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) *
      Complex.Gamma (1 / 2 : ℂ)
  let jPlus : ℂ → ℂ := fun w =>
    thetaCuspHawkingHypergeometricJostPlus w zl
  let jMinus : ℂ → ℂ := fun w =>
    thetaCuspHawkingHypergeometricJostMinus w zl
  have hprefAna : AnalyticAt ℂ pref omega := by
    exact (thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
      (by
        intro m
        change thetaCuspHawkingHypergeometricRadialC
          (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (d4ThetaCuspHawkingQuadraticDealiasedLift z)) ≠ -(m : ℂ)
        rw [d4ThetaCuspHawkingQuadraticDealiased_radialC_qnmMinus]
        exact hpole m)).mul analyticAt_const
  have hpref : HasDerivAt pref (deriv pref omega) omega :=
    hprefAna.differentiableAt.hasDerivAt
  have hplus : HasDerivAt jPlus (deriv jPlus omega) omega :=
    (thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega zl).differentiableAt.hasDerivAt
  have hminus :
      HasDerivAt jMinus (teukolskyNormalizedJostOmegaDerivative 0) omega := by
    simpa [jMinus, omega, zl, teukolskyNormalizedJostOmegaDerivative] using
      thetaCuspHawkingHypergeometricHasDerivAt_jostMinus_qnm 0 zl
  have hminusZero : jMinus omega = 0 := by
    simp [jMinus, omega, thetaCuspHawkingHypergeometricJostMinus_qnm_zero]
  have hprod := (hpref.mul hplus).mul hminus
  have hfun :
      (fun w : ℂ => d4GravitationalHypergeometricBoundaryJost w (d4ThetaCuspHawkingQuadraticDealiasedLift z)) =
        pref * jPlus * jMinus := by
    funext w
    simp [d4GravitationalHypergeometricBoundaryJost,
      thetaCuspHawkingHypergeometricPhysicalBoundaryJost,
      thetaCuspHawkingHypergeometricJost, pref, jPlus, jMinus, zl]
    ring
  rw [hfun]
  exact hprod.congr_deriv (by
    simp [d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus, d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus,
      pref, jPlus, omega, zl, hminusZero])

lemma d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus_eq (z : ℂ) :
    d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus z =
      Complex.Gamma (Complex.I * z - 1 / 2) * Complex.Gamma (1 / 2 : ℂ) *
        GaloisForLFunctions.reciprocalGammaEntire (Complex.I * z) *
          (-(Complex.I / 2)) := by
  unfold d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingHypergeometricRadialC
    thetaCuspHawkingHypergeometricJostPlus
    thetaCuspHawkingHypergeometricRadialA
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
    teukolskyNormalizedJostOmegaDerivative
  rw [d4ThetaCuspHawkingQuadraticDealiased_momentum]
  norm_num
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4ThetaCuspHawkingQuadraticDealiased_gamma_den_pair (x : ℂ) (hx : x ≠ 0)
    (_hsin : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    Complex.Gamma x * Complex.Gamma (-x) =
      -(Real.pi : ℂ) / (x * Complex.sin ((Real.pi : ℂ) * x)) := by
  have hreflect := Complex.Gamma_mul_Gamma_one_sub x
  have hrec := Complex.Gamma_add_one (-x) (neg_ne_zero.mpr hx)
  have hrec' : Complex.Gamma (1 - x) = -x * Complex.Gamma (-x) := by
    simpa [sub_eq_add_neg, add_comm] using hrec
  rw [hrec'] at hreflect
  field_simp [hx, _hsin] at hreflect ⊢
  linear_combination -hreflect

lemma d4ThetaCuspHawkingQuadraticDealiased_gamma_num_pair (x : ℂ)
    (hxmh : x - 1 / 2 ≠ 0) (hxph : x + 1 / 2 ≠ 0)
    (hcos : Complex.cos ((Real.pi : ℂ) * x) ≠ 0) :
    Complex.Gamma (x - 1 / 2) * Complex.Gamma (-x - 1 / 2) =
      -(Real.pi : ℂ) /
        ((x ^ (2 : ℕ) - 1 / 4) * Complex.cos ((Real.pi : ℂ) * x)) := by
  let y : ℂ := x - 1 / 2
  have hreflect := Complex.Gamma_mul_Gamma_one_sub y
  have h₁ : -x - 1 / 2 ≠ 0 := by
    intro h
    apply hxph
    linear_combination -h
  have h₂ : -x + 1 / 2 ≠ 0 := by
    intro h
    apply hxmh
    linear_combination -h
  have hrec₁ := Complex.Gamma_add_one (-x - 1 / 2) h₁
  have hrec₂ := Complex.Gamma_add_one (-x + 1 / 2) h₂
  have hshift : Complex.Gamma (1 - y) =
      (x ^ (2 : ℕ) - 1 / 4) * Complex.Gamma (-x - 1 / 2) := by
    rw [show 1 - y = (-x + 1 / 2) + 1 by simp [y]; ring, hrec₂]
    rw [show -x + 1 / 2 = (-x - 1 / 2) + 1 by ring, hrec₁]
    ring
  rw [hshift] at hreflect
  have hsin : Complex.sin ((Real.pi : ℂ) * y) =
      -Complex.cos ((Real.pi : ℂ) * x) := by
    rw [show (Real.pi : ℂ) * y = (Real.pi : ℂ) * x - (Real.pi : ℂ) / 2 by
      simp [y]; ring]
    rw [Complex.sin_sub]
    rw [Complex.sin_pi_div_two, Complex.cos_pi_div_two]
    ring
  rw [hsin] at hreflect
  have hquad : x ^ (2 : ℕ) - 1 / 4 ≠ 0 := by
    rw [show x ^ (2 : ℕ) - 1 / 4 = (x - 1 / 2) * (x + 1 / 2) by ring]
    exact mul_ne_zero hxmh hxph
  have hreflect' :
      Complex.Gamma (x - 1 / 2) *
          ((x ^ (2 : ℕ) - 1 / 4) * Complex.Gamma (-x - 1 / 2)) =
        -(Real.pi : ℂ) / Complex.cos ((Real.pi : ℂ) * x) := by
    simpa [y, div_neg, neg_div] using hreflect
  apply (eq_div_iff (mul_ne_zero hquad hcos)).2
  calc
    (Complex.Gamma (x - 1 / 2) * Complex.Gamma (-x - 1 / 2)) *
          ((x ^ (2 : ℕ) - 1 / 4) * Complex.cos ((Real.pi : ℂ) * x)) =
        (Complex.Gamma (x - 1 / 2) *
          ((x ^ (2 : ℕ) - 1 / 4) * Complex.Gamma (-x - 1 / 2))) *
            Complex.cos ((Real.pi : ℂ) * x) := by ring
    _ = (-(Real.pi : ℂ) / Complex.cos ((Real.pi : ℂ) * x)) *
          Complex.cos ((Real.pi : ℂ) * x) := by rw [hreflect']
    _ = -(Real.pi : ℂ) := div_mul_cancel₀ _ hcos

lemma d4ThetaCuspHawkingQuadraticDealiased_gamma_half_sq :
    Complex.Gamma (1 / 2 : ℂ) * Complex.Gamma (1 / 2 : ℂ) =
      (Real.pi : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1 / 2 : ℂ)
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring,
    show (Real.pi : ℂ) * (1 / 2) = (Real.pi : ℂ) / 2 by ring,
    Complex.sin_pi_div_two, div_one] at h
  exact h

lemma d4ThetaCuspHawkingQuadraticDealiased_gamma_ratio_pair (x : ℂ)
    (hx : x ≠ 0) (hxmh : x - 1 / 2 ≠ 0) (hxph : x + 1 / 2 ≠ 0)
    (hsin : Complex.sin ((Real.pi : ℂ) * x) ≠ 0)
    (hcos : Complex.cos ((Real.pi : ℂ) * x) ≠ 0) :
    (Complex.Gamma (x - 1 / 2) * (Complex.Gamma x)⁻¹) *
        (Complex.Gamma (-x - 1 / 2) * (Complex.Gamma (-x))⁻¹) =
      x * Complex.tan ((Real.pi : ℂ) * x) / (x ^ (2 : ℕ) - 1 / 4) := by
  have hden := d4ThetaCuspHawkingQuadraticDealiased_gamma_den_pair x hx hsin
  have hnum := d4ThetaCuspHawkingQuadraticDealiased_gamma_num_pair x hxmh hxph hcos
  have hquad : x ^ (2 : ℕ) - 1 / 4 ≠ 0 := by
    rw [show x ^ (2 : ℕ) - 1 / 4 = (x - 1 / 2) * (x + 1 / 2) by ring]
    exact mul_ne_zero hxmh hxph
  calc
    (Complex.Gamma (x - 1 / 2) * (Complex.Gamma x)⁻¹) *
          (Complex.Gamma (-x - 1 / 2) * (Complex.Gamma (-x))⁻¹) =
        (Complex.Gamma (x - 1 / 2) * Complex.Gamma (-x - 1 / 2)) *
          ((Complex.Gamma x)⁻¹ * (Complex.Gamma (-x))⁻¹) := by ring
    _ = (Complex.Gamma (x - 1 / 2) * Complex.Gamma (-x - 1 / 2)) *
          (Complex.Gamma x * Complex.Gamma (-x))⁻¹ := by rw [mul_inv]
    _ = x * Complex.tan ((Real.pi : ℂ) * x) / (x ^ (2 : ℕ) - 1 / 4) := by
      rw [hnum, hden, Complex.tan_eq_sin_div_cos]
      field_simp [hx, hsin, hcos, hquad, Real.pi_ne_zero]

theorem d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus_mul_neg (z : ℂ)
    (hx : Complex.I * z ≠ 0)
    (hxmh : Complex.I * z - 1 / 2 ≠ 0)
    (hxph : Complex.I * z + 1 / 2 ≠ 0)
    (hsin : Complex.sin ((Real.pi : ℂ) * (Complex.I * z)) ≠ 0)
    (hcos : Complex.cos ((Real.pi : ℂ) * (Complex.I * z)) ≠ 0) :
    d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus z * d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus (-z) =
      (-(Real.pi : ℂ) / 4) *
        ((Complex.I * z) * Complex.tan ((Real.pi : ℂ) * (Complex.I * z)) /
          ((Complex.I * z) ^ (2 : ℕ) - 1 / 4)) := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus_eq, d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus_eq]
  have hneg : Complex.I * (-z) = -(Complex.I * z) := by ring
  rw [hneg]
  unfold GaloisForLFunctions.reciprocalGammaEntire
  have hratio := d4ThetaCuspHawkingQuadraticDealiased_gamma_ratio_pair (Complex.I * z) hx hxmh hxph hsin hcos
  calc
    (Complex.Gamma (Complex.I * z - 1 / 2) * Complex.Gamma (1 / 2) *
          (Complex.Gamma (Complex.I * z))⁻¹ * (-(Complex.I / 2))) *
        (Complex.Gamma (-(Complex.I * z) - 1 / 2) * Complex.Gamma (1 / 2) *
          (Complex.Gamma (-(Complex.I * z)))⁻¹ * (-(Complex.I / 2))) =
      ((Complex.Gamma (Complex.I * z - 1 / 2) *
          (Complex.Gamma (Complex.I * z))⁻¹) *
        (Complex.Gamma (-(Complex.I * z) - 1 / 2) *
          (Complex.Gamma (-(Complex.I * z)))⁻¹)) *
        (Complex.Gamma (1 / 2) * Complex.Gamma (1 / 2)) *
          ((-(Complex.I / 2)) * (-(Complex.I / 2))) := by ring
    _ = ((Complex.I * z) * Complex.tan ((Real.pi : ℂ) * (Complex.I * z)) /
          ((Complex.I * z) ^ (2 : ℕ) - 1 / 4)) * (Real.pi : ℂ) *
            ((-(Complex.I / 2)) * (-(Complex.I / 2))) := by
      rw [hratio, d4ThetaCuspHawkingQuadraticDealiased_gamma_half_sq]
    _ = (-(Real.pi : ℂ) / 4) *
        ((Complex.I * z) * Complex.tan ((Real.pi : ℂ) * (Complex.I * z)) /
          ((Complex.I * z) ^ (2 : ℕ) - 1 / 4)) := by
      rw [show (-(Complex.I / 2)) * (-(Complex.I / 2)) = (-1 / 4 : ℂ) by
        ring_nf
        rw [Complex.I_sq]
        norm_num]
      ring

lemma d4ThetaCuspHawkingQuadraticDealiased_sin_eq (a b : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)) =
      (Real.sin (Real.pi * a) * Real.cosh (Real.pi * b) : ℝ) +
        (Real.cos (Real.pi * a) * Real.sinh (Real.pi * b) : ℝ) * Complex.I := by
  rw [show (Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I) =
      ((Real.pi * a : ℝ) : ℂ) + ((Real.pi * b : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  have hsinA : Complex.sin (((Real.pi * a : ℝ) : ℂ)) =
      (Real.sin (Real.pi * a) : ℂ) := (Complex.ofReal_sin _).symm
  have hcosA : Complex.cos (((Real.pi * a : ℝ) : ℂ)) =
      (Real.cos (Real.pi * a) : ℂ) := (Complex.ofReal_cos _).symm
  have hsinhB : Complex.sinh (((Real.pi * b : ℝ) : ℂ)) =
      (Real.sinh (Real.pi * b) : ℂ) := (Complex.ofReal_sinh _).symm
  have hcoshB : Complex.cosh (((Real.pi * b : ℝ) : ℂ)) =
      (Real.cosh (Real.pi * b) : ℂ) := (Complex.ofReal_cosh _).symm
  rw [Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I]
  rw [hsinA, hcosA, hsinhB, hcoshB]
  push_cast
  ring

lemma d4ThetaCuspHawkingQuadraticDealiased_cos_eq (a b : ℝ) :
    Complex.cos ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)) =
      (Real.cos (Real.pi * a) * Real.cosh (Real.pi * b) : ℝ) -
        (Real.sin (Real.pi * a) * Real.sinh (Real.pi * b) : ℝ) * Complex.I := by
  rw [show (Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I) =
      ((Real.pi * a : ℝ) : ℂ) + ((Real.pi * b : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  have hsinA : Complex.sin (((Real.pi * a : ℝ) : ℂ)) =
      (Real.sin (Real.pi * a) : ℂ) := (Complex.ofReal_sin _).symm
  have hcosA : Complex.cos (((Real.pi * a : ℝ) : ℂ)) =
      (Real.cos (Real.pi * a) : ℂ) := (Complex.ofReal_cos _).symm
  have hsinhB : Complex.sinh (((Real.pi * b : ℝ) : ℂ)) =
      (Real.sinh (Real.pi * b) : ℂ) := (Complex.ofReal_sinh _).symm
  have hcoshB : Complex.cosh (((Real.pi * b : ℝ) : ℂ)) =
      (Real.cosh (Real.pi * b) : ℂ) := (Complex.ofReal_cosh _).symm
  rw [Complex.cos_add, Complex.sin_mul_I, Complex.cos_mul_I]
  rw [hsinA, hcosA, hsinhB, hcoshB]
  push_cast
  ring

lemma d4ThetaCuspHawkingQuadraticDealiased_sin_re (a b : ℝ) :
    (Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))).re =
      Real.sin (Real.pi * a) * Real.cosh (Real.pi * b) := by
  have h := congrArg Complex.re (d4ThetaCuspHawkingQuadraticDealiased_sin_eq a b)
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, mul_one] using h

lemma d4ThetaCuspHawkingQuadraticDealiased_sin_im (a b : ℝ) :
    (Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))).im =
      Real.cos (Real.pi * a) * Real.sinh (Real.pi * b) := by
  have h := congrArg Complex.im (d4ThetaCuspHawkingQuadraticDealiased_sin_eq a b)
  simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    add_zero, zero_add, mul_one] using h

lemma d4ThetaCuspHawkingQuadraticDealiased_cos_re (a b : ℝ) :
    (Complex.cos ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))).re =
      Real.cos (Real.pi * a) * Real.cosh (Real.pi * b) := by
  have h := congrArg Complex.re (d4ThetaCuspHawkingQuadraticDealiased_cos_eq a b)
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, mul_one] using h

lemma d4ThetaCuspHawkingQuadraticDealiased_cos_im (a b : ℝ) :
    (Complex.cos ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))).im =
      -Real.sin (Real.pi * a) * Real.sinh (Real.pi * b) := by
  have h := congrArg Complex.im (d4ThetaCuspHawkingQuadraticDealiased_cos_eq a b)
  simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, zero_sub, add_zero, zero_add, mul_one, neg_mul] using h

lemma d4ThetaCuspHawkingQuadraticDealiased_cot_re_pos {a b : ℝ} (ha0 : 0 < a) (hah : a < 1 / 2)
    (hb : 0 < b) :
    0 < (Complex.cot
      ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))).re := by
  have hpa0 : 0 < Real.pi * a := mul_pos Real.pi_pos ha0
  have hpah : Real.pi * a < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsinA : 0 < Real.sin (Real.pi * a) :=
    Real.sin_pos_of_pos_of_lt_pi hpa0 (by nlinarith [Real.pi_pos])
  have hcosA : 0 < Real.cos (Real.pi * a) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hcoshB : 0 < Real.cosh (Real.pi * b) := Real.cosh_pos _
  have hsinhB : 0 < Real.sinh (Real.pi * b) :=
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hb)
  have hsinRe : 0 <
      (Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))).re := by
    rw [d4ThetaCuspHawkingQuadraticDealiased_sin_re]
    positivity
  have hsinNe :
      Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hnorm : 0 < Complex.normSq
      (Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))) :=
    Complex.normSq_pos.mpr hsinNe
  rw [Complex.cot_eq_cos_div_sin, Complex.div_re,
    d4ThetaCuspHawkingQuadraticDealiased_cos_re, d4ThetaCuspHawkingQuadraticDealiased_cos_im, d4ThetaCuspHawkingQuadraticDealiased_sin_re, d4ThetaCuspHawkingQuadraticDealiased_sin_im]
  rw [← add_div]
  apply div_pos _ hnorm
  have hhyp := Real.cosh_sq_sub_sinh_sq (Real.pi * b)
  calc
    Real.cos (Real.pi * a) * Real.cosh (Real.pi * b) *
          (Real.sin (Real.pi * a) * Real.cosh (Real.pi * b)) +
        (-Real.sin (Real.pi * a) * Real.sinh (Real.pi * b)) *
          (Real.cos (Real.pi * a) * Real.sinh (Real.pi * b)) =
      Real.sin (Real.pi * a) * Real.cos (Real.pi * a) *
        (Real.cosh (Real.pi * b) ^ (2 : ℕ) - Real.sinh (Real.pi * b) ^ (2 : ℕ)) := by ring
    _ = Real.sin (Real.pi * a) * Real.cos (Real.pi * a) := by rw [hhyp]; ring
    _ > 0 := mul_pos hsinA hcosA

lemma d4ThetaCuspHawkingQuadraticDealiased_cot_im_neg {a b : ℝ} (ha0 : 0 < a) (hah : a < 1 / 2)
    (hb : 0 < b) :
    (Complex.cot
      ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))).im < 0 := by
  have hpa0 : 0 < Real.pi * a := mul_pos Real.pi_pos ha0
  have hpah : Real.pi * a < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsinA : 0 < Real.sin (Real.pi * a) :=
    Real.sin_pos_of_pos_of_lt_pi hpa0 (by nlinarith [Real.pi_pos])
  have hcosA : 0 < Real.cos (Real.pi * a) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hcoshB : 0 < Real.cosh (Real.pi * b) := Real.cosh_pos _
  have hsinhB : 0 < Real.sinh (Real.pi * b) :=
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hb)
  have hsinRe : 0 <
      (Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))).re := by
    rw [d4ThetaCuspHawkingQuadraticDealiased_sin_re]
    positivity
  have hsinNe :
      Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hnorm : 0 < Complex.normSq
      (Complex.sin ((Real.pi : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))) :=
    Complex.normSq_pos.mpr hsinNe
  rw [Complex.cot_eq_cos_div_sin, Complex.div_im,
    d4ThetaCuspHawkingQuadraticDealiased_cos_re, d4ThetaCuspHawkingQuadraticDealiased_cos_im, d4ThetaCuspHawkingQuadraticDealiased_sin_re, d4ThetaCuspHawkingQuadraticDealiased_sin_im]
  rw [← sub_div]
  apply div_neg_of_neg_of_pos _ hnorm
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * a)
  calc
    (-Real.sin (Real.pi * a) * Real.sinh (Real.pi * b)) *
          (Real.sin (Real.pi * a) * Real.cosh (Real.pi * b)) -
        Real.cos (Real.pi * a) * Real.cosh (Real.pi * b) *
          (Real.cos (Real.pi * a) * Real.sinh (Real.pi * b)) =
      -(Real.sinh (Real.pi * b) * Real.cosh (Real.pi * b)) *
        (Real.sin (Real.pi * a) ^ (2 : ℕ) + Real.cos (Real.pi * a) ^ (2 : ℕ)) := by ring
    _ = -(Real.sinh (Real.pi * b) * Real.cosh (Real.pi * b)) := by
      rw [htrig]
      ring
    _ < 0 := neg_neg_of_pos (mul_pos hsinhB hcoshB)

def d4ThetaCuspHawkingQuadraticDealiasedRational (x : ℂ) : ℂ :=
  (x ^ (2 : ℕ) - 1 / 4) / (x * (9 / 4 - x ^ (2 : ℕ)) ^ (2 : ℕ))

def d4ThetaCuspHawkingQuadraticDealiasedRationalReNumerator (a b : ℝ) : ℝ :=
  (-3) * (b ^ (2 : ℕ)) ^ (3 : ℕ) - (5 * a ^ (2 : ℕ) + 23 / 4) * (b ^ (2 : ℕ)) ^ (2 : ℕ) +
    (1 / 4 - a ^ (2 : ℕ)) * (a ^ (2 : ℕ) + 27 / 4) * b ^ (2 : ℕ) -
      (1 / 4 - a ^ (2 : ℕ)) * (9 / 4 - a ^ (2 : ℕ)) ^ (2 : ℕ)

def d4ThetaCuspHawkingQuadraticDealiasedRationalImNumerator (a b : ℝ) : ℝ :=
  (b ^ (2 : ℕ)) ^ (3 : ℕ) + (-a ^ (2 : ℕ) + 19 / 4) * (b ^ (2 : ℕ)) ^ (2 : ℕ) +
    (-5 * (a ^ (2 : ℕ)) ^ (2 : ℕ) + 13 / 2 * a ^ (2 : ℕ) + 99 / 16) * b ^ (2 : ℕ) +
      ((-3) * (a ^ (2 : ℕ)) ^ (3 : ℕ) + 23 / 4 * (a ^ (2 : ℕ)) ^ (2 : ℕ) +
        27 / 16 * a ^ (2 : ℕ) + 81 / 64)

lemma d4ThetaCuspHawkingQuadraticDealiasedRational_re_eq (a b : ℝ) :
    (d4ThetaCuspHawkingQuadraticDealiasedRational ((a : ℂ) + (b : ℂ) * Complex.I)).re =
      (a * d4ThetaCuspHawkingQuadraticDealiasedRationalReNumerator a b) /
        Complex.normSq (((a : ℂ) + (b : ℂ) * Complex.I) *
          (9 / 4 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedRational, Complex.div_re]
  rw [← add_div]
  congr 1
  · simp [d4ThetaCuspHawkingQuadraticDealiasedRationalReNumerator, pow_two,
      Complex.mul_re, Complex.mul_im]
    ring

lemma d4ThetaCuspHawkingQuadraticDealiasedRational_im_eq (a b : ℝ) :
    (d4ThetaCuspHawkingQuadraticDealiasedRational ((a : ℂ) + (b : ℂ) * Complex.I)).im =
      (b * d4ThetaCuspHawkingQuadraticDealiasedRationalImNumerator a b) /
        Complex.normSq (((a : ℂ) + (b : ℂ) * Complex.I) *
          (9 / 4 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedRational, Complex.div_im]
  rw [← sub_div]
  congr 1
  · simp [d4ThetaCuspHawkingQuadraticDealiasedRationalImNumerator, pow_two,
      Complex.mul_re, Complex.mul_im]
    ring

lemma d4ThetaCuspHawkingQuadraticDealiasedRationalReNumerator_neg {a b : ℝ}
    (ha0 : 0 < a) (hah : a < 1 / 2) (hb : 0 < b) :
    d4ThetaCuspHawkingQuadraticDealiasedRationalReNumerator a b < 0 := by
  let u := a ^ (2 : ℕ)
  let v := b ^ (2 : ℕ)
  have hu0 : 0 ≤ u := sq_nonneg a
  have huh : u < 1 / 4 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have hv0 : 0 < v := sq_pos_of_pos hb
  let A := 5 * u + 23 / 4
  let B := (1 / 4 - u) * (u + 27 / 4)
  let C := (1 / 4 - u) * (9 / 4 - u) ^ (2 : ℕ)
  have hA : 0 < A := by dsimp [A]; nlinarith
  have hd : 0 < 1 / 4 - u := by linarith
  have hup : 0 < u + 27 / 4 := by nlinarith
  have hupp : u + 27 / 4 < 7 := by linarith
  have hsqUpper : (u + 27 / 4) ^ (2 : ℕ) < 49 := by
    nlinarith [sq_nonneg ((u + 27 / 4) + 7)]
  have hfirst :
      (1 / 4 - u) * (u + 27 / 4) ^ (2 : ℕ) < (49 : ℝ) / 4 := by
    nlinarith [mul_lt_mul_of_pos_right hsqUpper hd]
  have hbase : 2 < 9 / 4 - u := by linarith
  have hbaseSq : 4 < (9 / 4 - u) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg ((9 / 4 - u) + 2)]
  have hAcoarse : 23 / 4 < A := by dsimp [A]; nlinarith
  have hsecond : 92 < 4 * A * (9 / 4 - u) ^ (2 : ℕ) := by
    have hsqPos : 0 < (9 / 4 - u) ^ (2 : ℕ) := by positivity
    have hleft : (23 / 4 : ℝ) * (9 / 4 - u) ^ (2 : ℕ) <
        A * (9 / 4 - u) ^ (2 : ℕ) := mul_lt_mul_of_pos_right hAcoarse hsqPos
    have hright : (23 / 4 : ℝ) * 4 <
        (23 / 4 : ℝ) * (9 / 4 - u) ^ (2 : ℕ) :=
      mul_lt_mul_of_pos_left hbaseSq (by norm_num)
    have hmul : (23 / 4 : ℝ) * 4 < A * (9 / 4 - u) ^ (2 : ℕ) :=
      lt_trans hright hleft
    nlinarith
  have hdisc : B ^ (2 : ℕ) - 4 * A * C < 0 := by
    dsimp [B, C]
    have hfactor :
        ((1 / 4 - u) * (u + 27 / 4)) ^ (2 : ℕ) =
          (1 / 4 - u) ^ (2 : ℕ) * (u + 27 / 4) ^ (2 : ℕ) := by ring
    rw [hfactor]
    have hbracket :
        (1 / 4 - u) * (u + 27 / 4) ^ (2 : ℕ) -
          4 * A * (9 / 4 - u) ^ (2 : ℕ) < 0 := by
      nlinarith
    calc
      (1 / 4 - u) ^ (2 : ℕ) * (u + 27 / 4) ^ (2 : ℕ) -
          4 * A * ((1 / 4 - u) * (9 / 4 - u) ^ (2 : ℕ)) =
        (1 / 4 - u) *
          ((1 / 4 - u) * (u + 27 / 4) ^ (2 : ℕ) -
            4 * A * (9 / 4 - u) ^ (2 : ℕ)) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hd hbracket
  have hquadratic : 0 < A * v ^ (2 : ℕ) - B * v + C := by
    have hsquare : 0 ≤ (2 * A * v - B) ^ (2 : ℕ) := sq_nonneg _
    have hfour : 0 < 4 * A := by positivity
    have hid :
        4 * A * (A * v ^ (2 : ℕ) - B * v + C) =
          (2 * A * v - B) ^ (2 : ℕ) + (4 * A * C - B ^ (2 : ℕ)) := by ring
    nlinarith
  have hv3 : 0 < v ^ (3 : ℕ) := pow_pos hv0 3
  change (-3) * v ^ (3 : ℕ) - A * v ^ (2 : ℕ) + B * v - C < 0
  nlinarith

lemma d4ThetaCuspHawkingQuadraticDealiasedRationalImNumerator_pos {a b : ℝ}
    (ha0 : 0 < a) (hah : a < 1 / 2) (hb : 0 < b) :
    0 < d4ThetaCuspHawkingQuadraticDealiasedRationalImNumerator a b := by
  let u := a ^ (2 : ℕ)
  let v := b ^ (2 : ℕ)
  have hu0 : 0 ≤ u := sq_nonneg a
  have huh : u < 1 / 4 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have huOne : u < 1 := by linarith
  have huSqLe : u ^ (2 : ℕ) ≤ u := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr (le_of_lt huOne))]
  have huCubeLe : u ^ (3 : ℕ) ≤ u := by
    calc
      u ^ (3 : ℕ) = u * u ^ (2 : ℕ) := by ring
      _ ≤ u * u := mul_le_mul_of_nonneg_left huSqLe hu0
      _ = u ^ (2 : ℕ) := by ring
      _ ≤ u := huSqLe
  have hv0 : 0 < v := sq_pos_of_pos hb
  have hcoef0 :
      0 < (-3) * u ^ (3 : ℕ) + 23 / 4 * u ^ (2 : ℕ) + 27 / 16 * u + 81 / 64 := by
    nlinarith
  have hcoef1 : 0 < -5 * u ^ (2 : ℕ) + 13 / 2 * u + 99 / 16 := by
    nlinarith
  have hcoef2 : 0 < -u + 19 / 4 := by linarith
  change 0 < v ^ (3 : ℕ) + (-u + 19 / 4) * v ^ (2 : ℕ) +
    (-5 * u ^ (2 : ℕ) + 13 / 2 * u + 99 / 16) * v +
      ((-3) * u ^ (3 : ℕ) + 23 / 4 * u ^ (2 : ℕ) + 27 / 16 * u + 81 / 64)
  positivity

private lemma d4ThetaCuspHawkingQuadraticDealiasedRational_den_ne_zero {a b : ℝ}
    (ha0 : 0 < a) (hb : 0 < b) :
    ((a : ℂ) + (b : ℂ) * Complex.I) *
        (9 / 4 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ (2 : ℕ)) ^ (2 : ℕ) ≠ 0 := by
  let x : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have hx : x ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [x] at him
    linarith
  have hq : (9 / 4 : ℂ) - x ^ (2 : ℕ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [x, pow_two, Complex.mul_im] at him
    nlinarith
  exact mul_ne_zero hx (pow_ne_zero 2 hq)

lemma d4ThetaCuspHawkingQuadraticDealiasedRational_re_neg {a b : ℝ}
    (ha0 : 0 < a) (hah : a < 1 / 2) (hb : 0 < b) :
    (d4ThetaCuspHawkingQuadraticDealiasedRational ((a : ℂ) + (b : ℂ) * Complex.I)).re < 0 := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedRational_re_eq]
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg ha0
      (d4ThetaCuspHawkingQuadraticDealiasedRationalReNumerator_neg ha0 hah hb)
  · exact Complex.normSq_pos.mpr (d4ThetaCuspHawkingQuadraticDealiasedRational_den_ne_zero ha0 hb)

lemma d4ThetaCuspHawkingQuadraticDealiasedRational_im_pos {a b : ℝ}
    (ha0 : 0 < a) (hah : a < 1 / 2) (hb : 0 < b) :
    0 < (d4ThetaCuspHawkingQuadraticDealiasedRational ((a : ℂ) + (b : ℂ) * Complex.I)).im := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedRational_im_eq]
  apply div_pos
  · exact mul_pos hb (d4ThetaCuspHawkingQuadraticDealiasedRationalImNumerator_pos ha0 hah hb)
  · exact Complex.normSq_pos.mpr (d4ThetaCuspHawkingQuadraticDealiasedRational_den_ne_zero ha0 hb)

/-- Gamma-free polarization left after multiplying functional-equation mirror residues. -/
def d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel (x : ℂ) : ℂ :=
  d4ThetaCuspHawkingQuadraticDealiasedRational x * Complex.cot ((Real.pi : ℂ) * x)

/-- Unit-amplitude chiral AIME residue in the quadratically dealiased radial channel. -/
def d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue (z : ℂ) : ℂ :=
  d4FundamentalQNMCrossBranchAIMEResidue 1 (d4ThetaCuspHawkingQuadraticDealiasedLift z)

lemma d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue_eq (z : ℂ) :
    d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue z = (-12 / (9 / 4 + z ^ (2 : ℕ))) / d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus z := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue, d4FundamentalQNMCrossBranchAIMEResidue,
    d4FundamentalQNMCrossBranchAIMENumerator,
    d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq, d4ThetaCuspHawkingQuadraticDealiased_q]
  norm_num
  unfold d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus
  ring

/-- Exact FE-paired AIME return: all Gamma factors collapse to the Hawking cotangent
polarization. -/
theorem d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue_mul_neg (z : ℂ)
    (hx : Complex.I * z ≠ 0)
    (hxmh : Complex.I * z - 1 / 2 ≠ 0)
    (hxph : Complex.I * z + 1 / 2 ≠ 0)
    (hsin : Complex.sin ((Real.pi : ℂ) * (Complex.I * z)) ≠ 0)
    (hcos : Complex.cos ((Real.pi : ℂ) * (Complex.I * z)) ≠ 0) :
    d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue z * d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue (-z) =
      (-(576 : ℂ) / (Real.pi : ℂ)) *
        d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel (Complex.I * z) := by
  have hquad : (Complex.I * z) ^ (2 : ℕ) - 1 / 4 ≠ 0 := by
    rw [show (Complex.I * z) ^ (2 : ℕ) - 1 / 4 =
      (Complex.I * z - 1 / 2) * (Complex.I * z + 1 / 2) by ring]
    exact mul_ne_zero hxmh hxph
  have hDprod := d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus_mul_neg z hx hxmh hxph hsin hcos
  rw [d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue_eq, d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue_eq]
  rw [show (-z) ^ (2 : ℕ) = z ^ (2 : ℕ) by ring]
  rw [show (9 / 4 : ℂ) + z ^ (2 : ℕ) = 9 / 4 - (Complex.I * z) ^ (2 : ℕ) by
    rw [mul_pow, Complex.I_sq]
    ring]
  rw [div_mul_div_comm, hDprod]
  rw [d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel, d4ThetaCuspHawkingQuadraticDealiasedRational,
    Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos]
  field_simp [hx, hsin, hcos, hquad, Real.pi_ne_zero]
  ring

theorem d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_im_pos {a b : ℝ}
    (ha0 : 0 < a) (hah : a < 1 / 2) (hb : 0 < b) :
    0 < (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel
      ((a : ℂ) + (b : ℂ) * Complex.I)).im := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel, Complex.mul_im]
  exact add_pos
    (mul_pos_of_neg_of_neg
      (d4ThetaCuspHawkingQuadraticDealiasedRational_re_neg ha0 hah hb)
      (d4ThetaCuspHawkingQuadraticDealiased_cot_im_neg ha0 hah hb))
    (mul_pos
      (d4ThetaCuspHawkingQuadraticDealiasedRational_im_pos ha0 hah hb)
      (d4ThetaCuspHawkingQuadraticDealiased_cot_re_pos ha0 hah hb))

lemma d4ThetaCuspHawkingQuadraticDealiasedRational_neg (x : ℂ) : d4ThetaCuspHawkingQuadraticDealiasedRational (-x) = -d4ThetaCuspHawkingQuadraticDealiasedRational x := by
  unfold d4ThetaCuspHawkingQuadraticDealiasedRational
  rw [show (-x) ^ (2 : ℕ) = x ^ (2 : ℕ) by ring,
    show (-x) * (9 / 4 - x ^ (2 : ℕ)) ^ (2 : ℕ) =
      -(x * (9 / 4 - x ^ (2 : ℕ)) ^ (2 : ℕ)) by ring,
    div_neg]

lemma d4ThetaCuspHawkingQuadraticDealiased_cot_neg (x : ℂ) : Complex.cot (-x) = -Complex.cot x := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin]
  simp only [Complex.cos_neg, Complex.sin_neg, div_neg]

lemma d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_neg (x : ℂ) :
    d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel (-x) = d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel x := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel, d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel, d4ThetaCuspHawkingQuadraticDealiasedRational_neg]
  rw [show (Real.pi : ℂ) * -x = -((Real.pi : ℂ) * x) by ring,
    d4ThetaCuspHawkingQuadraticDealiased_cot_neg]
  ring

lemma d4ThetaCuspHawkingQuadraticDealiasedRational_conj (x : ℂ) :
    d4ThetaCuspHawkingQuadraticDealiasedRational (starRingEnd ℂ x) = starRingEnd ℂ (d4ThetaCuspHawkingQuadraticDealiasedRational x) := by
  unfold d4ThetaCuspHawkingQuadraticDealiasedRational
  simp only [map_div₀, map_sub, map_pow, map_mul,
    map_ofNat (starRingEnd ℂ) 4, map_ofNat (starRingEnd ℂ) 9]
  rw [map_one]

lemma d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_conj (x : ℂ) :
    d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel (starRingEnd ℂ x) =
      starRingEnd ℂ (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel x) := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel, d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel, d4ThetaCuspHawkingQuadraticDealiasedRational_conj]
  rw [show (Real.pi : ℂ) * starRingEnd ℂ x =
      starRingEnd ℂ ((Real.pi : ℂ) * x) by simp]
  rw [Complex.cot_conj, map_mul]

theorem d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_pureImag_im_eq_zero (b : ℝ) :
    (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel ((0 : ℂ) + (b : ℂ) * Complex.I)).im = 0 := by
  let x : ℂ := (0 : ℂ) + (b : ℂ) * Complex.I
  have hx : starRingEnd ℂ x = -x := by
    apply Complex.ext <;> simp [x]
  have h := d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_conj x
  rw [hx, d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_neg] at h
  have him := congrArg Complex.im h
  simp at him
  have him0 : (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel x).im = 0 := by
    linarith
  simpa [x] using him0

theorem d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_im_ne_zero {a b : ℝ}
    (hal : -1 / 2 < a) (har : a < 1 / 2) (ha : a ≠ 0) (hb : b ≠ 0) :
    (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel
      ((a : ℂ) + (b : ℂ) * Complex.I)).im ≠ 0 := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · rcases lt_or_gt_of_ne hb with hbNeg | hbPos
    · have ha' : 0 < -a := neg_pos.mpr haNeg
      have hb' : 0 < -b := neg_pos.mpr hbNeg
      have hah' : -a < 1 / 2 := by linarith
      have hpos := d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_im_pos ha' hah' hb'
      have harg :
          ((-a : ℝ) : ℂ) + ((-b : ℝ) : ℂ) * Complex.I =
            -((a : ℂ) + (b : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [harg, d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_neg] at hpos
      exact ne_of_gt hpos
    · have ha' : 0 < -a := neg_pos.mpr haNeg
      have hah' : -a < 1 / 2 := by linarith
      have hpos := d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_im_pos ha' hah' hbPos
      let x : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
      have harg :
          ((-a : ℝ) : ℂ) + (b : ℂ) * Complex.I =
            -(starRingEnd ℂ x) := by
        apply Complex.ext <;> simp [x]
      have hrel :
          d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel
              (((-a : ℝ) : ℂ) + (b : ℂ) * Complex.I) =
            starRingEnd ℂ (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel x) := by
        rw [harg, d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_neg,
          d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_conj]
      have him :
          (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel
              (((-a : ℝ) : ℂ) + (b : ℂ) * Complex.I)).im =
            -(d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel x).im := by
        have him' := congrArg Complex.im hrel
        simpa using him'
      have hneg : 0 < -(d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel x).im := by
        rw [← him]
        simpa only [ofReal_neg] using hpos
      intro hz
      have hzx : (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel x).im = 0 := by simpa [x] using hz
      rw [hzx] at hneg
      linarith
  · rcases lt_or_gt_of_ne hb with hbNeg | hbPos
    · have hb' : 0 < -b := neg_pos.mpr hbNeg
      have hpos := d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_im_pos haPos har hb'
      let x : ℂ := (a : ℂ) + ((-b : ℝ) : ℂ) * Complex.I
      have harg :
          starRingEnd ℂ x = (a : ℂ) + (b : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [x]
      have hrel := d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_conj x
      rw [harg] at hrel
      have him :
          (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel
              ((a : ℂ) + (b : ℂ) * Complex.I)).im =
            -(d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel x).im := by
        have him' := congrArg Complex.im hrel
        simpa using him'
      have hposx : 0 < (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel x).im := by
        simpa [x] using hpos
      intro hz
      rw [hz] at him
      rw [him] at hposx
      linarith
    · exact ne_of_gt (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_im_pos haPos har hbPos)

theorem d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_xi_im_eq_zero_iff (q : XiZeroCopy) :
    (d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel
      (Complex.I * xiSpectralPoint q)).im = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  let a : ℝ := (q.1 : ℂ).re - 1 / 2
  let b : ℝ := (q.1 : ℂ).im
  have hx :
      Complex.I * xiSpectralPoint q =
        (a : ℂ) + (b : ℂ) * Complex.I := by
    rw [I_mul_xiSpectralPoint]
    apply Complex.ext <;> simp [a, b]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hal : -1 / 2 < a := by
    dsimp [a]
    linarith
  have har : a < 1 / 2 := by
    dsimp [a]
    linarith
  have hb : b ≠ 0 := by
    exact xi_divisor_support_im_ne_zero q.1
  constructor
  · intro hzero
    by_contra hcritical
    have ha : a ≠ 0 := by
      dsimp [a]
      exact sub_ne_zero.mpr hcritical
    have hne := d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_im_ne_zero hal har ha hb
    rw [hx] at hzero
    exact hne hzero
  · intro hcritical
    have ha : a = 0 := by
      dsimp [a]
      linarith
    rw [hx, ha]
    exact d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_pureImag_im_eq_zero b

lemma d4ThetaCuspHawkingQuadraticDealiased_sin_pi_ne_zero_of_im_ne_zero {x : ℂ} (hx : x.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * x) ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hzero
  have him := congrArg Complex.im hk
  simp [Complex.mul_im] at him
  exact hx him

lemma d4ThetaCuspHawkingQuadraticDealiased_cos_pi_ne_zero_of_im_ne_zero {x : ℂ} (hx : x.im ≠ 0) :
    Complex.cos ((Real.pi : ℂ) * x) ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hzero
  have him := congrArg Complex.im hk
  simp [Complex.mul_im] at him
  exact hx him

lemma d4ThetaCuspHawkingQuadraticDealiased_I_mul_xiSpectralPoint_im_ne_zero (q : XiZeroCopy) :
    (Complex.I * xiSpectralPoint q).im ≠ 0 := by
  rw [I_mul_xiSpectralPoint]
  simpa using xi_divisor_support_im_ne_zero q.1

lemma d4ThetaCuspHawkingQuadraticDealiased_I_mul_xiSpectralPoint_sub_half_ne_neg_nat
    (q : XiZeroCopy) (m : ℕ) :
    Complex.I * xiSpectralPoint q - 1 / 2 ≠ -(m : ℂ) := by
  intro hzero
  apply d4ThetaCuspHawkingQuadraticDealiased_I_mul_xiSpectralPoint_im_ne_zero q
  calc
    (Complex.I * xiSpectralPoint q).im =
        (Complex.I * xiSpectralPoint q - 1 / 2).im := by simp
    _ = (-(m : ℂ)).im := congrArg Complex.im hzero
    _ = 0 := by simp

lemma d4ThetaCuspHawkingQuadraticDealiased_I_mul_xiSpectralPoint_ne_neg_nat
    (q : XiZeroCopy) (m : ℕ) :
    Complex.I * xiSpectralPoint q ≠ -(m : ℂ) := by
  intro hzero
  apply d4ThetaCuspHawkingQuadraticDealiased_I_mul_xiSpectralPoint_im_ne_zero q
  calc
    (Complex.I * xiSpectralPoint q).im = (-(m : ℂ)).im :=
      congrArg Complex.im hzero
    _ = 0 := by simp

theorem d4ThetaCuspHawkingQuadraticDealiased_boundaryJost_hasDerivAt_xi (q : XiZeroCopy) :
    HasDerivAt
      (fun omega : ℂ =>
        d4GravitationalHypergeometricBoundaryJost omega
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)))
      (d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) := by
  exact d4ThetaCuspHawkingQuadraticDealiased_boundaryJost_hasDerivAt (xiSpectralPoint q)
    (d4ThetaCuspHawkingQuadraticDealiased_I_mul_xiSpectralPoint_sub_half_ne_neg_nat q)

theorem d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus_xi_ne_zero (q : XiZeroCopy) :
    d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus (xiSpectralPoint q) ≠ 0 := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus_eq]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (Complex.Gamma_ne_zero
          (d4ThetaCuspHawkingQuadraticDealiased_I_mul_xiSpectralPoint_sub_half_ne_neg_nat q))
        thetaCuspHawkingHypergeometricGamma_half_ne_zero)
      (by
        unfold GaloisForLFunctions.reciprocalGammaEntire
        exact inv_ne_zero (Complex.Gamma_ne_zero
          (d4ThetaCuspHawkingQuadraticDealiased_I_mul_xiSpectralPoint_ne_neg_nat q))))
    (by
      apply neg_ne_zero.mpr
      exact div_ne_zero Complex.I_ne_zero (by norm_num))

/-- Every Xi descendant is a literal simple zero of the dealiased Birmingham--Mokhtari
boundary determinant. -/
theorem d4ThetaCuspHawkingQuadraticDealiased_boundaryJost_xi_simpleZero (q : XiZeroCopy) :
    d4GravitationalHypergeometricBoundaryJost
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)))
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)) = 0 ∧
      HasDerivAt
        (fun omega : ℂ =>
          d4GravitationalHypergeometricBoundaryJost omega
            (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)))
        (d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus (xiSpectralPoint q))
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) ∧
      d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus (xiSpectralPoint q) ≠ 0 := by
  exact ⟨d4ThetaCuspHawkingQuadraticDealiased_boundaryJost_qnmMinus_eq_zero _,
    d4ThetaCuspHawkingQuadraticDealiased_boundaryJost_hasDerivAt_xi q, d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus_xi_ne_zero q⟩

/-- Unit chiral source has an actual simple scattering pole whose Laurent residue is
`d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue`; this is pole incidence before the FE-pair collapse. -/
theorem d4ThetaCuspHawkingQuadraticDealiased_AIMEFrequencyResponse_tendsto_residue_xi (q : XiZeroCopy) :
    Tendsto
      (fun omega : ℂ =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMMinus 0
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) *
          d4FundamentalQNMCrossBranchAIMEFrequencyResponse 1
            (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)) omega)
      (nhdsWithin
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)))
        {thetaCuspHawkingTopologicalBlackHoleQNMMinus 0
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))}ᶜ)
      (nhds (d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue (xiSpectralPoint q))) := by
  let z := xiSpectralPoint q
  let sigma := thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (d4ThetaCuspHawkingQuadraticDealiasedLift z)
  let D : ℂ → ℂ := fun omega =>
    d4GravitationalHypergeometricBoundaryJost omega (d4ThetaCuspHawkingQuadraticDealiasedLift z)
  let N : ℂ → ℂ := fun _ =>
    d4FundamentalQNMCrossBranchAIMENumerator 1 (d4ThetaCuspHawkingQuadraticDealiasedLift z)
  have hD : HasDerivAt D (d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus z) sigma := by
    simpa [D, sigma, z] using d4ThetaCuspHawkingQuadraticDealiased_boundaryJost_hasDerivAt_xi q
  have hD0 : D sigma = 0 := by
    simpa [D, sigma] using d4ThetaCuspHawkingQuadraticDealiased_boundaryJost_qnmMinus_eq_zero z
  have hlim := tendsto_residue_of_simple_zero hD hD0 (d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus_xi_ne_zero q)
    (continuousAt_const : ContinuousAt N sigma)
  simpa [z, sigma, D, N, d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue,
    d4ThetaCuspHawkingQuadraticDealiasedBoundaryJostDerivativeMinus,
    d4FundamentalQNMCrossBranchAIMEResidue,
    d4FundamentalQNMCrossBranchAIMEFrequencyResponse,
    d4GravitationalHypergeometricBoundaryGreen, div_eq_mul_inv] using hlim

theorem d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue_mul_neg_xi (q : XiZeroCopy) :
    d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue (xiSpectralPoint q) *
        d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue (-xiSpectralPoint q) =
      (-(576 : ℂ) / (Real.pi : ℂ)) *
        d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel
          (Complex.I * xiSpectralPoint q) := by
  have him := d4ThetaCuspHawkingQuadraticDealiased_I_mul_xiSpectralPoint_im_ne_zero q
  apply d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue_mul_neg
  · intro hzero
    apply him
    simpa only [Complex.zero_im] using congrArg Complex.im hzero
  · intro hzero
    apply him
    calc
      (Complex.I * xiSpectralPoint q).im =
          (Complex.I * xiSpectralPoint q - 1 / 2).im := by simp
      _ = 0 := by
        simpa only [Complex.zero_im] using congrArg Complex.im hzero
  · intro hzero
    apply him
    calc
      (Complex.I * xiSpectralPoint q).im =
          (Complex.I * xiSpectralPoint q + 1 / 2).im := by simp
      _ = 0 := by
        simpa only [Complex.zero_im] using congrArg Complex.im hzero
  · exact d4ThetaCuspHawkingQuadraticDealiased_sin_pi_ne_zero_of_im_ne_zero him
  · exact d4ThetaCuspHawkingQuadraticDealiased_cos_pi_ne_zero_of_im_ne_zero him

theorem d4ThetaCuspHawkingQuadraticDealiasedAIMEResiduePair_xi_im_eq_zero_iff (q : XiZeroCopy) :
    (d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue (xiSpectralPoint q) *
      d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue (-xiSpectralPoint q)).im = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4ThetaCuspHawkingQuadraticDealiasedAIMEResidue_mul_neg_xi, Complex.mul_im]
  have hkernel := d4ThetaCuspHawkingQuadraticDealiasedPolarizationKernel_xi_im_eq_zero_iff q
  simpa [Real.pi_ne_zero] using hkernel

end

end RHTower
