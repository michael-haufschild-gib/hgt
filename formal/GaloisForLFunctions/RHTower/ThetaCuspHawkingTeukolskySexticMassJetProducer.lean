import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyFiniteMassParityRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskySexticJostDealiasing

/-!
# Sextic Teukolsky source from the second horizon-mass jet

Let `G(Q,x,u)` be the exact Birmingham--Mokhtari scalar-minus-vector potential bracket.  Its
second mass curvature at `x = 0` is

`G''(0) = 36 (Q+u-1)/(Q+2)^(2 : ℕ)`.

A negative-charge quadratic carrier has amplitude `conj(A)^(2 : ℕ)`.  Two insertions of a quadratic
horizon mass response `h A conj(A)` therefore produce the sextic carrier

`(h^(2 : ℕ)/2) A^(2 : ℕ) conj(A)^(4 : ℕ) G''(0)`.

The charge-minus-two carrier lies in the quadratic de-aliased angular channel
`Q_H = 1/4+z^(2 : ℕ)`, not the raw half-weight cusp channel.  At an Xi divisor, `re(z) != 0`.
Consequently `Q_H+2` never vanishes, and `Q_H+u-1` is nonzero throughout the physical exterior
`u >= 1`: away from the critical line its imaginary part is nonzero, while on the line its real
part is positive.  The curvature is also affine and nonconstant in `u`.  Consequently no
`u`-independent same-grade counterterm can erase this component at two distinct radii.

Combining coefficient nonvanishing with the alias-free sextic Jost theorem shows that this
canonical mass-jet source is on the negative gravitational Jost divisor exactly on the critical
line.

**[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**

This module identifies one stationary-background, two-memory component.  Mass derivatives of the
mode and frequency contribute at the same perturbative grade, so this local potential coefficient
is not by itself an invariant modulo the Teukolsky range and does not establish full-source
noncancellation.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Complexification of the exact second mass curvature of the `d=4` parity gap. -/
def d4ComplexSecondMassParityCurvature (Q : ℂ) (u : ℝ) : ℂ :=
  36 * (Q + (u : ℂ) - 1) / (Q + 2) ^ (2 : ℕ)

theorem d4ComplexSecondMassParityCurvature_ofReal (Q u : ℝ) :
    d4ComplexSecondMassParityCurvature (Q : ℂ) u =
      (d4SecondMassParityCurvature Q u : ℂ) := by
  unfold d4ComplexSecondMassParityCurvature d4SecondMassParityCurvature
  push_cast
  rfl

/-- The quadratic de-aliased angular denominator is nonzero at every Xi divisor. -/
lemma d4ThetaQuadraticDealiasedAngularQ_xi_add_two_ne_zero (q : XiZeroCopy) :
    d4ThetaTeukolskyAngularQ
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)) + 2 ≠ 0 := by
  rw [d4ThetaCuspHawkingQuadraticDealiased_q]
  intro hzero
  have him := congrArg Complex.im hzero
  simp [pow_two, Complex.mul_im] at him
  have hre : (xiSpectralPoint q).re ≠ 0 :=
    thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  have hprod : (xiSpectralPoint q).re * (xiSpectralPoint q).im = 0 := by
    nlinarith
  have hzim : (xiSpectralPoint q).im = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact (hre h).elim
    · exact h
  have hreal := congrArg Complex.re hzero
  simp [pow_two, Complex.mul_re, hzim] at hreal
  nlinarith [sq_nonneg (xiSpectralPoint q).re]

/-- In the physical exterior, the quadratic de-aliased second mass curvature never vanishes at an
Xi divisor. -/
theorem d4ComplexSecondMassParityCurvature_dealiased_xi_ne_zero
    (q : XiZeroCopy) (u : ℝ) (hu : 1 ≤ u) :
    d4ComplexSecondMassParityCurvature
        (d4ThetaTeukolskyAngularQ
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) u ≠ 0 := by
  unfold d4ComplexSecondMassParityCurvature
  apply div_ne_zero
  · apply mul_ne_zero (by norm_num)
    rw [d4ThetaCuspHawkingQuadraticDealiased_q]
    intro hzero
    have him := congrArg Complex.im hzero
    simp [pow_two, Complex.mul_im] at him
    have hre : (xiSpectralPoint q).re ≠ 0 :=
      thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
    have hprod : (xiSpectralPoint q).re * (xiSpectralPoint q).im = 0 := by
      nlinarith
    have hzim : (xiSpectralPoint q).im = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact (hre h).elim
      · exact h
    have hreal := congrArg Complex.re hzero
    simp [pow_two, Complex.mul_re, hzim] at hreal
    nlinarith [sq_nonneg (xiSpectralPoint q).re]
  · exact pow_ne_zero 2 (d4ThetaQuadraticDealiasedAngularQ_xi_add_two_ne_zero q)

/-- Exact radial principal difference of the second mass curvature. -/
theorem d4ComplexSecondMassParityCurvature_sub
    (Q : ℂ) (u v : ℝ) (hQ2 : Q + 2 ≠ 0) :
    d4ComplexSecondMassParityCurvature Q u -
        d4ComplexSecondMassParityCurvature Q v =
      36 * ((u - v : ℝ) : ℂ) / (Q + 2) ^ (2 : ℕ) := by
  unfold d4ComplexSecondMassParityCurvature
  field_simp [hQ2]
  push_cast
  ring

/-- Xi-labelled curvature separates every two distinct exterior radii. -/
theorem d4ComplexSecondMassParityCurvature_ne_const
    (q : XiZeroCopy) {u v : ℝ} (huv : u ≠ v) :
    d4ComplexSecondMassParityCurvature
        (d4ThetaTeukolskyAngularQ
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) u ≠
      d4ComplexSecondMassParityCurvature
        (d4ThetaTeukolskyAngularQ
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) v := by
  rw [ne_eq, ← sub_eq_zero, d4ComplexSecondMassParityCurvature_sub _ _ _
    (d4ThetaQuadraticDealiasedAngularQ_xi_add_two_ne_zero q)]
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (by exact_mod_cast sub_ne_zero.mpr huv)
  · exact pow_ne_zero 2 (d4ThetaQuadraticDealiasedAngularQ_xi_add_two_ne_zero q)

/-- No radially constant counterterm cancels the curvature at two distinct radii. -/
theorem d4ComplexSecondMassParityCurvature_add_const_not_both_zero
    (q : XiZeroCopy) {u v : ℝ} (huv : u ≠ v) (counterterm : ℂ) :
      ¬(d4ComplexSecondMassParityCurvature
          (d4ThetaTeukolskyAngularQ
            (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) u +
            counterterm = 0 ∧
      d4ComplexSecondMassParityCurvature
          (d4ThetaTeukolskyAngularQ
            (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) v +
            counterterm = 0) := by
  rintro ⟨hu, hv⟩
  apply d4ComplexSecondMassParityCurvature_ne_const q huv
  linear_combination hu - hv

/-- Canonical sextic coefficient obtained from two quadratic horizon-mass insertions into a
charge-minus-two carrier. -/
def d4ThetaHawkingSexticMassJetCoefficient
    (horizonMassResponse amplitude : ℂ) (u : ℝ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * horizonMassResponse ^ (2 : ℕ) * amplitude ^ (2 : ℕ) *
    (starRingEnd ℂ amplitude) ^ (4 : ℕ) *
      d4ComplexSecondMassParityCurvature
        (d4ThetaTeukolskyAngularQ (d4ThetaCuspHawkingQuadraticDealiasedLift z)) u

/-- Nonzero absorbed response and seed give a nonzero sextic mass-jet coefficient at every Xi
divisor. -/
theorem d4ThetaHawkingSexticMassJetCoefficient_xi_ne_zero
    {horizonMassResponse amplitude : ℂ}
    (hh : horizonMassResponse ≠ 0) (ha : amplitude ≠ 0)
    (q : XiZeroCopy) (u : ℝ) (hu : 1 ≤ u) :
    d4ThetaHawkingSexticMassJetCoefficient horizonMassResponse amplitude u
        (xiSpectralPoint q) ≠ 0 := by
  unfold d4ThetaHawkingSexticMassJetCoefficient
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hh))
        (pow_ne_zero 2 ha))
      (pow_ne_zero 4 ((map_ne_zero (starRingEnd ℂ)).2 ha)))
    (d4ComplexSecondMassParityCurvature_dealiased_xi_ne_zero q u hu)

/-- The complete sextic mass-jet coefficient distinguishes every pair of radii. -/
theorem d4ThetaHawkingSexticMassJetCoefficient_ne_const
    {horizonMassResponse amplitude : ℂ}
    (hh : horizonMassResponse ≠ 0) (ha : amplitude ≠ 0)
    (q : XiZeroCopy) {u v : ℝ} (huv : u ≠ v) :
    d4ThetaHawkingSexticMassJetCoefficient horizonMassResponse amplitude u
        (xiSpectralPoint q) ≠
      d4ThetaHawkingSexticMassJetCoefficient horizonMassResponse amplitude v
        (xiSpectralPoint q) := by
  let prefactor : ℂ :=
    (1 / 2 : ℂ) * horizonMassResponse ^ (2 : ℕ) * amplitude ^ (2 : ℕ) *
      (starRingEnd ℂ amplitude) ^ (4 : ℕ)
  have hprefactor : prefactor ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hh))
        (pow_ne_zero 2 ha))
      (pow_ne_zero 4 ((map_ne_zero (starRingEnd ℂ)).2 ha))
  change prefactor * d4ComplexSecondMassParityCurvature
      (d4ThetaTeukolskyAngularQ
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) u ≠
    prefactor * d4ComplexSecondMassParityCurvature
      (d4ThetaTeukolskyAngularQ
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) v
  exact fun h => d4ComplexSecondMassParityCurvature_ne_const q huv
    (mul_left_cancel₀ hprefactor h)

/-- No radially constant same-grade term cancels the sextic coefficient at two radii. -/
theorem d4ThetaHawkingSexticMassJetCoefficient_add_const_not_both_zero
    {horizonMassResponse amplitude : ℂ}
    (hh : horizonMassResponse ≠ 0) (ha : amplitude ≠ 0)
    (q : XiZeroCopy) {u v : ℝ} (huv : u ≠ v) (counterterm : ℂ) :
    ¬(d4ThetaHawkingSexticMassJetCoefficient horizonMassResponse amplitude u
          (xiSpectralPoint q) + counterterm = 0 ∧
      d4ThetaHawkingSexticMassJetCoefficient horizonMassResponse amplitude v
          (xiSpectralPoint q) + counterterm = 0) := by
  rintro ⟨hu, hv⟩
  apply d4ThetaHawkingSexticMassJetCoefficient_ne_const hh ha q huv
  linear_combination hu - hv

/-- Nonzero canonical sextic source and negative-Jost incidence occur together exactly on the
critical line. -/
theorem d4ThetaHawkingSexticMassJetSource_incides_iff_re_eq_half
    {horizonMassResponse amplitude : ℂ}
    (hh : horizonMassResponse ≠ 0) (ha : amplitude ≠ 0)
    (q : XiZeroCopy) (u : ℝ) (hu : 1 ≤ u) :
    (d4ThetaHawkingSexticMassJetCoefficient horizonMassResponse amplitude u
          (xiSpectralPoint q) ≠ 0 ∧
      d4ThetaHawkingChargeDecayNegativeJost 0 (xiSpectralPoint q) = 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4ThetaHawkingSexticNegativeJost_xi_eq_zero_iff]
  simp [d4ThetaHawkingSexticMassJetCoefficient_xi_ne_zero hh ha q u hu]

end

end RHTower
