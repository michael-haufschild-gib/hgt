import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBUnboundedMaximalDissipativeReflectedForcingNoGo

/-!
# Arbitrary unbounded dissipative diagonal-response polarity no-go

HB needs a source-fixed two-leg observable with orientation opposite to standard passivity. The
preceding maximal-dissipative no-go proved that closed order-maximal passive dynamics cannot
extinguish either exact source on a tilted Schwarz Xi pair. This module removes maximality,
closedness, density, and even response existence from the polarity obstruction.

For any partial dissipative operator `A`, any upper-half-plane parameter `z`, and any nonzero source
`s`, every solution of `(A-z)x=s` satisfies

`Im <x,s> = Im <x,A x> - Im(z)||x||^(2 : ℕ) < 0`.

The antidissipative lower-half-plane law has the strict reverse sign. Applied to the exact
doubled-weight Teukolsky sources at a tilted Xi copy and its Schwarz copy, every existing diagonal
source-response observable therefore has standard passive polarity, never HB's missing opposite
polarity.

This kills arbitrary unbounded linear passive response-as-left-leg producers. Strongest positive
survivor: a linear HB producer must use an independently transforming left-QNM leg rather than the
response itself. Otherwise it must abandon passivity or response existence, or become nonlinear.

`[NEW APPLICATION] [HB ROUTE KILL] [ARBITRARY UNBOUNDED DOMAIN] [DISSIPATIVE]
[DIAGONAL RESPONSE POLARITY] [REFLECTED TEUKOLSKY SOURCE] [LEAN-PROVED]`
-/

open Complex Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem pmapDissipative_shiftedResponse_inner_im_neg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapDissipative A)
    (z : ℂ) (hz : 0 < z.im) (source : H) (hsource : source ≠ 0)
    (x : A.domain) (hx : shiftedMap A z x = source) :
    (⟪(x : H), source⟫_ℂ).im < 0 := by
  have hx0 : (x : H) ≠ 0 := by
    intro hzero
    apply hsource
    have hxsub : x = 0 := Subtype.ext hzero
    rw [← hx, hxsub, map_zero]
  have him :
      (⟪(x : H), source⟫_ℂ).im =
        (⟪(x : H), A x⟫_ℂ).im - z.im * ‖(x : H)‖ ^ (2 : ℕ) := by
    rw [← hx]
    simp [shiftedMap_apply, pow_two, Complex.mul_im]
  have hnorm : 0 < ‖(x : H)‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hstrict : 0 < z.im * ‖(x : H)‖ ^ (2 : ℕ) := mul_pos hz hnorm
  rw [him]
  linarith [hA x]

theorem pmapAntidissipative_shiftedResponse_inner_im_pos
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapAntidissipative A)
    (z : ℂ) (hz : z.im < 0) (source : H) (hsource : source ≠ 0)
    (x : A.domain) (hx : shiftedMap A z x = source) :
    0 < (⟪(x : H), source⟫_ℂ).im := by
  have hx0 : (x : H) ≠ 0 := by
    intro hzero
    apply hsource
    have hxsub : x = 0 := Subtype.ext hzero
    rw [← hx, hxsub, map_zero]
  have him :
      (⟪(x : H), source⟫_ℂ).im =
        (⟪(x : H), A x⟫_ℂ).im - z.im * ‖(x : H)‖ ^ (2 : ℕ) := by
    rw [← hx]
    simp [shiftedMap_apply, pow_two, Complex.mul_im]
  have hnorm : 0 < ‖(x : H)‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hstrict : z.im * ‖(x : H)‖ ^ (2 : ℕ) < 0 := mul_neg_of_neg_of_pos hz hnorm
  rw [him]
  linarith [hA x]

def D4HBArbitraryUnboundedDissipativeDiagonalReflectedSourcePolarity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (upper lower : H →ₗ.[ℂ] H) (amplitude mixed anti : ℂ)
    (profile : H) (q : XiZeroCopy) : Prop :=
  let qstar := xiZeroCopyConjEquiv q
  let lambda := d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)
  let lambdaStar :=
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint qstar)
  let source := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile q
  let sourceStar := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile qstar
  (0 < lambda.im ∧
      (∀ x : upper.domain, shiftedMap upper lambda x = source →
        (⟪(x : H), source⟫_ℂ).im < 0) ∧
      (∀ x : lower.domain, shiftedMap lower lambdaStar x = sourceStar →
        0 < (⟪(x : H), sourceStar⟫_ℂ).im)) ∨
    (lambda.im < 0 ∧
      (∀ x : lower.domain, shiftedMap lower lambda x = source →
        0 < (⟪(x : H), source⟫_ℂ).im) ∧
      (∀ x : upper.domain, shiftedMap upper lambdaStar x = sourceStar →
        (⟪(x : H), sourceStar⟫_ℂ).im < 0))

theorem d4ThetaReducedSecondOrderChiralTeukolskySource_arbitraryUnboundedDissipative_diagonalReflected_polarity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (upper lower : H →ₗ.[ℂ] H)
    (hupper : IsPMapDissipative upper)
    (hlower : IsPMapAntidissipative lower)
    {amplitude : ℂ} (ha : amplitude ≠ 0) (mixed anti : ℂ)
    (profile : H) (hprofile : profile ≠ 0)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    D4HBArbitraryUnboundedDissipativeDiagonalReflectedSourcePolarity
      upper lower amplitude mixed anti profile q := by
  let qstar := xiZeroCopyConjEquiv q
  let lambda := d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)
  let lambdaStar :=
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint qstar)
  let source := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile q
  let sourceStar := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile qstar
  have htiltStar : (qstar.1 : ℂ).re ≠ 1 / 2 :=
    xiZeroCopyConjEquiv_tilt q htilt
  have hlambda : lambda.im ≠ 0 :=
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_xi_im_ne_zero_of_tilt q htilt
  have hreflect : lambdaStar.im = -lambda.im :=
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_copyConj_im q
  have hsource : source ≠ 0 :=
    d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector_ne_zero
      ha mixed anti 0 profile hprofile q htilt
  have hsourceStar : sourceStar ≠ 0 :=
    d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector_ne_zero
      ha mixed anti 0 profile hprofile qstar htiltStar
  change (0 < lambda.im ∧
      (∀ x : upper.domain, shiftedMap upper lambda x = source →
        (⟪(x : H), source⟫_ℂ).im < 0) ∧
      (∀ x : lower.domain, shiftedMap lower lambdaStar x = sourceStar →
        0 < (⟪(x : H), sourceStar⟫_ℂ).im)) ∨
    (lambda.im < 0 ∧
      (∀ x : lower.domain, shiftedMap lower lambda x = source →
        0 < (⟪(x : H), source⟫_ℂ).im) ∧
      (∀ x : upper.domain, shiftedMap upper lambdaStar x = sourceStar →
        (⟪(x : H), sourceStar⟫_ℂ).im < 0))
  rcases lt_or_gt_of_ne hlambda with hneg | hpos
  · right
    refine ⟨hneg, ?_, ?_⟩
    · intro x hx
      exact pmapAntidissipative_shiftedResponse_inner_im_pos
        lower hlower lambda hneg source hsource x hx
    · intro x hx
      exact pmapDissipative_shiftedResponse_inner_im_neg
        upper hupper lambdaStar (by linarith) sourceStar hsourceStar x hx
  · left
    refine ⟨hpos, ?_, ?_⟩
    · intro x hx
      exact pmapDissipative_shiftedResponse_inner_im_neg
        upper hupper lambda hpos source hsource x hx
    · intro x hx
      exact pmapAntidissipative_shiftedResponse_inner_im_pos
        lower hlower lambdaStar (by linarith) sourceStar hsourceStar x hx

def D4HBArbitraryUnboundedDissipativeDiagonalResponsePolarityRouteKilled : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (upper lower : H →ₗ.[ℂ] H)
    (amplitude mixed anti : ℂ) (profile : H),
      IsPMapDissipative upper →
      IsPMapAntidissipative lower →
      amplitude ≠ 0 → profile ≠ 0 →
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
        D4HBArbitraryUnboundedDissipativeDiagonalReflectedSourcePolarity
          upper lower amplitude mixed anti profile q

theorem d4HBArbitraryUnboundedDissipativeDiagonalResponsePolarityRouteKilled :
    D4HBArbitraryUnboundedDissipativeDiagonalResponsePolarityRouteKilled := by
  intro H _ _ upper lower amplitude mixed anti profile
    hupper hlower ha hprofile q htilt
  exact
    d4ThetaReducedSecondOrderChiralTeukolskySource_arbitraryUnboundedDissipative_diagonalReflected_polarity
      upper lower hupper hlower ha mixed anti profile hprofile q htilt

end

end RHTower
