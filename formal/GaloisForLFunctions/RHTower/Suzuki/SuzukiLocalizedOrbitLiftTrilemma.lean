import GaloisForLFunctions.RHTower.Suzuki.SuzukiSupportPrunedSelfAdjointSeamCarrier

/-!
# Square-summable localized orbit lifts lose translation covariance

A localized valuation lift places translated copies of one physical source in separate carrier
coordinates.  Exact projective translation covariance forces the coordinate weights to have
translation-invariant modulus.  On an infinite additive group, such a weight is square summable
only when it is zero.

This is the formal core of the Suzuki bounded/covariant/self-adjoint orbit-lift trilemma.  It does
not rule out the live source-dependent `ell¹ ⊂ ell² ⊂ ell∞` coefficient relation, and it assumes
neither RH nor a completed-domain carrier map.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- A square-summable scalar weight on an infinite additive group cannot be invariant under every
translation unless it vanishes. -/
theorem translationInvariant_summable_normSq_eq_zero
    {G : Type*} [AddGroup G] [Infinite G]
    (w : G → ℂ)
    (hsum : Summable (fun g => ‖w g‖ ^ (2 : ℕ)))
    (hinv : ∀ g δ, w (g + δ) = w g) :
    w = 0 := by
  funext g
  change w g = 0
  have hconst : ∀ x, w x = w 0 := by
    intro x
    simpa using hinv 0 x
  by_contra hne
  have hzero_ne : w 0 ≠ 0 := by
    intro hzero
    apply hne
    rw [hconst g, hzero]
  have hpos : 0 < ‖w 0‖ ^ (2 : ℕ) := by positivity
  have hs : Summable (fun _ : G => ‖w 0‖ ^ (2 : ℕ)) := by
    simpa only [hconst] using hsum
  haveI : Finite G := Finite.of_summable_const hpos hs
  exact not_finite G

/-- The analysis-side obstruction needs only invariant modulus.  This is the form forced both by
unit-modulus projective covariance and by a self-adjoint diagonal similarity along every active
edge. -/
theorem translationInvariantNorm_summable_normSq_eq_zero
    {G : Type*} [AddGroup G] [Infinite G]
    (w : G → ℂ)
    (hsum : Summable (fun g => ‖w g‖ ^ (2 : ℕ)))
    (hinv : ∀ g δ, ‖w (g + δ)‖ = ‖w g‖) :
    w = 0 := by
  funext g
  change w g = 0
  have hconst : ∀ x, ‖w x‖ = ‖w 0‖ := by
    intro x
    simpa using hinv 0 x
  by_contra hne
  have hzero_ne : w 0 ≠ 0 := by
    intro hzero
    apply hne
    apply norm_eq_zero.mp
    rw [hconst g, hzero, norm_zero]
  have hpos : 0 < ‖w 0‖ ^ (2 : ℕ) := by positivity
  have hs : Summable (fun _ : G => ‖w 0‖ ^ (2 : ℕ)) := by
    simpa only [hconst] using hsum
  haveI : Finite G := Finite.of_summable_const hpos hs
  exact not_finite G

/-- Unit-modulus projective covariance still forces a square-summable orbit weight to vanish.
Allowing a phase at each translation therefore does not repair the localized Hilbert lift. -/
theorem projectivelyTranslationCovariant_summable_normSq_eq_zero
    {G : Type*} [AddGroup G] [Infinite G]
    (w phase : G → ℂ)
    (hsum : Summable (fun g => ‖w g‖ ^ (2 : ℕ)))
    (hphase : ∀ δ, ‖phase δ‖ = 1)
    (hcov : ∀ g δ, w (g + δ) = phase δ * w g) :
    w = 0 := by
  apply translationInvariantNorm_summable_normSq_eq_zero w hsum
  intro g δ
  rw [hcov, norm_mul, hphase, one_mul]

/-- Suzuki specialization: the complete finite-support prime-valuation lattice is infinite, so
no nonzero square-summable valuation weight can retain exact projective translation covariance. -/
theorem suzukiProjectivelyCovariantSummableWeight_eq_zero
    (w phase : SuzukiSeamValuation → ℂ)
    (hsum : Summable (fun ν => ‖w ν‖ ^ (2 : ℕ)))
    (hphase : ∀ δ, ‖phase δ‖ = 1)
    (hcov : ∀ ν δ, w (ν + δ) = phase δ * w ν) :
    w = 0 := by
  exact projectivelyTranslationCovariant_summable_normSq_eq_zero
    w phase hsum hphase hcov

end GaloisForLFunctions.RHTower

