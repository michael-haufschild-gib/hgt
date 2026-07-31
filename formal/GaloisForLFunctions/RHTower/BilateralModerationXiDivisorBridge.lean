import GaloisForLFunctions.RHTower.BilateralAllPrimeIndLimit
import GaloisForLFunctions.RHTower.DeningerDivisorGaugeWardIdentity

/-!
# The moderation selector at the actual Xi divisor: conormal conservativity ⟺ RH

The bilateral moderation machinery is abstract in `s`; the divisor flow modules carry the
actual multiplicity-exact Xi zeros.  This file joins them: instantiating the selector at every
divisor copy turns conormal conservativity into an exact equivalence with the Riemann
hypothesis.

* `riemannHypothesis_iff_forall_xiZero_bilateralModerate` — for any fixed prime `p ≥ 2` and
  grade `k`, the bilateral jet family of **every** Xi zero is moderate iff RH.
* `riemannHypothesis_iff_forall_xiZero_exists_moderate_eigen` — **conormal conservativity at
  the divisor**: every Xi zero carries a *nonzero moderate bilateral sewing eigenfamily* with
  its own half-density character iff RH.  The backward direction exhibits the canonical
  conormal `e ↦ λ^(-e)`; the forward direction is the moderation selector followed by the
  divisor endgame.

These are equivalences, honestly labelled as re-encodings: the card's open arithmetic sewing
conjecture is exactly the assertion that the completed source construction *supplies* the
left-hand side.  What this file contributes unconditionally is that the supply would be
exactly RH — no more and no less — with no loss at any single zero.
-/

noncomputable section

open Complex

namespace RHTower

/-- For a fixed prime and grade, moderation of every Xi zero's bilateral jet family is
exactly the Riemann hypothesis. -/
theorem riemannHypothesis_iff_forall_xiZero_bilateralModerate {p : ℕ}
    (hp : 2 ≤ p) (k : ℕ) :
    (∀ q : XiZeroCopy, bilateralModerate
      (bilateralJetFamily p (deningerDivisorThetaEigen q) k)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    exact (bilateralModerate_jetFamily_iff_re_eq_half hp k
      (deningerDivisorThetaEigen q)).mp (h q)
  · intro hRH q
    have hre : (deningerDivisorThetaEigen q).re = 1 / 2 :=
      xi_divisor_support_re_eq_half_of_rh hRH q.1
    exact (bilateralModerate_jetFamily_iff_re_eq_half hp k
      (deningerDivisorThetaEigen q)).mpr hre

/-- The canonical conormal eigenfamily of a character: `e ↦ λ^(-e)` solves the sewing
recursion. -/
theorem bilateralEigenFamily_sewing {lam : ℂ} (hlam : lam ≠ 0) (e : ℤ) :
    bilateralEigenFamily lam (e - 1) = lam * bilateralEigenFamily lam e := by
  rw [bilateralEigenFamily, bilateralEigenFamily,
    show -(e - 1) = 1 + -e by ring, zpow_add₀ hlam, zpow_one]

/-- The canonical conormal eigenfamily is nonzero. -/
theorem bilateralEigenFamily_ne_zero (lam : ℂ) :
    bilateralEigenFamily lam ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [bilateralEigenFamily, neg_zero, zpow_zero, Pi.zero_apply] at h0
  exact one_ne_zero h0

/-- A unimodular character has a moderate conormal eigenfamily. -/
theorem bilateralModerate_eigenFamily_of_norm_eq_one {lam : ℂ}
    (h : ‖lam‖ = 1) :
    bilateralModerate (bilateralEigenFamily lam) := by
  refine ⟨1, 0, fun e => ?_⟩
  rw [pow_zero, mul_one, bilateralEigenFamily, norm_zpow, h, one_zpow]

/-- **Conormal conservativity at the divisor ⟺ RH.**  Every Xi zero carries a nonzero
moderate bilateral sewing eigenfamily with its own half-density character iff the Riemann
hypothesis holds.  The card's arithmetic sewing conjecture asserts that the completed source
construction supplies the left-hand side; this equivalence says that supply is exactly RH. -/
theorem riemannHypothesis_iff_forall_xiZero_exists_moderate_eigen {p : ℕ}
    (hp : 2 ≤ p) :
    (∀ q : XiZeroCopy, ∃ c : ℤ → ℂ, c ≠ 0 ∧ bilateralModerate c ∧
      ∀ e : ℤ, c (e - 1) =
        bilateralHalfDensityCharacter p (deningerDivisorThetaEigen q) * c e) ↔
      RiemannHypothesis := by
  have hp0 : 0 < p := lt_of_lt_of_le two_pos hp
  constructor
  · intro h
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    obtain ⟨c, hc0, hmod, heig⟩ := h q
    exact re_eq_half_of_moderate_bilateral_eigen hp hc0 hmod heig
  · intro hRH q
    have hre : (deningerDivisorThetaEigen q).re = 1 / 2 :=
      xi_divisor_support_re_eq_half_of_rh hRH q.1
    have hlam : bilateralHalfDensityCharacter p
        (deningerDivisorThetaEigen q) ≠ 0 :=
      bilateralHalfDensityCharacter_ne_zero hp0 _
    have hnorm : ‖bilateralHalfDensityCharacter p
        (deningerDivisorThetaEigen q)‖ = 1 :=
      (norm_bilateralHalfDensityCharacter_eq_one_iff hp _).mpr hre
    exact ⟨bilateralEigenFamily _, bilateralEigenFamily_ne_zero _,
      bilateralModerate_eigenFamily_of_norm_eq_one hnorm,
      bilateralEigenFamily_sewing hlam⟩

end RHTower
