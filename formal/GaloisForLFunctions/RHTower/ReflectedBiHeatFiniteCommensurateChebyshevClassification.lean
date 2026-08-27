import GaloisForLFunctions.RHTower.ReflectedBiHeatSignedThreeScaleReceiverCone
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Reflected bi-heat finite commensurate Chebyshev classification

Every finite signed packet of commensurate RBH aperture rates factors through one explicit
second-kind Chebyshev polynomial.  Its forced `sinh(t)` wall factor is the only real zero exactly
when that polynomial has no root on `(1,∞)`.  The same factorization holds for the physical
multiplicity-leading aperture packet, so every polynomial-wall-selective packet is an exact RH
receiver.

This closes arbitrary finite signed cancellation for commensurate diagonal apertures; the prior
two- and three-rate cones are its degree-one and degree-two shadows.

`[NEW] [FINITE COMMENSURATE CLASSIFICATION] [CHEBYSHEV REDUCTION] [LEAN-PROVED]`
-/

open Complex Filter Topology Polynomial Polynomial.Chebyshev
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Finite signed packet of the first `N` commensurate hyperbolic rates. -/
def reflectedBiHeatFiniteCommensurateReporter
    {N : ℕ} (a : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ i, a i * Real.sinh (((i : ℕ) + 1 : ℝ) * t)

/-- Second-kind Chebyshev polynomial carrying a finite commensurate signed packet. -/
def reflectedBiHeatFiniteCommensurateChebyshevPolynomial
    {N : ℕ} (a : Fin N → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (a i) *
    Polynomial.Chebyshev.U ℝ ((i : ℕ) : ℤ)

/-- Exact finite multiple-angle factorization through one Chebyshev polynomial. -/
theorem reflectedBiHeatFiniteCommensurateReporter_factor
    {N : ℕ} (a : Fin N → ℝ) (t : ℝ) :
    reflectedBiHeatFiniteCommensurateReporter a t =
      Real.sinh t *
        (reflectedBiHeatFiniteCommensurateChebyshevPolynomial a).eval
          (Real.cosh t) := by
  rw [reflectedBiHeatFiniteCommensurateReporter,
    reflectedBiHeatFiniteCommensurateChebyshevPolynomial,
    Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  have hU := Polynomial.Chebyshev.U_real_cosh t ((i : ℕ) : ℤ)
  calc
    a i * Real.sinh (((i : ℕ) + 1 : ℝ) * t) =
        a i *
          ((Polynomial.Chebyshev.U ℝ ((i : ℕ) : ℤ)).eval (Real.cosh t) *
            Real.sinh t) := by
      rw [hU]
      norm_num
    _ = Real.sinh t *
        (a i * (Polynomial.Chebyshev.U ℝ ((i : ℕ) : ℤ)).eval
          (Real.cosh t)) := by ring

/-- Polynomial half-line condition for a wall-selective finite commensurate packet. -/
def ReflectedBiHeatFiniteCommensurateWallSelective
    {N : ℕ} (a : Fin N → ℝ) : Prop :=
  ∀ u : ℝ, 1 < u →
    (reflectedBiHeatFiniteCommensurateChebyshevPolynomial a).eval u ≠ 0

/-- Complete finite commensurate classification: the forced wall zero is unique exactly when the
associated Chebyshev polynomial has no root on `(1,∞)`. -/
theorem reflectedBiHeatFiniteCommensurateWallSelective_iff
    {N : ℕ} (a : Fin N → ℝ) :
    ReflectedBiHeatFiniteCommensurateWallSelective a ↔
      ∀ t : ℝ,
        reflectedBiHeatFiniteCommensurateReporter a t = 0 ↔ t = 0 := by
  constructor
  · intro hpoly t
    rw [reflectedBiHeatFiniteCommensurateReporter_factor]
    constructor
    · intro hzero
      rcases mul_eq_zero.mp hzero with hsinh | hpolyzero
      · exact Real.sinh_eq_zero.mp hsinh
      · by_contra ht
        exact hpoly (Real.cosh t) (Real.one_lt_cosh.mpr ht) hpolyzero
    · rintro rfl
      simp
  · intro hselect u hu hpolyzero
    let t := Real.arcosh u
    have ht : 0 < t := Real.arcosh_pos hu
    have hcosh : Real.cosh t = u := Real.cosh_arcosh hu.le
    have hzero : reflectedBiHeatFiniteCommensurateReporter a t = 0 := by
      rw [reflectedBiHeatFiniteCommensurateReporter_factor, hcosh,
        hpolyzero, mul_zero]
    exact ht.ne' ((hselect t).mp hzero)

/-- Physical finite packet at apertures `x^(i+1)` with canonical centering weights. -/
def reflectedBiHeatFiniteCommensurateApertureGap
    {N : ℕ} (a : Fin N → ℝ) (x : ℝ) (rho : XiDivisorSupport) : ℝ :=
  ∑ i, a i *
    (x ^ (((i : ℕ) + 1 : ℝ) / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ ((i : ℕ) + 1)) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ ((i : ℕ) + 1)) ^ 2))

/-- Exact physical finite-packet factorization. -/
theorem reflectedBiHeatFiniteCommensurateApertureGap_eq_reporter
    {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hx : 0 < x)
    (rho : XiDivisorSupport) :
    reflectedBiHeatFiniteCommensurateApertureGap a x rho =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        reflectedBiHeatFiniteCommensurateReporter a
          (Real.log x * ((rho : ℂ).re - 1 / 2)) := by
  rw [reflectedBiHeatFiniteCommensurateApertureGap,
    reflectedBiHeatFiniteCommensurateReporter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hgap := reflectedBiHeatWeightedPowerApertureGap_eq_sinh
    ((i : ℕ) + 1) hx rho
  norm_num at hgap
  rw [hgap]
  ring

/-- A wall-selective finite Chebyshev packet balances physically exactly on the critical wall. -/
theorem reflectedBiHeatFiniteCommensurateApertureGap_eq_zero_iff
    {N : ℕ} {a : Fin N → ℝ}
    (hselect : ReflectedBiHeatFiniteCommensurateWallSelective a)
    {x : ℝ} (hx : 1 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatFiniteCommensurateApertureGap a x rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatFiniteCommensurateApertureGap_eq_reporter a
    (lt_trans zero_lt_one hx) rho]
  have hcoef :
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)))
  constructor
  · intro hzero
    have hreport : reflectedBiHeatFiniteCommensurateReporter a
        (Real.log x * ((rho : ℂ).re - 1 / 2)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hcoef
    have hu :=
      ((reflectedBiHeatFiniteCommensurateWallSelective_iff a).mp hselect
        (Real.log x * ((rho : ℂ).re - 1 / 2))).mp hreport
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsub : (rho : ℂ).re - 1 / 2 = 0 :=
      (mul_eq_zero.mp hu).resolve_left hlog.ne'
    exact sub_eq_zero.mp hsub
  · intro hre
    rw [hre, sub_self, mul_zero]
    simp [reflectedBiHeatFiniteCommensurateReporter]

/-- Every wall-selective finite commensurate packet supplies an RH-equivalent receiver. -/
theorem riemannHypothesis_iff_reflectedBiHeatFiniteCommensurateApertureGap_eq_zero
    {N : ℕ} {a : Fin N → ℝ}
    (hselect : ReflectedBiHeatFiniteCommensurateWallSelective a)
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatFiniteCommensurateApertureGap a x rho = 0 := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatFiniteCommensurateApertureGap_eq_zero_iff
      hselect hx rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatFiniteCommensurateApertureGap_eq_zero_iff
        hselect hx rho).mp (h rho)

end

end RHTower
