import GaloisForLFunctions.HTGeometry.FiniteOrthoNoCommonRoot
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeWorldlineSourceLaw

/-!
# Characteristic-apex transport for canonical shifted-Xi admission

The shifted moment Möbius generator has characteristic curve `X=1/y`.  Along this curve, spatial
motion cancels the `X² P_n'` part of canonical coefficient transport.  The remaining equation is
triangular in degree.  In forward form its next-degree coefficient is the universal scalar `-2n`,
so no lower bound on interlacing gaps is required.

At an apex contact the diagonal term vanishes.  Finite positive-block no-common-root then makes the
next-degree value nonzero, proving every contact is transverse.
-/

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Backward-degree polynomial form of characteristic transport. -/
theorem finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_characteristicTransport
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) =
      X ^ 2 * (HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) n).derivative -
      (n : ℝ) • (X * HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) n) +
      HTGeometry.monicOrthoFirstCoeff
        (fun k => (xiShiftedReciprocalMoment y k).re) n •
        HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment y k).re) n +
      (2 * (n : ℝ) * HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) n) •
        HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment y k).re) (n - 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_monicHalfDensityLanding_add_prev
    hy hn hH]
  have hrec := HTGeometry.X_mul_monicOrtho_below hbelow
    (n := n) (by omega : n + 1 ≤ n + 2)
  change X * HTGeometry.monicOrtho s n =
      HTGeometry.monicOrtho s (n + 1) +
        HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n +
        HTGeometry.monicOrthoBeta s n • HTGeometry.monicOrtho s (n - 1) at hrec
  change xiShiftedAdaptiveMonicHalfDensityLanding s n +
      (((n : ℝ) - 1 / 2) * HTGeometry.monicOrthoBeta s n) •
        HTGeometry.monicOrtho s (n - 1) = _
  rw [xiShiftedAdaptiveMonicHalfDensityLanding,
    xiShiftedAdaptiveHalfDensityLanding,
    xiShiftedAdaptiveMonicHalfDensityCoefficient,
    xiShiftedMobiusHalfDensityGenerator,
    xiShiftedMobiusDensityGenerator]
  have hnext : HTGeometry.monicOrtho s (n + 1) =
      X * HTGeometry.monicOrtho s n -
        HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n -
        HTGeometry.monicOrthoBeta s n • HTGeometry.monicOrtho s (n - 1) := by
    calc
      HTGeometry.monicOrtho s (n + 1) =
          (HTGeometry.monicOrtho s (n + 1) +
            HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n +
            HTGeometry.monicOrthoBeta s n • HTGeometry.monicOrtho s (n - 1)) -
            HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n -
            HTGeometry.monicOrthoBeta s n • HTGeometry.monicOrtho s (n - 1) := by module
      _ = X * HTGeometry.monicOrtho s n -
            HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n -
            HTGeometry.monicOrthoBeta s n • HTGeometry.monicOrtho s (n - 1) := by
              rw [← hrec]
  rw [hnext]
  module

/-- Forward-degree form of characteristic transport.  The next-degree coefficient is the
universal scalar `-2n`, independent of all Jacobi root gaps. -/
theorem finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_forwardCharacteristicTransport
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) =
      X ^ 2 * (HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) n).derivative +
      (n : ℝ) • (X * HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) n) +
      (HTGeometry.monicOrthoFirstCoeff
          (fun k => (xiShiftedReciprocalMoment y k).re) n -
        2 * (n : ℝ) * HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n) •
        HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment y k).re) n -
      (2 * (n : ℝ)) • HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_characteristicTransport
    hy hn hH]
  have hrec := HTGeometry.X_mul_monicOrtho_below hbelow
    (n := n) (by omega : n + 1 ≤ n + 2)
  change X * HTGeometry.monicOrtho s n =
      HTGeometry.monicOrtho s (n + 1) +
        HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n +
        HTGeometry.monicOrthoBeta s n • HTGeometry.monicOrtho s (n - 1) at hrec
  have hprev : HTGeometry.monicOrthoBeta s n •
      HTGeometry.monicOrtho s (n - 1) =
        X * HTGeometry.monicOrtho s n - HTGeometry.monicOrtho s (n + 1) -
          HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n := by
    calc
      HTGeometry.monicOrthoBeta s n • HTGeometry.monicOrtho s (n - 1) =
          (HTGeometry.monicOrtho s (n + 1) +
            HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n +
            HTGeometry.monicOrthoBeta s n • HTGeometry.monicOrtho s (n - 1)) -
            HTGeometry.monicOrtho s (n + 1) -
            HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n := by module
      _ = X * HTGeometry.monicOrtho s n - HTGeometry.monicOrtho s (n + 1) -
            HTGeometry.monicOrthoAlpha s n • HTGeometry.monicOrtho s n := by
              rw [← hrec]
  change X ^ 2 * (HTGeometry.monicOrtho s n).derivative -
      (n : ℝ) • (X * HTGeometry.monicOrtho s n) +
      HTGeometry.monicOrthoFirstCoeff s n • HTGeometry.monicOrtho s n +
      (2 * (n : ℝ) * HTGeometry.monicOrthoBeta s n) •
        HTGeometry.monicOrtho s (n - 1) = _
  rw [show (2 * (n : ℝ) * HTGeometry.monicOrthoBeta s n) •
      HTGeometry.monicOrtho s (n - 1) =
        (2 * (n : ℝ)) •
          (HTGeometry.monicOrthoBeta s n • HTGeometry.monicOrtho s (n - 1)) by
    simp only [smul_smul]]
  rw [hprev]
  module

/-- Canonical shifted-Xi admission evaluated on the characteristic moving apex `X=1/y`. -/
def xiShiftedCanonicalAdmissionApexValue (y : ℝ) (n : ℕ) : ℝ :=
  (HTGeometry.monicMomentAdmissionPolynomial
    (fun k => (xiShiftedReciprocalMoment y k).re) n).eval y⁻¹

/-- Raw moving-apex chain rule before characteristic cancellation. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexValue_raw
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexValue v n)
      ((finitePolynomialVelocity
          (xiShiftedCanonicalAdmissionVelocity y n)).eval y⁻¹ -
        (y ^ 2)⁻¹ *
          (HTGeometry.monicMomentAdmissionPolynomial
            (fun k => (xiShiftedReciprocalMoment y k).re) n).derivative.eval y⁻¹) y := by
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  have hcoeff : ∀ i : Fin (n + 1),
      HasDerivAt (xiShiftedCanonicalAdmissionCurve n i)
        (xiShiftedCanonicalAdmissionVelocity y n i) y :=
    hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet
  have hapex : HasDerivAt (fun v : ℝ => v⁻¹) (-(y ^ 2)⁻¹) y :=
    hasDerivAt_inv (ne_of_gt hy)
  have hchain := hasDerivAt_finitePolynomialCurve_eval hcoeff hapex
  have hfun :
      (fun v => (finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) v).eval v⁻¹) =
        (fun v => (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n).eval v⁻¹) := by
    funext v
    rw [finitePolynomialCurve_xiShiftedCanonicalAdmission]
  rw [hfun] at hchain
  rw [finitePolynomialCurve_xiShiftedCanonicalAdmission] at hchain
  simpa only [xiShiftedCanonicalAdmissionApexValue, neg_mul, sub_eq_add_neg] using hchain

/-- Backward-degree characteristic law at the moving apex. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_prev
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexValue v n)
      ((HTGeometry.monicOrthoFirstCoeff
          (fun k => (xiShiftedReciprocalMoment y k).re) n - (n : ℝ) * y⁻¹) *
          xiShiftedCanonicalAdmissionApexValue y n +
        2 * (n : ℝ) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
          (HTGeometry.monicOrtho
            (fun k => (xiShiftedReciprocalMoment y k).re) (n - 1)).eval y⁻¹) y := by
  have hraw := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_raw hy hH
  apply hraw.congr_deriv
  rw [finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_characteristicTransport
    hy hn hH]
  rw [xiShiftedCanonicalAdmissionApexValue,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_smul, smul_eq_mul]
  rw [inv_pow]
  ring

/-- Forward-degree characteristic law.  Continuous mass transport is triangular in degree and
couples to the next apex value with universal coefficient `-2n`. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_next
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexValue v n)
      ((HTGeometry.monicOrthoFirstCoeff
          (fun k => (xiShiftedReciprocalMoment y k).re) n + (n : ℝ) * y⁻¹ -
          2 * (n : ℝ) * HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n) *
          xiShiftedCanonicalAdmissionApexValue y n -
        2 * (n : ℝ) *
          (HTGeometry.monicOrtho
            (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).eval y⁻¹) y := by
  have hraw := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_raw hy hH
  apply hraw.congr_deriv
  rw [finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_forwardCharacteristicTransport
    hy hn hH]
  rw [xiShiftedCanonicalAdmissionApexValue,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_smul, smul_eq_mul]
  rw [inv_pow]
  ring

/-- At apex contact, every diagonal transport term vanishes and only next degree remains. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexValue_contact
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexValue v n)
      (-2 * (n : ℝ) *
        (HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).eval y⁻¹) y := by
  have h := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_next hy hn hH
  rw [hcontact, mul_zero, zero_sub] at h
  convert h using 1
  ring

/-- **Finite shifted-Xi apex-contact transversality.**  A contact cannot stall: its derivative is
the nonzero next-degree apex value times the universal scalar `-2n`. -/
theorem xiShiftedCanonicalAdmissionApexValue_contact_transverse
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexValue v n)
      (-2 * (n : ℝ) *
        (HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).eval y⁻¹) y ∧
      -2 * (n : ℝ) *
        (HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).eval y⁻¹ ≠ 0 := by
  refine ⟨hasDerivAt_xiShiftedCanonicalAdmissionApexValue_contact hy hn hH hcontact, ?_⟩
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hroot : (HTGeometry.monicOrtho s n).eval y⁻¹ = 0 := by
    simpa only [s, xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH] using hcontact
  have hnext : (HTGeometry.monicOrtho s (n + 1)).eval y⁻¹ ≠ 0 := by
    intro hnext
    exact HTGeometry.monicOrtho_succ_no_common_root_below hbelow
      (by omega : n + 1 ≤ n + 2) hroot hnext
  change -2 * (n : ℝ) * (HTGeometry.monicOrtho s (n + 1)).eval y⁻¹ ≠ 0
  exact mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))) hnext

end

end RHTower
