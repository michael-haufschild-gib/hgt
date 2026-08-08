import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryExtensionClass
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryQuadratureSource
import GaloisForLFunctions.RHTower.XiShiftedHankelFirstCrossing

/-!
# Canonical monic extension class at a shifted Xi Hankel face

This specializes the projective finite-Hankel extension coordinate to the shifted Xi moment
family.  At a right-hand first crossing, the canonical monic remainder is nonpositive.  Thus a
source proof of its strict positivity would contradict every first crossing without choosing an
orientation of the null vector.
-/

open Matrix Polynomial Set

namespace RHTower

noncomputable section

/-- Canonically oriented first extension coordinate of a shifted Xi Hankel boundary. -/
def xiShiftedHankelBoundaryMonicRemainder
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  HTGeometry.finiteHankelBoundaryMonicRemainder
    (fun k => (xiShiftedReciprocalMoment y k).re) c

/-- The terminal product in the shifted Xi flux is a positive square times the canonical monic
extension class. -/
theorem xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) * xiShiftedHankelFirstOmittedCoupling y (n + 1) c =
      c (Fin.last n) ^ 2 * xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
    (fun k => (xiShiftedReciprocalMoment y k).re) c hlast

/-- At a right-hand first crossing with a positive-definite preceding block, the intrinsic monic
extension class is nonpositive. -/
theorem xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c) (Ici y) y) :
    xiShiftedHankelBoundaryMonicRemainder y c ≤ 0 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  have hcross := xiShiftedHankelFirstCrossing_terminal_product_nonpos
    hy n c hc hmin
  rw [xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder y c hlast]
    at hcross
  have hsquare : 0 < c (Fin.last n) ^ 2 := sq_pos_of_ne_zero hlast
  nlinarith

/-- The monic extension class is the monic positive-flat-quadrature remainder. -/
theorem xiShiftedHankelBoundaryQuadratureError_monic_eq_monicRemainder
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    xiShiftedHankelBoundaryQuadratureError y c
        (X ^ (n + 1) * HTGeometry.finiteHankelNullMonicPolynomial c) =
      xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.finiteHankelBoundaryQuadratureError_monic_eq_monicRemainder
    (fun k => (xiShiftedReciprocalMoment y k).re) c

/-- Completed-source formula for the canonical monic extension class. -/
theorem xiShiftedHankelBoundaryMonicRemainder_eq_inv_mul_sourceJet
    {w : ℝ} (hw : 0 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    xiShiftedHankelBoundaryMonicRemainder (w ^ 2) c =
      (c (Fin.last n))⁻¹ * xiShiftedHankelBoundarySourceJet w (n + 1) c := by
  rw [xiShiftedHankelBoundaryMonicRemainder,
    HTGeometry.finiteHankelBoundaryMonicRemainder_eq_inv_mul_raw _ c hlast,
    xiShiftedHankelBoundarySourceJet_eq hw]
  congr 1
  rw [xiShiftedHankelFirstOmittedCoupling,
    GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling,
    HTGeometry.momentFunctional_X_pow_mul_finiteHankelNullPolynomial]

/-- Projective form of completed-source transport: multiplication by the terminal coordinate
removes the orientation ambiguity and leaves a positive square times the monic remainder. -/
theorem xiShiftedHankel_terminal_mul_sourceJet_eq_sq_mul_monicRemainder
    {w : ℝ} (hw : 0 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) * xiShiftedHankelBoundarySourceJet w (n + 1) c =
      c (Fin.last n) ^ 2 *
        xiShiftedHankelBoundaryMonicRemainder (w ^ 2) c := by
  rw [xiShiftedHankelBoundarySourceJet_eq hw,
    xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder
      (w ^ 2) c hlast]

/-- **Projective prime--Gamma open core.** On the Euler ray, positivity of the canonical monic
extension class is exactly domination of the oriented prime discrepancy by the oriented
archimedean jet.  Both sides are invariant under reversing the null vector. -/
theorem xiShiftedHankelBoundaryMonicRemainder_pos_iff_projectiveSourceDominance
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < xiShiftedHankelBoundaryMonicRemainder (w ^ 2) c ↔
      -(c (Fin.last n) *
          xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c) <
        c (Fin.last n) *
          xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c := by
  have hsource :=
    xiShiftedHankel_terminal_mul_sourceJet_eq_sq_mul_monicRemainder
      (by linarith : 0 < w) c hlast
  rw [xiShiftedHankelBoundarySourceJet_eq_archimedean_add_discrepancy hw]
    at hsource
  have hsquare : 0 < c (Fin.last n) ^ 2 := sq_pos_of_ne_zero hlast
  constructor <;> intro h <;> nlinarith

/-- In the endpoint convergence window, the source-only negative-binomial prime--Gamma jet is the
projective extension coordinate up to the positive square of the terminal coefficient. -/
theorem xiShiftedHankel_terminal_mul_primeArchJet_eq_sq_mul_monicRemainder
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) * xiShiftedHankelBoundaryPrimeArchJet y (n + 1) c =
      c (Fin.last n) ^ 2 * xiShiftedHankelBoundaryMonicRemainder y c := by
  rw [← xiShiftedHankelBoundaryQuadratureError_eq_primeArchJet hy hymax,
    ← xiShiftedHankelFirstOmittedCoupling_eq_boundaryQuadratureError]
  exact xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder y c hlast

/-- **First-crossing source obstruction.** At a right-hand first crossing, projective domination
of the oriented prime discrepancy by the oriented archimedean jet is impossible.  Thus proving
this one source inequality for every admissible singular face excludes every first crossing. -/
theorem xiShiftedHankelFirstCrossing_not_projectiveSourceDominance
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ 2) n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c)
      (Ici (w ^ 2)) (w ^ 2)) :
    ¬ (-(c (Fin.last n) *
          xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c) <
        c (Fin.last n) *
          xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c) := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    (w ^ 2) n c hhead hcne hc
  have hnonpos := xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    (sq_pos_of_pos (by linarith : 0 < w)) n c hhead hcne hc hmin
  intro hdominance
  have hpos :=
    (xiShiftedHankelBoundaryMonicRemainder_pos_iff_projectiveSourceDominance
      hw c hlast).2 hdominance
  exact (not_lt_of_ge hnonpos) hpos

end

end RHTower
