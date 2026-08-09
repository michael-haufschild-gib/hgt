import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryPadeContactParity
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryExtensionClass

/-!
# Padé contact parity for shifted Xi Hankel faces

This module specializes the finite-Hankel Padé normal coordinates to the shifted reciprocal moments
of Xi.  In the zero-free window these defects are exactly the completed prime--archimedean defects.
At first contact, the linear Möbius coefficient is the negative of the existing Route-U monic
remainder, with the positive factor `2n+1`.
-/

open Matrix Polynomial

namespace RHTower

noncomputable section

/-- Difference between the shifted-Xi moments and the canonical flat atomic shadow. -/
def xiShiftedHankelBoundaryPadeDefect
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  HTGeometry.finiteHankelBoundaryPadeDefect
    (fun j => (xiShiftedReciprocalMoment y j).re) c k

/-- Source-side form of the same flat-shadow defect. -/
def primeArchShiftedHankelBoundaryPadeDefect
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  HTGeometry.finiteHankelBoundaryPadeDefect
    (fun j => (primeArchShiftedReciprocalMoment y j).re) c k

/-- In the local zero-free window, Xi and completed prime--archimedean Padé defects agree. -/
theorem xiShiftedHankelBoundaryPadeDefect_eq_primeArch
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) :
    xiShiftedHankelBoundaryPadeDefect y c k =
      primeArchShiftedHankelBoundaryPadeDefect y c k := by
  have hseq : (fun j => (xiShiftedReciprocalMoment y j).re) =
      (fun j => (primeArchShiftedReciprocalMoment y j).re) := by
    funext j
    rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy hymax]
  simp only [xiShiftedHankelBoundaryPadeDefect,
    primeArchShiftedHankelBoundaryPadeDefect, hseq]

/-- Flatness annihilates every shifted-Xi defect visible to the singular Hankel face. -/
theorem xiShiftedHankelBoundaryPadeDefect_eq_zero_of_le
    {y : ℝ} {n k : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (hk : k ≤ 2 * n) :
    xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
  exact HTGeometry.finiteHankelBoundaryPadeDefect_eq_zero_of_le
    c hhead hc hlast hk

/-- The first shifted-Xi Padé defect is the Route-U monic remainder. -/
theorem xiShiftedHankelBoundaryPadeDefect_first_eq_monicRemainder
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    xiShiftedHankelBoundaryPadeDefect y c (2 * n + 1) =
      xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.finiteHankelBoundaryPadeDefect_first_eq_monicRemainder
    (fun j => (xiShiftedReciprocalMoment y j).re) c hhead hc hlast

/-- The order-one contact coefficient is `-(2n+1)` times the Route-U remainder. -/
theorem xiShiftedHankelBoundaryContactSeries_coeff_one
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    PowerSeries.coeff 1
        (HTGeometry.mobiusPadeContactSeries
          (xiShiftedHankelBoundaryPadeDefect y c)
          (HTGeometry.finiteHankelNullMonicPolynomial c) n) =
      -((2 * n + 1 : ℕ) : ℝ) * xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.finiteHankelBoundaryContactSeries_coeff_one c hhead hc hlast

/-- Any completed source law with the opposite alternating defect sign excludes positive Padé
contact orientation.  This is the source-side consumer needed by the higher-contact Route-U pivot. -/
theorem not_xiShiftedHankelBoundaryContactCoefficient_pos_of_primeArch_opposite
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    {n d : ℕ} (c : Fin (n + 1) → ℝ) (hd : 0 < d)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + d,
      primeArchShiftedHankelBoundaryPadeDefect y c k = 0)
    (hsource : (-1 : ℝ) ^ d *
      primeArchShiftedHankelBoundaryPadeDefect y c (2 * n + d) < 0) :
    ¬ 0 < PowerSeries.coeff d
      (HTGeometry.mobiusPadeContactSeries
        (xiShiftedHankelBoundaryPadeDefect y c)
        (HTGeometry.finiteHankelNullMonicPolynomial c) n) := by
  have hseq : xiShiftedHankelBoundaryPadeDefect y c =
      primeArchShiftedHankelBoundaryPadeDefect y c := by
    funext k
    exact xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy hymax c k
  rw [hseq]
  exact HTGeometry.not_contactCoefficient_pos_of_source_opposite
    (HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast)
    (HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast)
    hd hzero hsource

end

end RHTower
