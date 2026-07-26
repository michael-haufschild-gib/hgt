import GaloisForLFunctions.RHTower.XiSafeHalfPlaneJacobiGammaRecovery
import GaloisForLFunctions.RHTower.XiTransversePrimeSourceProjectiveTangent

/-!
# Safe Jacobi--Gamma projective-contact universality

The actual valuation-zero boundary outputs of the safe Jacobi--Gamma recovery carry the
projective contact filtration of the transverse Xi source.  Ratios of two integral-aperture
increments forget the real base aperture exactly.  Over the cofinite prime boundary they collapse
to one projective ray, while the first nonzero defect has contact grade `min a b` and remembers
the order of the increments.
-/

namespace RHTower

open Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Actual valuation-zero boundary coordinate produced by the safe Jacobi--Gamma source map. -/
def xiSafeHalfPlaneRecoveredBoundaryCoordinate
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  xiSafeHalfPlaneJacobiGammaRecovery x
    (gammaSewnMobiusPascalNormalizedRay x)
    (fun q => Real.log (q : ℝ) *
      xiTransversePrimeHalfShiftedFirstValuationCoordinate q)
    p 0

/-- Complexified change of the recovered boundary coordinate under an integral aperture shift. -/
def xiSafeHalfPlaneRecoveredBoundaryIncrement
    (x : ℝ) (a : ℕ) (p : Nat.Primes) : ℂ :=
  ((xiSafeHalfPlaneRecoveredBoundaryCoordinate x p -
    xiSafeHalfPlaneRecoveredBoundaryCoordinate (x + (a : ℝ)) p : ℝ) : ℂ)

/-- The actual recovered increment is a common nonzero base-aperture weight times the transverse
Xi-shift source. -/
theorem xiSafeHalfPlaneRecoveredBoundaryIncrement_eq_transverseSource
    {x : ℝ} (hx : 1 / 2 ≤ x) (a : ℕ) (p : Nat.Primes) :
    xiSafeHalfPlaneRecoveredBoundaryIncrement x a p =
      (xiMobiusContinuousApertureDiskNode x p : ℂ) *
        xiTransverseShiftArithmetic a p := by
  have hxa : 1 / 2 ≤ x + (a : ℝ) := by
    exact hx.trans (le_add_of_nonneg_right (Nat.cast_nonneg a))
  simp only [xiSafeHalfPlaneRecoveredBoundaryIncrement,
    xiSafeHalfPlaneRecoveredBoundaryCoordinate]
  rw [
    xiSafeHalfPlaneJacobiGammaRecovery_eq_coefficient hx,
    xiSafeHalfPlaneJacobiGammaRecovery_eq_coefficient hxa]
  exact xiSafeHalfPlanePrimeCoefficient_sub_natShift_eq_transverseSource x a p

/-- **Safe Jacobi--Gamma projective ratio law.**  The ratio of two positive recovered aperture
increments is independent of the base aperture and equals the transverse Xi-source ratio. -/
theorem xiSafeHalfPlaneRecoveredBoundaryIncrement_ratio_eq
    {x : ℝ} (hx : 1 / 2 ≤ x) (a b : ℕ) (hb : 0 < b) (p : Nat.Primes) :
    xiSafeHalfPlaneRecoveredBoundaryIncrement x a p /
        xiSafeHalfPlaneRecoveredBoundaryIncrement x b p =
      xiTransversePrimeApertureRatio a b p := by
  rw [xiSafeHalfPlaneRecoveredBoundaryIncrement_eq_transverseSource hx,
    xiSafeHalfPlaneRecoveredBoundaryIncrement_eq_transverseSource hx,
    xiTransversePrimeApertureRatio_eq_source_ratio a b hb p]
  have hnode :
      (xiMobiusContinuousApertureDiskNode x p : ℂ) ≠ 0 := by
    exact_mod_cast (xiMobiusContinuousApertureDiskNode_pos x p).ne'
  have hsource : xiTransverseShiftArithmetic b p ≠ 0 := by
    have h := xiTransverseShiftArithmetic_primePow_ne_zero b hb p 0
    simpa using h
  field_simp [hnode, hsource]

/-- All positive recovered aperture-increment columns collapse to one cofinite-prime projective
ray, uniformly in the safe base aperture. -/
theorem tendsto_xiSafeHalfPlaneRecoveredBoundaryIncrement_ratio_cofinite_one
    {x : ℝ} (hx : 1 / 2 ≤ x) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun p : Nat.Primes =>
      xiSafeHalfPlaneRecoveredBoundaryIncrement x a p /
        xiSafeHalfPlaneRecoveredBoundaryIncrement x b p) cofinite (𝓝 1) := by
  simpa only [xiSafeHalfPlaneRecoveredBoundaryIncrement_ratio_eq hx a b hb] using
    tendsto_xiTransversePrimeApertureRatio_cofinite_one a b ha hb

/-- **Safe Jacobi--Gamma projective-contact universality.**  Distinct positive recovered
increment columns first separate at grade `min a b`; the limiting sign records which increment
is smaller. -/
theorem tendsto_xiSafeHalfPlaneRecoveredBoundaryIncrement_firstDefect
    {x : ℝ} (hx : 1 / 2 ≤ x) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    Tendsto (fun p : Nat.Primes =>
      (xiSafeHalfPlaneRecoveredBoundaryIncrement x a p /
          xiSafeHalfPlaneRecoveredBoundaryIncrement x b p - 1) /
        primeShiftFactor ((min a b : ℕ) : ℂ) p) cofinite
      (𝓝 (if a < b then (-1 : ℂ) else 1)) := by
  simpa only [xiSafeHalfPlaneRecoveredBoundaryIncrement_ratio_eq hx a b hb] using
    tendsto_xiTransversePrimeApertureRatio_firstDefect ha hb hne

end

end RHTower
