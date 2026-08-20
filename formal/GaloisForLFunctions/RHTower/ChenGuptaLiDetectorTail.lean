/-
# Chen--Gupta--Li finite detector tail

This module turns the finite-times-full Dirichlet convolution underlying
`M_X(s, χ)L(s, χ)` into an exact `1 + tail` identity in the certified
absolute-convergence half-plane.  It also proves algebraically that the tail
has no coefficient through the literal cutoff.  The critical-strip contour
argument required to evaluate that tail at an L-function zero is deliberately
not asserted here.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiAnalyticAnchor

open Complex LSeries DirichletCharacter

noncomputable section

namespace RHTower

/-- The Dirichlet-series unit coefficient function. -/
def cglUnitCoefficient (n : ℕ) : ℂ := if n = 1 then 1 else 0

/-- Coefficients of the tail after removing the unit term from the full finite
detector product. -/
def cglDetectorTailCoefficient (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (n : ℕ) : ℂ :=
  LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) n -
    cglUnitCoefficient n

/-- The full finite detector convolution is the unit coefficient function plus
its literal tail, coefficient by coefficient. -/
theorem cglTruncatedMobiusTwist_convolution_eq_unit_add_tail
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (n : ℕ) :
    LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) n =
      cglUnitCoefficient n + cglDetectorTailCoefficient X q χ n := by
  unfold cglDetectorTailCoefficient cglUnitCoefficient
  ring

/-- The detector tail has zero unit coefficient. -/
theorem cglDetectorTailCoefficient_one
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) :
    cglDetectorTailCoefficient X q χ 1 = 0 := by
  unfold cglDetectorTailCoefficient cglUnitCoefficient
  rw [cglTruncatedMobiusTwist_convolution_character_one]
  norm_num

/-- Every tail coefficient represented by `n + 2` for `n : Fin X` vanishes.
Thus the tail begins strictly after the detector cutoff without an externally
supplied range premise. -/
theorem cglDetectorTailCoefficient_vanishes_below_cutoff
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (n : Fin X) :
    cglDetectorTailCoefficient X q χ (n.1 + 2) = 0 := by
  unfold cglDetectorTailCoefficient cglUnitCoefficient
  rw [cglTruncatedMobiusTwist_convolution_character_vanishes_below_cutoff]
  have hne : n.1 + 2 ≠ 1 := by omega
  rw [if_neg hne]
  norm_num

/-- The L-series of the unit coefficient function is summable everywhere. -/
theorem lseriesSummable_cglUnitCoefficient (s : ℂ) :
    LSeriesSummable cglUnitCoefficient s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  apply Set.Finite.subset (Finset.finite_toSet {1})
  intro n hn
  simp only [Function.mem_support] at hn
  simp only [Finset.mem_coe, Finset.mem_singleton]
  by_contra hne
  rw [LSeries.term] at hn
  by_cases hn0 : n = 0
  · simp [hn0] at hn
  · simp [hn0, cglUnitCoefficient, hne] at hn

/-- The L-series of the unit coefficient function equals one at every complex
point. -/
theorem lseries_cglUnitCoefficient (s : ℂ) :
    LSeries cglUnitCoefficient s = 1 := by
  unfold LSeries
  rw [tsum_eq_sum (s := {1})]
  · rw [Finset.sum_singleton, LSeries.term_of_ne_zero one_ne_zero]
    simp [cglUnitCoefficient]
  · intro n hn
    have hne1 : n ≠ 1 := by
      intro hn1
      apply hn
      simp [hn1]
    rw [LSeries.term]
    split_ifs with hn0
    · rfl
    · simp [cglUnitCoefficient, hne1]

/-- In the certified absolute-convergence half-plane, the detector-tail
L-series is summable. -/
theorem lseriesSummable_cglDetectorTailCoefficient (X q : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLAbsoluteConvergencePoint) :
    LSeriesSummable (cglDetectorTailCoefficient X q χ) s.1 := by
  unfold cglDetectorTailCoefficient
  exact (lseriesSummable_cglTruncatedMobiusTwist X (q + 1) χ s.1).convolution
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ s.2) |>.sub
      (lseriesSummable_cglUnitCoefficient s.1)

/-- The L-series of the literal detector tail is the finite detector product
minus one throughout the certified absolute-convergence half-plane. -/
theorem lseries_cglDetectorTailCoefficient (X q : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLAbsoluteConvergencePoint) :
    LSeries (cglDetectorTailCoefficient X q χ) s.1 =
      zeroDetectionMobiusPolynomial X (q + 1) χ s.1 * DirichletCharacter.LFunction χ s.1 - 1 := by
  let hconv : LSeriesSummable
      (LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m)) s.1 :=
    (lseriesSummable_cglTruncatedMobiusTwist X (q + 1) χ s.1).convolution
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ s.2)
  calc
    LSeries (cglDetectorTailCoefficient X q χ) s.1 =
        LSeries (LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ)
          (fun m : ℕ => χ m)) s.1 - LSeries cglUnitCoefficient s.1 := by
      exact LSeries_sub hconv (lseriesSummable_cglUnitCoefficient s.1)
    _ = LSeries (LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ)
          (fun m : ℕ => χ m)) s.1 - 1 := by
      rw [lseries_cglUnitCoefficient]
    _ = zeroDetectionMobiusPolynomial X (q + 1) χ s.1 * DirichletCharacter.LFunction χ s.1 - 1 := by
      rw [zeroDetectionMobiusPolynomial_mul_lfunction_eq_convolutionLSeries]

/-- The exact detector product is one plus the literal tail throughout the
certified absolute-convergence half-plane. -/
theorem zeroDetectionMobiusPolynomial_mul_lfunction_eq_one_add_tail
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (s : CGLAbsoluteConvergencePoint) :
    zeroDetectionMobiusPolynomial X (q + 1) χ s.1 * DirichletCharacter.LFunction χ s.1 =
      1 + LSeries (cglDetectorTailCoefficient X q χ) s.1 := by
  rw [lseries_cglDetectorTailCoefficient]
  ring

end RHTower
