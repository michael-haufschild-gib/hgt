import GaloisForLFunctions.HTGeometry.QuadraticContactPickObstruction
import GaloisForLFunctions.RHTower.GammaSewnMobiusValuationContraction

/-!
# Gamma-sewn Möbius scalar Pick obstruction

The Gamma-sewn Möbius valuation multiplier is positive and strictly below one at every positive
aperture, but it reaches the lossless zero-aperture boundary quadratically.  This module applies
the universal quadratic-contact theorem to prove that the scalar sewing is not contractive on
aperture packets: against every fixed positive aperture, all sufficiently small positive
apertures give a negative two-point defect determinant.

The last theorem identifies this normalized determinant with the determinant of the actual
fixed-prime Möbius valuation Gram loss by a positive diagonal congruence.  Thus the obstruction
acts on the source Gram itself, before any Xi divisor or cofinal limit is introduced.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The Gamma-sewn normalized two-aperture Pick determinant at one fixed prime. -/
def gammaSewnMobiusPickTwoPointDeterminant
    (x y : ℝ) (p : Nat.Primes) : ℝ :=
  HTGeometry.pickTwoPointDeterminant
    (gammaSewnMobiusValuationContractionMultiplier x p)
    (xiMobiusContinuousApertureDiskNode x p)
    (gammaSewnMobiusValuationContractionMultiplier y p)
    (xiMobiusContinuousApertureDiskNode y p)

/-- Exact quadratic contact makes the normalized moving diagonal Pick defect vanish at the
lossless aperture boundary. -/
theorem tendsto_gammaSewnMobius_pickDiagonalDefect_nhdsGT_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ => HTGeometry.pickDiagonalDefect
        (gammaSewnMobiusValuationContractionMultiplier x p)
        (xiMobiusContinuousApertureDiskNode x p))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
  let q : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
  let c : ℝ → ℝ := fun x => gammaSewnMobiusValuationContractionMultiplier x p
  let g : ℝ → ℝ := fun x => gammaSewnMobiusValuationQuadraticDefectGain x p
  change Tendsto (fun x : ℝ => HTGeometry.pickDiagonalDefect (c x) (q x))
    (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0)
  have heq : ∀ x : ℝ, 0 < x →
      HTGeometry.pickDiagonalDefect (c x) (q x) =
        (1 - q x) * g x * (1 + c x) / (1 + q x) := by
    intro x hx
    have hq_lt : q x < 1 :=
      xiMobiusContinuousApertureDiskNode_lt_one hx p
    have hq_sub : 1 - q x ≠ 0 := sub_ne_zero.mpr hq_lt.ne'
    rw [HTGeometry.pickDiagonalDefect,
      show 1 - c x ^ 2 = (1 - c x) * (1 + c x) by ring,
      show 1 - q x ^ 2 = (1 - q x) * (1 + q x) by ring]
    rw [show 1 - c x = (1 - q x) ^ 2 * g x by
      simpa only [c, q, g] using
        one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain x p]
    field_simp [hq_sub]
  have hqcont : ContinuousAt q 0 := by
    dsimp only [q, xiMobiusContinuousApertureDiskNode]
    fun_prop
  have hccont : ContinuousAt c 0 := by
    simpa only [c] using
      continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p
  have hgcont : ContinuousAt g 0 := by
    change ContinuousAt (fun x : ℝ =>
      (7 * q x ^ 2 + 10 * q x + 7) /
        (8 * (1 + q x ^ 4) * (1 + c x) * (1 + c x ^ 2))) 0
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · have hqzero : q 0 = 1 := by simp [q]
      have hczero : c 0 = 1 := by
        simp [c, gammaSewnMobiusValuationContractionMultiplier_zero]
      rw [hqzero, hczero]
      norm_num
  have hcont : ContinuousAt
      (fun x : ℝ => (1 - q x) * g x * (1 + c x) / (1 + q x)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp [q]
  have ht : Tendsto
      (fun x : ℝ => (1 - q x) * g x * (1 + c x) / (1 + q x))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 ((fun x : ℝ => (1 - q x) * g x * (1 + c x) / (1 + q x)) 0)) :=
    hcont.continuousWithinAt.tendsto
  have hval :
      (fun x : ℝ => (1 - q x) * g x * (1 + c x) / (1 + q x)) 0 = 0 := by
    simp [q, c, gammaSewnMobiusValuationContractionMultiplier_zero]
  rw [hval] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (heq x hx).symm

/-- Scalar Gamma sewing is not Pick-contractive across apertures: against every fixed positive
aperture, all sufficiently small positive apertures give a negative two-point determinant. -/
theorem eventually_gammaSewnMobiusPickTwoPointDeterminant_neg
    {x₀ : ℝ} (hx₀ : 0 < x₀) (p : Nat.Primes) :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi 0),
      gammaSewnMobiusPickTwoPointDeterminant x₀ x p < 0 := by
  let c : ℝ → ℝ := fun x => gammaSewnMobiusValuationContractionMultiplier x p
  let q : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
  have hc : Tendsto c (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 1) := by
    have h : Tendsto
        (fun x : ℝ => gammaSewnMobiusValuationContractionMultiplier x p)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (𝓝 (gammaSewnMobiusValuationContractionMultiplier 0 p)) :=
      (continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p).continuousWithinAt.tendsto
    simpa only [c, gammaSewnMobiusValuationContractionMultiplier_zero] using h
  have hq : Tendsto q (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 1) := by
    have hcont : ContinuousAt q 0 := by
      dsimp only [q, xiMobiusContinuousApertureDiskNode]
      fun_prop
    have h : Tendsto q (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (q 0)) :=
      hcont.continuousWithinAt.tendsto
    simpa only [q, xiMobiusContinuousApertureDiskNode_zero] using h
  have hdiag : Tendsto (fun x => HTGeometry.pickDiagonalDefect (c x) (q x))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
    simpa only [c, q] using
      tendsto_gammaSewnMobius_pickDiagonalDefect_nhdsGT_zero p
  have hc₀ : c x₀ ≠ 1 :=
    (gammaSewnMobiusValuationContractionMultiplier_lt_one hx₀ p).ne
  have hq₀ : q x₀ ≠ 1 :=
    (xiMobiusContinuousApertureDiskNode_lt_one hx₀ p).ne
  have hneg := HTGeometry.eventually_pickTwoPointDeterminant_neg_of_boundaryContact
    c q (c x₀) (q x₀) hc hq hdiag hc₀ hq₀
  simpa only [gammaSewnMobiusPickTwoPointDeterminant, c, q] using hneg

/-- Fixed-prime aperture Gram lost under scalar Gamma sewing. -/
def gammaSewnMobiusApertureCrossDefect
    (x y : ℝ) (p : Nat.Primes) : ℝ :=
  let cx := gammaSewnMobiusValuationContractionMultiplier x p
  let cy := gammaSewnMobiusValuationContractionMultiplier y p
  (1 - cx * cy) * xiMobiusPrimeContinuousApertureSzegoMetric x y p

/-- Two-aperture determinant of the actual fixed-prime Gram loss. -/
def gammaSewnMobiusApertureCrossDefectDeterminant
    (x y : ℝ) (p : Nat.Primes) : ℝ :=
  gammaSewnMobiusApertureCrossDefect x x p *
      gammaSewnMobiusApertureCrossDefect y y p -
    gammaSewnMobiusApertureCrossDefect x y p ^ 2

/-- Positive diagonal congruence identifies the actual Gram-loss determinant with the normalized
Pick determinant. -/
theorem gammaSewnMobiusApertureCrossDefectDeterminant_eq
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (p : Nat.Primes) :
    gammaSewnMobiusApertureCrossDefectDeterminant x y p =
      (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 4 *
        (1 - xiMobiusContinuousApertureDiskNode x p) ^ 2 *
        (1 - xiMobiusContinuousApertureDiskNode y p) ^ 2 *
        gammaSewnMobiusPickTwoPointDeterminant x y p := by
  let qx := xiMobiusContinuousApertureDiskNode x p
  let qy := xiMobiusContinuousApertureDiskNode y p
  have hqx0 : 0 < qx := xiMobiusContinuousApertureDiskNode_pos x p
  have hqy0 : 0 < qy := xiMobiusContinuousApertureDiskNode_pos y p
  have hqx1 : qx < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hqy1 : qy < 1 := xiMobiusContinuousApertureDiskNode_lt_one hy p
  have hxx : 1 - qx * qx ≠ 0 := by nlinarith
  have hyy : 1 - qy * qy ≠ 0 := by nlinarith
  have hxy : 1 - qx * qy ≠ 0 := by
    have hprod : qx * qy < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hqx0.le hqx1 hqy1.le
    linarith
  simp only [gammaSewnMobiusApertureCrossDefectDeterminant,
    gammaSewnMobiusApertureCrossDefect,
    xiMobiusPrimeContinuousApertureSzegoMetric,
    gammaSewnMobiusPickTwoPointDeterminant,
    HTGeometry.pickTwoPointDeterminant, HTGeometry.pickDiagonalDefect,
    HTGeometry.pickCrossDefect]
  field_simp [hxx, hyy, hxy]

/-- The actual fixed-prime aperture Gram loss is indefinite on every neighborhood of the
lossless boundary. -/
theorem eventually_gammaSewnMobiusApertureCrossDefectDeterminant_neg
    {x₀ : ℝ} (hx₀ : 0 < x₀) (p : Nat.Primes) :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi 0),
      gammaSewnMobiusApertureCrossDefectDeterminant x₀ x p < 0 := by
  filter_upwards
    [eventually_gammaSewnMobiusPickTwoPointDeterminant_neg hx₀ p,
      self_mem_nhdsWithin] with x hpick hx
  rw [gammaSewnMobiusApertureCrossDefectDeterminant_eq hx₀ hx p]
  have hnode : 0 < xiTransversePrimeApertureDiskNode 1 p :=
    xiTransversePrimeApertureDiskNode_pos 1 p
  have hqx := xiMobiusContinuousApertureDiskNode_lt_one hx₀ p
  have hqy := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hscale : 0 <
      (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 4 *
        (1 - xiMobiusContinuousApertureDiskNode x₀ p) ^ 2 *
        (1 - xiMobiusContinuousApertureDiskNode x p) ^ 2 := by
    positivity
  exact mul_neg_of_pos_of_neg hscale hpick

end

end RHTower
