import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weighted radial primitives from the Navier--Stokes construction

This file formalizes the exact scalar, auxiliary-independent core of Lemma 8.2 and
equations (8.6)--(8.7) in the supplied Navier--Stokes paper.  Dividing a corrected
primitive by a nonvanishing radial weight gives a right inverse to the associated
weighted radial derivative, up to the explicitly isolated cutoff remainder.

The paper needs the weights `r ^ e` for `e ∈ {0, 1, 2}`.  The statements below prove
the identity for every natural exponent and, first, for an arbitrary differentiable
nonvanishing weight.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Primitive based at the cylindrical axis. -/
def radialPrimitive (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r, g s

/-- Subtract a cutoff multiple of the total moment from a radial primitive. -/
def cutoffRadialPrimitive (g cutoff : ℝ → ℝ) (total r : ℝ) : ℝ :=
  radialPrimitive g r - cutoff r * total

/-- Corrected primitive divided by its radial weight. -/
def weightedRadialInverse (weight source cutoff : ℝ → ℝ) (total r : ℝ) : ℝ :=
  cutoffRadialPrimitive (fun s => weight s * source s) cutoff total r / weight r

/-- Weighted radial derivative `D_weight = d/dr + (weight'/weight)`. -/
def weightedRadialOperator (weight field : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv field r + deriv weight r / weight r * field r

/-- Error introduced by subtracting the cutoff multiple of the full moment. -/
def weightedCutoffRemainder (weight cutoff : ℝ → ℝ) (total r : ℝ) : ℝ :=
  deriv cutoff r * total / weight r

theorem radialPrimitive_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (r : ℝ) :
    HasDerivAt (radialPrimitive g) (g r) r := by
  exact intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 r)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem weightedRadialInverse_hasDerivAt
    {weight source cutoff : ℝ → ℝ} {total r : ℝ}
    (hweight : DifferentiableAt ℝ weight r) (hsource : Continuous source)
    (hweightContinuous : Continuous weight) (hcutoff : DifferentiableAt ℝ cutoff r)
    (hweightNe : weight r ≠ 0) :
    HasDerivAt (weightedRadialInverse weight source cutoff total)
      (source r - deriv weight r / weight r *
          weightedRadialInverse weight source cutoff total r -
        weightedCutoffRemainder weight cutoff total r) r := by
  have hproduct : Continuous (fun s => weight s * source s) :=
    hweightContinuous.mul hsource
  have hprimitive := radialPrimitive_hasDerivAt hproduct r
  have hcut : HasDerivAt
      (cutoffRadialPrimitive (fun s => weight s * source s) cutoff total)
      (weight r * source r - deriv cutoff r * total) r := by
    exact hprimitive.sub (hcutoff.hasDerivAt.mul_const total)
  have hquot := hcut.div hweight.hasDerivAt hweightNe
  apply hquot.congr_deriv
  simp only [weightedRadialInverse, weightedCutoffRemainder]
  field_simp [hweightNe]
  ring

/-- Arbitrary-weight form of the paper's exact identity `D_e T_e f = f - A_e f`. -/
theorem weightedRadialOperator_weightedRadialInverse
    {weight source cutoff : ℝ → ℝ} {total r : ℝ}
    (hweight : DifferentiableAt ℝ weight r) (hsource : Continuous source)
    (hweightContinuous : Continuous weight) (hcutoff : DifferentiableAt ℝ cutoff r)
    (hweightNe : weight r ≠ 0) :
    weightedRadialOperator weight (weightedRadialInverse weight source cutoff total) r =
      source r - weightedCutoffRemainder weight cutoff total r := by
  rw [weightedRadialOperator,
    (weightedRadialInverse_hasDerivAt hweight hsource hweightContinuous hcutoff hweightNe).deriv]
  ring

/-- The monomial cylindrical weights used in Lemma 8.2. -/
def powerWeight (e : ℕ) (r : ℝ) : ℝ := r ^ e

theorem weightedRadialOperator_powerWeight (e : ℕ) (field : ℝ → ℝ) {r : ℝ}
    (hr : r ≠ 0) :
    weightedRadialOperator (powerWeight e) field r =
      deriv field r + (e : ℝ) / r * field r := by
  change deriv field r + deriv (fun x : ℝ => x ^ e) r / r ^ e * field r = _
  rw [deriv_pow_field]
  by_cases he : e = 0
  · subst e
    simp
  · have hpowSucc : r ^ e = r ^ (e - 1) * r := by
      nth_rewrite 1 [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]
      exact pow_succ r (e - 1)
    rw [hpowSucc]
    field_simp [hr]

/-- Equation (8.7), generalized from the paper's three exponents to every natural exponent. -/
theorem powerWeightedRadialInverse_operator (e : ℕ)
    {source cutoff : ℝ → ℝ} {total r : ℝ}
    (hsource : Continuous source) (hcutoff : DifferentiableAt ℝ cutoff r)
    (hr : r ≠ 0) :
    deriv (weightedRadialInverse (powerWeight e) source cutoff total) r +
        (e : ℝ) / r * weightedRadialInverse (powerWeight e) source cutoff total r =
      source r - weightedCutoffRemainder (powerWeight e) cutoff total r := by
  rw [← weightedRadialOperator_powerWeight e _ hr]
  apply weightedRadialOperator_weightedRadialInverse
  · exact ((hasDerivAt_id r).pow e).differentiableAt
  · exact hsource
  · exact continuous_id.pow e
  · exact hcutoff
  · simp [powerWeight, hr]

/-- In the zero-moment case, the cutoff is algebraically invisible and the inverse is exact. -/
theorem powerWeightedRadialInverse_operator_of_total_eq_zero (e : ℕ)
    {source cutoff : ℝ → ℝ} {total r : ℝ}
    (hsource : Continuous source) (hcutoff : DifferentiableAt ℝ cutoff r)
    (hr : r ≠ 0) (htotal : total = 0) :
    deriv (weightedRadialInverse (powerWeight e) source cutoff total) r +
        (e : ℝ) / r * weightedRadialInverse (powerWeight e) source cutoff total r =
      source r := by
  rw [powerWeightedRadialInverse_operator e hsource hcutoff hr, htotal]
  simp [weightedCutoffRemainder]

end

end GaloisForLFunctions.HTGeometry
