import GaloisForLFunctions.RHTower.XiStrictSchwarzSixthSpectralCeiling
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminants
import GaloisForLFunctions.RHTower.PrimeLagLandauCriterion
import GaloisForLFunctions.RHTower.XiWallLogDerivativeCones
import GaloisForLFunctions.RHTower.TwistedArcN1Reduction
import GaloisForLFunctions.RHTower.TwistedArcMinimumPrincipleProof
import GaloisForLFunctions.RHTower.XiEndpointQuantitativeNormBudget
import GaloisForLFunctions.RHTower.XiEndpointCompletedValueBound
import GaloisForLFunctions.RHTower.XiEndpointCompletedValue

/-!
# Xi zero copies, the twisted arc and the endpoint curvature: discharged premises

Lemmas stated under an input that the corpus proves elsewhere:

* `[Infinite XiZeroCopy]` — `infinite_xiZeroCopy` (infinitely many nontrivial zeros);
* `[Nonempty XiZeroCopy]` — `exists_xiZeroCopy`;
* `TwistedArcMinimumPrinciple` — `twistedArcMinimumPrinciple_holds`;
* `xiEndpointCompletedCurvature < 1` — `xiEndpointCompletedCurvature_lt_one`.
-/

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Infinitely many zero copies -/

/-- A strictly positive, conjugation-invariant summable weight on the Xi divisor has strictly more
total mass than any Schwarz pair `{q, q̄}`. -/
theorem two_mul_lt_tsum_of_conj_invariant_unconditional
    {f : XiZeroCopy → ℝ} (hpos : ∀ r, 0 < f r) (hsum : Summable f)
    (hCinv : ∀ r, f (xiZeroCopyConjEquiv r) = f r) (q : XiZeroCopy) :
    2 * f q < ∑' r, f r :=
  haveI := infinite_xiZeroCopy
  two_mul_lt_tsum_of_conj_invariant hpos hsum hCinv q

/-- Strict Hölder sixth spectral ceiling `2 (Σ b)² < (Σ a)³` for positive spectral coordinates
with `b² ≤ a³` atomwise and `a` conjugation invariant. -/
theorem strict_sixth_spectral_ceiling_of_schwarz_atoms_unconditional
    {a b : XiZeroCopy → ℝ}
    (ha : ∀ q, 0 < a q) (hb : ∀ q, 0 < b q)
    (hab : ∀ q, b q ^ 2 ≤ a q ^ 3)
    (hsa : Summable a) (hsa2 : Summable (fun q => a q ^ 2))
    (hainv : ∀ q, a (xiZeroCopyConjEquiv q) = a q) :
    2 * (∑' q, b q) ^ 2 < (∑' q, a q) ^ 3 :=
  haveI := infinite_xiZeroCopy
  strict_sixth_spectral_ceiling_of_schwarz_atoms ha hb hab hsa hsa2 hainv

/-! ## Existence of a zero copy -/

/-- `zeroReSup ≤ θ` as soon as every zero copy has real part at most `θ`. -/
theorem zeroReSup_le_unconditional {θ : ℝ} (h : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) :
    zeroReSup ≤ θ :=
  haveI := exists_xiZeroCopy
  zeroReSup_le h

/-- Below `zeroReSup` there is a zero copy with larger real part. -/
theorem exists_re_gt_of_lt_zeroReSup_unconditional {b : ℝ} (hb : b < zeroReSup) :
    ∃ q : XiZeroCopy, b < (q.1 : ℂ).re :=
  haveI := exists_xiZeroCopy
  exists_re_gt_of_lt_zeroReSup hb

/-! ## The twisted arc minimum principle -/

/-- For every `N` and `δ > 0` some probability measure on the arc makes the first `N` twisted
moments `δ`-small. -/
theorem exists_probabilityMeasure_twArc_small_unconditional (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ μ : ProbabilityMeasure ArcParam, ∀ n < N,
      |∫ u, twArcMomentBCF n u ∂(μ : Measure ArcParam)| ≤ δ :=
  exists_probabilityMeasure_twArc_small twistedArcMinimumPrinciple_holds N hδ

/-- A probability measure on the arc annihilates every twisted moment. -/
theorem exists_probabilityMeasure_twArc_annihilating_unconditional :
    ∃ μ : ProbabilityMeasure ArcParam, ∀ n : ℕ,
      ∫ u, twArcMoment n u ∂(μ : Measure ArcParam) = 0 :=
  exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds

/-! ## Endpoint curvature below one -/

/-- Defect-to-cross-term estimate at every zero copy, with factor `κ/(1−κ)` for the endpoint
curvature `κ < 1`. -/
theorem endpoint_defect_term_le_source_factor_cross_unconditional (q : XiZeroCopy) :
    ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ (2 : ℕ) ≤
      (xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature)) *
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re :=
  endpoint_defect_term_le_source_factor_cross xiEndpointCompletedCurvature_lt_one q

/-- The completed zeta function without poles has real part below `1/2` at the origin. -/
theorem completedRiemannZeta₀_zero_re_lt_half : (completedRiemannZeta₀ 0).re < 1 / 2 :=
  xiEndpointCompletedCurvature_lt_one_iff_completedRiemannZeta0_re_lt_half.mp
    xiEndpointCompletedCurvature_lt_one

end

end RHTower
