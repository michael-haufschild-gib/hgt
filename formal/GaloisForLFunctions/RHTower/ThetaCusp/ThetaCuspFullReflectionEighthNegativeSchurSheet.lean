import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthSchurTail

/-!
# Negative Schur sheet for complete-theta rank-three curvature

The strict Schur diagonals reduce native rank-three curvature to one quadratic cone.  The
complete theta source lies on only one of its two sheets: its sixth-jet coupling is strictly
negative on the entire physical half-line.  Consequently every singular face has a unique
positive sheet coordinate.

This is the sheet-selection input for a source-specific normal-flow argument.  The remaining
chain is: inward orientation on this unique negative sheet -> strict native `D1` -> finite
TCD/S6F gate -> cofinal Hankel/Bezoutian landing -> Weil positivity -> RH.
-/

open Real

namespace RHTower

noncomputable section

/-- Positive coordinate on the physical Schur sheet. -/
def thetaCuspFullReflectionEighthNegativeSchurCoordinate (x : ℝ) : ℝ :=
  64 * thetaCuspFullReflectedLogCurvature x ^ (3 : ℕ) -
    thetaCuspFullReflectedLogSixthJet x

/-- The actual complete-theta sixth-jet Schur coupling is globally strictly negative.  Thus the
positive correlation sheet is absent, independently of rank-three positivity. -/
theorem thetaCuspFullReflectionEighthSchurCoupling_neg
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspReflectedEighthSchurCoupling
      (thetaCuspFullReflectedLogCurvature x)
      (thetaCuspFullReflectedLogSixthJet x) < 0 := by
  have hcoef := thetaCuspFullReflectionEighthSixthLossCoefficient_pos hx
  have he6 := thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx
  unfold thetaCuspReflectedEighthSchurCoupling
    thetaCuspFullReflectedLogSixthJet
  linarith

/-- The negative-sheet coordinate is globally strict. -/
theorem thetaCuspFullReflectionEighthNegativeSchurCoordinate_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspFullReflectionEighthNegativeSchurCoordinate x := by
  have hJ := thetaCuspFullReflectionEighthSchurCoupling_neg hx
  unfold thetaCuspReflectedEighthSchurCoupling at hJ
  unfold thetaCuspFullReflectionEighthNegativeSchurCoordinate
  linarith

/-- Exact normal form on the selected physical sheet. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_eq_negativeSchurNormalForm
    (x : ℝ) :
    thetaCuspFullReflectionEighthHankelCurvature x =
      thetaCuspReflectedEighthSchurHead
          (thetaCuspFullReflectedLogCurvature x)
          (thetaCuspFullReflectedLogFourthJet x) *
        thetaCuspReflectedEighthSchurTail
          (thetaCuspFullReflectedLogCurvature x)
          (thetaCuspFullReflectedLogFourthJet x)
          (thetaCuspFullReflectedLogEighthJet x) -
      thetaCuspFullReflectionEighthNegativeSchurCoordinate x ^ (2 : ℕ) := by
  rw [show thetaCuspFullReflectionEighthHankelCurvature x =
      thetaCuspReflectedEighthPolynomial
        (thetaCuspFullReflectedLogCurvature x)
        (thetaCuspFullReflectedLogFourthJet x)
        (thetaCuspFullReflectedLogSixthJet x)
        (thetaCuspFullReflectedLogEighthJet x) by rfl,
    thetaCuspReflectedEighthPolynomial_eq_schur]
  unfold thetaCuspReflectedEighthSchurCoupling
    thetaCuspFullReflectionEighthNegativeSchurCoordinate
  ring

/-- On the physical sheet, singularity is exactly one positive-coordinate cone equation. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_eq_zero_iff_negativeSchurCone
    (x : ℝ) :
    thetaCuspFullReflectionEighthHankelCurvature x = 0 ↔
      thetaCuspFullReflectionEighthNegativeSchurCoordinate x ^ (2 : ℕ) =
        thetaCuspReflectedEighthSchurHead
            (thetaCuspFullReflectedLogCurvature x)
            (thetaCuspFullReflectedLogFourthJet x) *
          thetaCuspReflectedEighthSchurTail
            (thetaCuspFullReflectedLogCurvature x)
            (thetaCuspFullReflectedLogFourthJet x)
            (thetaCuspFullReflectedLogEighthJet x) := by
  rw [thetaCuspFullReflectionEighthHankelCurvature_eq_negativeSchurNormalForm]
  constructor <;> intro h <;> linarith

/-- Exact singular-locus classification on the physical orbit.  At a rank-three zero there is a
unique positive coordinate `q`; the Schur coupling is `-q`, and the cone equation is
`q² = head * tail`.  This removes the positive sheet before any crossing argument. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_eq_zero_iff_unique_negativeSchurSheet
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullReflectionEighthHankelCurvature x = 0 ↔
      ∃! q : ℝ, 0 < q ∧
        thetaCuspReflectedEighthSchurCoupling
          (thetaCuspFullReflectedLogCurvature x)
          (thetaCuspFullReflectedLogSixthJet x) = -q ∧
        q ^ (2 : ℕ) =
          thetaCuspReflectedEighthSchurHead
              (thetaCuspFullReflectedLogCurvature x)
              (thetaCuspFullReflectedLogFourthJet x) *
            thetaCuspReflectedEighthSchurTail
              (thetaCuspFullReflectedLogCurvature x)
              (thetaCuspFullReflectedLogFourthJet x)
              (thetaCuspFullReflectedLogEighthJet x) := by
  let A := thetaCuspFullReflectedLogCurvature x
  let B := thetaCuspFullReflectedLogFourthJet x
  let C := thetaCuspFullReflectedLogSixthJet x
  let D := thetaCuspFullReflectedLogEighthJet x
  let J := thetaCuspReflectedEighthSchurCoupling A C
  have hJ : J < 0 := by
    simpa only [J, A, C] using thetaCuspFullReflectionEighthSchurCoupling_neg hx
  have hschur := thetaCuspReflectedEighthPolynomial_eq_schur A B C D
  change thetaCuspReflectedEighthPolynomial A B C D = 0 ↔ _
  constructor
  · intro hzero
    refine ⟨-J, ⟨by linarith, ?_, ?_⟩, ?_⟩
    · simp only [A, C, J, neg_neg]
    · rw [hschur] at hzero
      nlinarith
    · intro y hy
      have hyJ : J = -y := by
        simpa only [A, C, J] using hy.2.1
      nlinarith
  · rintro ⟨q, ⟨hq, hJq, hq2⟩, _⟩
    rw [hschur]
    change thetaCuspReflectedEighthSchurHead A B *
        thetaCuspReflectedEighthSchurTail A B D - J ^ (2 : ℕ) = 0
    nlinarith

end

end RHTower
