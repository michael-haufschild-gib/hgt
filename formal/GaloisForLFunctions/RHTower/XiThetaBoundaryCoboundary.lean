import GaloisForLFunctions.RHTower.XiThetaLogTranslationSeam

/-!
# The theta moving boundary is an exact translation coboundary

Positive truncation creates a finite moving window when a logarithmic theta profile is translated.
This file tests whether that window is a genuine seam obstruction or merely flow data.  It is the
latter.

After normalization by inverse translation, the boundary is exactly the conjugation coboundary of
the fixed positive-half projection.  Its additive translation cocycle law is exact and its
curvature vanishes identically.  Consequently the moving-boundary charge cannot itself represent a
nontrivial polarized weld class; any such class must survive quotienting by these translation
coboundaries.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- Forward translation in logarithmic coordinates. -/
def forwardLogTranslate {E : Type*} (a : ℝ) (f : ℝ → E) (u : ℝ) : E := f (u + a)

/-- The positive-half projection defect after conjugating by logarithmic translation. -/
def positiveProjectionConjugationDefect {E : Type*} [AddCommGroup E]
    (a : ℝ) (f : ℝ → E) (u : ℝ) : E :=
  forwardLogTranslate a (positiveLogTruncation (forwardLogTranslate (-a) f)) u -
    positiveLogTruncation f u

/-- The moving boundary is exactly the unnormalized commutator of forward translation with the
positive-half projection. -/
theorem forwardTranslationBoundary_eq_projection_commutator
    {E : Type*} [AddCommGroup E] (f : ℝ → E) {a : ℝ} (ha : 0 < a) (u : ℝ) :
    forwardTranslationBoundary a f u =
      forwardLogTranslate a (positiveLogTruncation f) u -
        positiveLogTruncation (forwardLogTranslate a f) u := by
  have h := positiveLogTruncation_translate_add_boundary f ha u
  have h' : positiveLogTruncation (forwardLogTranslate a f) u +
      forwardTranslationBoundary a f u =
        forwardLogTranslate a (positiveLogTruncation f) u := by
    change positiveLogTruncation (fun v => f (v + a)) u +
      forwardTranslationBoundary a f u = positiveLogTruncation f (u + a)
    exact h
  exact eq_sub_of_add_eq (by simpa only [add_comm] using h')

/-- After normalization by the inverse translation, the moving boundary is a conjugation
coboundary of the fixed positive-half projection. -/
theorem forwardTranslationBoundary_eq_conjugationDefect
    {E : Type*} [AddCommGroup E] (f : ℝ → E) {a : ℝ} (ha : 0 < a) (u : ℝ) :
    forwardTranslationBoundary a f u =
      positiveProjectionConjugationDefect a (forwardLogTranslate a f) u := by
  rw [forwardTranslationBoundary_eq_projection_commutator f ha u]
  have hcancel : forwardLogTranslate (-a) (forwardLogTranslate a f) = f := by
    funext v
    simp only [forwardLogTranslate]
    congr 1
    ring
  simp only [positiveProjectionConjugationDefect, hcancel]

/-- The unnormalized moving windows compose by the exact translation-cocycle law. -/
theorem forwardTranslationBoundary_add
    {E : Type*} [AddCommGroup E] (f : ℝ → E) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    forwardTranslationBoundary (a + b) f u =
      forwardTranslationBoundary a (forwardLogTranslate b f) u +
        forwardLogTranslate a (forwardTranslationBoundary b f) u := by
  rw [forwardTranslationBoundary_eq_projection_commutator f (add_pos ha hb) u,
    forwardTranslationBoundary_eq_projection_commutator (forwardLogTranslate b f) ha u]
  change forwardLogTranslate (a + b) (positiveLogTruncation f) u -
      positiveLogTruncation (forwardLogTranslate (a + b) f) u =
    (forwardLogTranslate a (positiveLogTruncation (forwardLogTranslate b f)) u -
      positiveLogTruncation (forwardLogTranslate a (forwardLogTranslate b f)) u) +
      forwardTranslationBoundary b f (u + a)
  rw [forwardTranslationBoundary_eq_projection_commutator f hb (u + a)]
  have hcomp : forwardLogTranslate a (forwardLogTranslate b f) =
      forwardLogTranslate (a + b) f := by
    funext v
    simp only [forwardLogTranslate]
    congr 1
    ring
  rw [hcomp]
  simp only [forwardLogTranslate]
  rw [show u + (a + b) = u + a + b by ring]
  abel

/-- The normalized projection defect obeys the exact additive cocycle law for translation
conjugation. -/
theorem positiveProjectionConjugationDefect_add
    {E : Type*} [AddCommGroup E] (f : ℝ → E) (a b u : ℝ) :
    positiveProjectionConjugationDefect (a + b) f u =
      forwardLogTranslate a
          (positiveProjectionConjugationDefect b (forwardLogTranslate (-a) f)) u +
        positiveProjectionConjugationDefect a f u := by
  have hneg : forwardLogTranslate (-b) (forwardLogTranslate (-a) f) =
      forwardLogTranslate (-(a + b)) f := by
    funext v
    simp only [forwardLogTranslate]
    congr 1
    ring
  simp only [positiveProjectionConjugationDefect, forwardLogTranslate]
  rw [show u + (a + b) = u + a + b by ring]
  change positiveLogTruncation (forwardLogTranslate (-(a + b)) f) (u + a + b) -
      positiveLogTruncation f u =
    positiveLogTruncation (forwardLogTranslate (-b) (forwardLogTranslate (-a) f))
        (u + a + b) -
      positiveLogTruncation (forwardLogTranslate (-a) f) (u + a) +
      (positiveLogTruncation (forwardLogTranslate (-a) f) (u + a) -
        positiveLogTruncation f u)
  rw [hneg]
  abel

/-- The associated translation curvature vanishes identically: the boundary defect is flat because
it is an exact projection coboundary. -/
theorem positiveProjectionConjugationDefect_curvature_zero
    {E : Type*} [AddCommGroup E] (f : ℝ → E) (a b u : ℝ) :
    forwardLogTranslate a
          (positiveProjectionConjugationDefect b (forwardLogTranslate (-a) f)) u +
        positiveProjectionConjugationDefect a f u -
      positiveProjectionConjugationDefect (a + b) f u = 0 := by
  rw [positiveProjectionConjugationDefect_add]
  exact sub_self _

/-- The theta moving-boundary charge at every square index is an evaluation of the same exact
translation coboundary. -/
theorem thetaSquareForwardBoundary_eq_conjugationDefect {m : ℕ} (hm : 1 < m) (u : ℝ) :
    forwardTranslationBoundary (2 * Real.log m) thetaLogMother u =
      positiveProjectionConjugationDefect (2 * Real.log m)
        (forwardLogTranslate (2 * Real.log m) thetaLogMother) u := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  exact forwardTranslationBoundary_eq_conjugationDefect thetaLogMother
    (mul_pos (by norm_num) (Real.log_pos hmR)) u

end RHTower
