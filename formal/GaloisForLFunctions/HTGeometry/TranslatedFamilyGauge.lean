import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge
import GaloisForLFunctions.HTGeometry.RegularizedTransformGauge

/-!
# The translated Herglotz presentations as a componentwise gauge

Each translate of the normalized Herglotz presentation is the corresponding translate of the Cauchy
transform, multiplied by the translated Nevanlinna multiplier and shifted by the translated mass
term.  Both are polynomials in the spectral variable and the multiplier is nonzero, so the
componentwise affine gauge applies to the whole translated family at once.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory

noncomputable section

/-- The Nevanlinna multiplier translated by `c`. -/
def translatedNevanlinnaMultiplier (c : ℂ) : Polynomial ℂ :=
  1 + (Polynomial.X + Polynomial.C c) ^ 2

/-- The mass term translated by `c`. -/
def translatedMassShift (c M : ℂ) : Polynomial ℂ :=
  (Polynomial.X + Polynomial.C c) * Polynomial.C M

@[simp]
theorem eval_translatedNevanlinnaMultiplier (c z : ℂ) :
    Polynomial.eval z (translatedNevanlinnaMultiplier c) = 1 + (z + c) ^ 2 := by
  simp [translatedNevanlinnaMultiplier]

@[simp]
theorem eval_translatedMassShift (c M z : ℂ) :
    Polynomial.eval z (translatedMassShift c M) = (z + c) * M := by
  simp [translatedMassShift]

theorem translatedNevanlinnaMultiplier_ne_zero (c : ℂ) :
    translatedNevanlinnaMultiplier c ≠ 0 := by
  intro hzero
  have h := congrArg (Polynomial.eval (-c)) hzero
  rw [eval_translatedNevanlinnaMultiplier] at h
  simp at h

/-- The translated Cauchy transform is smooth wherever its node is off the real axis. -/
theorem contDiffAt_cauchyTransform_translate (ν : Measure ℝ) [IsFiniteMeasure ν] (c : ℂ)
    {z : ℂ} (hz : (z + c).im ≠ 0) :
    ContDiffAt ℂ (⊤ : ℕ∞) (fun w => cauchyTransform ν (w + c)) z := by
  have hshift : ContDiffAt ℂ (⊤ : ℕ∞) (fun w : ℂ => w + c) z :=
    contDiffAt_id.add contDiffAt_const
  have hcomp : (fun w => cauchyTransform ν (w + c))
      = cauchyTransform ν ∘ fun w : ℂ => w + c := rfl
  rw [hcomp]
  exact (contDiffAt_cauchyTransform ν hz).comp z hshift

/-- **The translated Herglotz presentations are a componentwise affine gauge of the translated
Cauchy transforms.**  A differential relation among the translates of the presentation pulls back
to one among the translates of the Cauchy transform. -/
theorem familyDifferentiallyAlgebraicOn_translatedCauchy_of_presentation
    {m : ℕ} {U : Set ℂ} (ν : Measure ℝ) [IsFiniteMeasure ν] (M : ℂ) (h : Fin m → ℂ)
    (hU : ∀ z ∈ U, ∀ i, (z + h i).im ≠ 0)
    (hrel : FamilyDifferentiallyAlgebraicOn
      (fun i z => (z + h i) * M + (1 + (z + h i) ^ 2) * cauchyTransform ν (z + h i)) U) :
    FamilyDifferentiallyAlgebraicOn (fun i z => cauchyTransform ν (z + h i)) U := by
  refine familyDifferentiallyAlgebraicOn_of_affine
    (fun i z => cauchyTransform ν (z + h i))
    (fun i => translatedNevanlinnaMultiplier (h i))
    (fun i => translatedMassShift (h i) M)
    (fun i => translatedNevanlinnaMultiplier_ne_zero (h i))
    (fun z hz i => contDiffAt_cauchyTransform_translate ν (h i) (hU z hz i)) ?_
  obtain ⟨n, P, hP, hzero⟩ := hrel
  refine ⟨n, P, hP, fun z hz => ?_⟩
  have hfun : (fun i (z : ℂ) => Polynomial.eval z (translatedMassShift (h i) M)
      + Polynomial.eval z (translatedNevanlinnaMultiplier (h i))
        * cauchyTransform ν (z + h i))
      = fun i (z : ℂ) => (z + h i) * M
        + (1 + (z + h i) ^ 2) * cauchyTransform ν (z + h i) := by
    funext i w
    rw [eval_translatedMassShift, eval_translatedNevanlinnaMultiplier]
  rw [hfun]
  exact hzero z hz

end

end GaloisForLFunctions.HTGeometry
