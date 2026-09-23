import GaloisForLFunctions.RHTower.WallBlockSourceExpansion
import GaloisForLFunctions.RHTower.WallEvenAmplitudeBounds

/-!
# The block Fubini in either orientation, and the evenness of the floor

The block source's Fubini and the integrability of its position average were established for an
interval traversed forwards.  On the inward frequency ray the same interval is traversed backwards,
and both statements follow from the forward ones by the orientation identity
`∫_a^b = −∫_b^a`, which changes nothing but a sign.

The logarithmic floor `log(2+|x|)` is even, so a gap assumed at a threshold holds at every frequency
of larger modulus — on either ray.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

omit [CompleteSpace X] in
/-- The floor is even in the frequency. -/
theorem wallFloor_neg (T : X →L[ℂ] X) (σ x : ℝ) : wallFloor T σ (-x) = wallFloor T σ x := by
  rw [wallFloor, wallFloor, abs_neg]

omit [CompleteSpace X] in
/-- The floor grows with the modulus of the frequency. -/
theorem wallFloor_abs_mono {σ Y t : ℝ} (hYt : |Y| ≤ |t|) :
    wallFloor T σ Y ≤ wallFloor T σ t := by
  rw [wallFloor, wallFloor]
  have : Real.log (2 + |Y|) ≤ Real.log (2 + |t|) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

variable [Nontrivial X] {E : ℂ → ℂ}

omit [Nontrivial X] in
/-- **The position average of the block phase integral is integrable, in either orientation.** -/
theorem integrableOn_blockPhaseIntegral'
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m : ℝ} (hg : IntegrableOn g (Icc m (m + 1))) (a b : ℝ) :
    IntegrableOn (fun L : ℝ => ∫ t in a..b, wallPhaseMap E T σ L t (g L))
      (Icc m (m + 1)) := by
  rcases le_total a b with hab | hba
  · exact integrableOn_blockPhaseIntegral hEdiff hE hEne hσ0 hσ1 hg hab
  · have h := (integrableOn_blockPhaseIntegral (T := T) hEdiff hE hEne hσ0 hσ1 hg hba).neg
    refine h.congr (Filter.Eventually.of_forall fun L => ?_)
    show -(∫ t in b..a, wallPhaseMap E T σ L t (g L))
      = ∫ t in a..b, wallPhaseMap E T σ L t (g L)
    rw [intervalIntegral.integral_symm, neg_neg]

omit [Nontrivial X] in
/-- **The block source's Fubini, in either orientation.** -/
theorem integral_blockSource_swap'
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m : ℝ} (hg : IntegrableOn g (Icc m (m + 1))) (a b : ℝ) :
    (∫ t in a..b, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (blockSource g m t))
      = (-(Complex.I) / 2 : ℂ) •
          ∫ L in Icc m (m + 1), ∫ t in a..b, wallPhaseMap E T σ L t (g L) := by
  rcases le_total a b with hab | hba
  · exact integral_blockSource_swap hEdiff hE hEne hσ0 hσ1 hg hab
  · have h := integral_blockSource_swap (T := T) hEdiff hE hEne hσ0 hσ1 hg hba
    simp only [intervalIntegral.integral_symm b a]
    rw [h, MeasureTheory.integral_neg, smul_neg]

end GaloisForLFunctions.RHTower
