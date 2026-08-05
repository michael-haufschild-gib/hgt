import GaloisForLFunctions.RHTower.XiMassComovingPrimeCone
import GaloisForLFunctions.RHTower.XiMassPrimeGradedOpenCore

/-!
# Exact type of the fixed-to-co-moving Xi prime aperture gap

The co-moving source with mass `|u|+2` is uniformly bounded.  Subtract it from a fixed legal mass
source.  The resulting transverse Bessel-aperture high-pass has exactly the same nonnegative
exponential growth classes as the fixed source, hence exactly the fixed carrier's displacement
type.  At exponent zero its boundedness is equivalent to RH.

This is not a boundedness proof.  It removes the universal bounded bulk and identifies the precise
source-side transverse aperture defect where all remaining RH-strength growth lives.
-/

open Complex

namespace RHTower

noncomputable section

/-- Difference between a fixed legal mass source and the uniformly bounded co-moving source. -/
def xiMassBottomPrimeApertureGap (a c σ u : ℝ) : ℂ :=
  xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I) -
    xiMassBottomPrimeIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I)

/-- Nonnegative exponential growth class of the transverse mass-aperture gap. -/
def XiMassBottomPrimeApertureGapLineGrowth
    (a c σ lam : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassBottomPrimeApertureGap a c σ u‖ ≤
      C * Real.exp (lam * |u|)

/-- Uniform boundedness of the transverse mass-aperture gap. -/
def XiMassBottomPrimeApertureGapLineBound
    (a c σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassBottomPrimeApertureGap a c σ u‖ ≤ C

/-- Subtracting the bounded co-moving source preserves every nonnegative exponential growth
class exactly. -/
theorem xiMassBottomPrimeApertureGapLineGrowth_iff_primeLineGrowth
    {a c σ lam : ℝ} (hσ : 1 / 2 < σ) (hlam : 0 ≤ lam) :
    XiMassBottomPrimeApertureGapLineGrowth a c σ lam ↔
      XiMassBottomPrimeLineGrowth a c σ lam := by
  let D : ℝ := ‖(Real.pi : ℂ) * I‖ * xiPoissonTraceReal (σ - 1 / 2) +
    xiMassBottomArchUniformBound 2 σ
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg
      (mul_nonneg (norm_nonneg _) (xiPoissonAbstract.traceReal_nonneg _))
      (xiMassBottomArchUniformBound_nonneg (by norm_num) (by linarith))
  have hmove : ∀ u : ℝ,
      ‖xiMassBottomPrimeIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I)‖ ≤ D :=
    fun u => norm_xiMassBottomPrimeIntegral_comoving_le hσ u
  have hE : ∀ u : ℝ, 1 ≤ Real.exp (lam * |u|) :=
    fun u => Real.one_le_exp (mul_nonneg hlam (abs_nonneg u))
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + D, fun u => ?_⟩
    let E : ℝ := Real.exp (lam * |u|)
    have hDE : D ≤ D * E := le_mul_of_one_le_right hD (hE u)
    calc
      ‖xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I)‖ =
          ‖xiMassBottomPrimeApertureGap a c σ u +
            xiMassBottomPrimeIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I)‖ := by
        unfold xiMassBottomPrimeApertureGap
        congr 1
        ring
      _ ≤ ‖xiMassBottomPrimeApertureGap a c σ u‖ +
          ‖xiMassBottomPrimeIntegral (xiComovingMass u) 1
            ((σ : ℂ) + u * I)‖ := norm_add_le _ _
      _ ≤ C * E + D := add_le_add (hC u) (hmove u)
      _ ≤ C * E + D * E := add_le_add le_rfl hDE
      _ = (C + D) * E := by ring
  · rintro ⟨C, hC⟩
    refine ⟨C + D, fun u => ?_⟩
    let E : ℝ := Real.exp (lam * |u|)
    have hDE : D ≤ D * E := le_mul_of_one_le_right hD (hE u)
    unfold xiMassBottomPrimeApertureGap
    calc
      ‖xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I) -
          xiMassBottomPrimeIntegral (xiComovingMass u) 1
            ((σ : ℂ) + u * I)‖ ≤
        ‖xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I)‖ +
          ‖xiMassBottomPrimeIntegral (xiComovingMass u) 1
            ((σ : ℂ) + u * I)‖ := norm_sub_le _ _
      _ ≤ C * E + D := add_le_add (hC u) (hmove u)
      _ ≤ C * E + D * E := add_le_add le_rfl hDE
      _ = (C + D) * E := by ring

/-- **Exact high-pass type law.**  The transverse prime aperture gap has exponent `lam` exactly
when every fixed-mass Xi displacement is at most `lam`. -/
theorem xiMassBottomPrimeApertureGapLineGrowth_iff_mass_displacement_le
    {a c σ lam : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hσ : 1 / 2 < σ) (hlam : 0 ≤ lam) :
    XiMassBottomPrimeApertureGapLineGrowth a c σ lam ↔
      ∀ q : XiZeroCopy,
        |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| ≤ lam := by
  rw [xiMassBottomPrimeApertureGapLineGrowth_iff_primeLineGrowth hσ hlam]
  exact xiMassBottomPrimeLineGrowth_iff_mass_displacement_le hhalf hca
    (by linarith) hlam

theorem xiMassBottomPrimeApertureGapLineBound_iff_primeLineBound
    {a c σ : ℝ} (hσ : 1 / 2 < σ) :
    XiMassBottomPrimeApertureGapLineBound a c σ ↔
      XiMassBottomPrimeLineBound a c σ := by
  have h := xiMassBottomPrimeApertureGapLineGrowth_iff_primeLineGrowth
    (a := a) (c := c) hσ (show 0 ≤ (0 : ℝ) by norm_num)
  simpa [XiMassBottomPrimeApertureGapLineGrowth,
    XiMassBottomPrimeApertureGapLineBound, XiMassBottomPrimeLineGrowth,
    XiMassBottomPrimeLineBound] using h

/-- **Prime aperture-gap RH criterion.**  All RH-strength growth is the transverse difference
between one fixed Bessel mass and the universally bounded co-moving mass cone. -/
theorem riemannHypothesis_iff_xiMassBottomPrimeApertureGapLineBound
    {a c σ : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 1 / 2 < σ) :
    RiemannHypothesis ↔ XiMassBottomPrimeApertureGapLineBound a c σ := by
  rw [xiMassBottomPrimeApertureGapLineBound_iff_primeLineBound hσ]
  exact riemannHypothesis_iff_xiMassBottomPrimeLineBound hhalf hca (by linarith)

end

end RHTower
