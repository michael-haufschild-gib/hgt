import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyWallHardyEvaluation

/-!
# Gamma-completed two-depth Suzuki wall secant

Suzuki's unit-Riesz reporter is realized as a two-depth complex wall secant.  This puts the literal
CCM archimedean density and hyperbolic polar channel into the same height carrier as the completed
prime wall.  Their assembled lower-Hardy value is Suzuki's Green functional.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

@[simp] theorem suzukiCauchyWallPhaseComplex_zero (x : ℝ) :
    suzukiCauchyWallPhaseComplex x 0 = 1 := by
  simp [suzukiCauchyWallPhaseComplex, suzukiOscillatoryKernel]

theorem suzukiCauchyWallPhaseComplex_two_mul
    (x : ℝ) (z : ℂ) :
    suzukiCauchyWallPhaseComplex x (2 * z) =
      suzukiCauchyWallPhaseComplex (2 * x) z := by
  rw [suzukiCauchyWallPhaseComplex, suzukiCauchyWallPhaseComplex,
    suzukiOscillatoryKernel, suzukiOscillatoryKernel]
  congr 1
  push_cast
  ring

/-- Complex two-depth secant whose lower Hardy value is Suzuki's unit-Riesz reporter. -/
def suzukiUnitRieszReporterWallSecant (H h : ℝ) (z : ℂ) : ℂ :=
  suzukiCauchyWallPhaseComplex (h - H) z -
    suzukiCauchyWallPhaseComplex (h - H) (2 * z)

@[simp] theorem suzukiUnitRieszReporterWallSecant_zero
    (H h : ℝ) :
    suzukiUnitRieszReporterWallSecant H h 0 = 0 := by
  simp [suzukiUnitRieszReporterWallSecant]

/-- Suzuki's real reporter is exactly one lower-Hardy evaluation of the two-depth wall secant. -/
theorem suzukiUnitRieszReporterWallSecant_neg_I
    (H h : ℝ) :
    suzukiUnitRieszReporterWallSecant H h (-I) =
      (RHTower.unitRieszSuzukiReporter H h : ℂ) := by
  rw [suzukiUnitRieszReporterWallSecant,
    suzukiCauchyWallPhaseComplex_neg_I,
    suzukiCauchyWallPhaseComplex_two_mul,
    suzukiCauchyWallPhaseComplex_neg_I,
    RHTower.unitRieszSuzukiReporter]
  rw [show 2 * (h - H) / 2 = h - H by ring]
  push_cast
  rfl

/-- Actual CCM archimedean density transported into the two-depth wall carrier. -/
def suzukiUnitRieszArchWallSecant (H : ℝ) (z : ℂ) : ℂ :=
  ∫ h in RHTower.unitRieszSuzukiBase..H,
    suzukiUnitRieszReporterWallSecant H h z *
      (RHTower.ccmPublishedArchimedeanDensity h : ℂ)

/-- The lower Hardy value of the archimedean wall is the literal Suzuki Gamma correction. -/
theorem suzukiUnitRieszArchWallSecant_neg_I (H : ℝ) :
    suzukiUnitRieszArchWallSecant H (-I) =
      (RHTower.unitRieszSuzukiArchCorrection H : ℂ) := by
  rw [suzukiUnitRieszArchWallSecant, RHTower.unitRieszSuzukiArchCorrection]
  calc
    (∫ h in RHTower.unitRieszSuzukiBase..H,
        suzukiUnitRieszReporterWallSecant H h (-I) *
          (RHTower.ccmPublishedArchimedeanDensity h : ℂ)) =
      ∫ h in RHTower.unitRieszSuzukiBase..H,
        ((RHTower.unitRieszSuzukiReporter H h *
          RHTower.ccmPublishedArchimedeanDensity h : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro h hh
        change suzukiUnitRieszReporterWallSecant H h (-I) *
            (RHTower.ccmPublishedArchimedeanDensity h : ℂ) =
          ((RHTower.unitRieszSuzukiReporter H h *
            RHTower.ccmPublishedArchimedeanDensity h : ℝ) : ℂ)
        rw [suzukiUnitRieszReporterWallSecant_neg_I]
        push_cast
        rfl
    _ = _ := intervalIntegral.integral_ofReal

@[simp] theorem suzukiUnitRieszArchWallSecant_zero (H : ℝ) :
    suzukiUnitRieszArchWallSecant H 0 = 0 := by
  simp [suzukiUnitRieszArchWallSecant]

/-- Hyperbolic polar channel in the same two-depth wall carrier, with its endpoint counterterm. -/
def suzukiUnitRieszPolarWallSecant (H : ℝ) (z : ℂ) : ℂ :=
  (∫ h in RHTower.unitRieszSuzukiBase..H,
    suzukiUnitRieszReporterWallSecant H h z *
      ((2 * Real.cosh (h / 2) : ℝ) : ℂ)) -
    (Real.exp (H / 2) : ℂ) * suzukiCauchyWallPolarCountertermComplex z

/-- The lower Hardy value of the polar wall is the literal Suzuki polar correction. -/
theorem suzukiUnitRieszPolarWallSecant_neg_I (H : ℝ) :
    suzukiUnitRieszPolarWallSecant H (-I) =
      (RHTower.unitRieszSuzukiPolarCorrection H : ℂ) := by
  rw [suzukiUnitRieszPolarWallSecant, RHTower.unitRieszSuzukiPolarCorrection,
    suzukiCauchyWallPolarCountertermComplex_neg_I]
  have hint :
      (∫ h in RHTower.unitRieszSuzukiBase..H,
        suzukiUnitRieszReporterWallSecant H h (-I) *
          ((2 * Real.cosh (h / 2) : ℝ) : ℂ)) =
        ((∫ h in RHTower.unitRieszSuzukiBase..H,
          RHTower.unitRieszSuzukiReporter H h *
            (2 * Real.cosh (h / 2))) : ℝ) := by
    calc
      _ = ∫ h in RHTower.unitRieszSuzukiBase..H,
          ((RHTower.unitRieszSuzukiReporter H h *
            (2 * Real.cosh (h / 2)) : ℝ) : ℂ) := by
            apply intervalIntegral.integral_congr
            intro h hh
            change suzukiUnitRieszReporterWallSecant H h (-I) *
                ((2 * Real.cosh (h / 2) : ℝ) : ℂ) =
              ((RHTower.unitRieszSuzukiReporter H h *
                (2 * Real.cosh (h / 2)) : ℝ) : ℂ)
            rw [suzukiUnitRieszReporterWallSecant_neg_I]
            push_cast
            rfl
      _ = _ := intervalIntegral.integral_ofReal
  rw [hint]
  push_cast
  ring

@[simp] theorem suzukiCauchyWallPolarCountertermComplex_zero :
    suzukiCauchyWallPolarCountertermComplex 0 = 0 := by
  simp [suzukiCauchyWallPolarCountertermComplex]

@[simp] theorem suzukiUnitRieszPolarWallSecant_zero (H : ℝ) :
    suzukiUnitRieszPolarWallSecant H 0 = 0 := by
  simp [suzukiUnitRieszPolarWallSecant]

/-- Full prime--polar--Gamma wall carrier selected by the Suzuki Green identity. -/
def suzukiUnitRieszGammaCompletedWardWall (N : ℕ) (z : ℂ) : ℂ :=
  suzukiUnitRieszCompletedCauchyWallSymbolComplex N z -
    suzukiUnitRieszPolarWallSecant (Real.log N) z +
    suzukiUnitRieszArchWallSecant (Real.log N) z

/-- All completed channels vanish at zero height before taking any trace. -/
@[simp] theorem suzukiUnitRieszGammaCompletedWardWall_zero (N : ℕ) :
    suzukiUnitRieszGammaCompletedWardWall N 0 = 0 := by
  have hsymbol : suzukiUnitRieszCompletedCauchyWallSymbolComplex N 0 = 0 := by
    change suzukiUnitRieszCompletedCauchyWallSymbolComplex N ((0 : ℝ) : ℂ) = 0
    rw [suzukiUnitRieszCompletedCauchyWallSymbolComplex_ofReal,
      suzukiUnitRieszCompletedCauchyWallSymbol_zero]
  rw [suzukiUnitRieszGammaCompletedWardWall, hsymbol]
  simp

/-- **Prime--polar--Gamma Ward assembly.**  At every nondegenerate natural aperture, the lower
Hardy value of the full wall is exactly Suzuki's Green functional. -/
theorem suzukiUnitRieszGammaCompletedWardWall_add_two_neg_I_eq_green
    (N : ℕ) :
    suzukiUnitRieszGammaCompletedWardWall (N + 2) (-I) =
      (RHTower.unitRieszSuzukiGreen (Real.log (N + 2)) : ℂ) := by
  rw [suzukiUnitRieszGammaCompletedWardWall,
    suzukiUnitRieszCompletedCauchyWallSymbolComplex_neg_I_eq_outgoingCharge,
    suzukiUnitRieszPolarWallSecant_neg_I,
    suzukiUnitRieszArchWallSecant_neg_I,
    RHTower.unitRieszSuzuki_outgoing_eq_green (by omega : 2 ≤ N + 2)]
  norm_num
  ring

end

end GaloisForLFunctions.RHTower
