import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseMellinTrace
import GaloisForLFunctions.RHTower.Reflection

/-!
# Gamma-weighted reflection fixing the native Weil pole

The unit-modulus Gamma quotient mechanism in the paper's cubic reflection
kernel applies to the actual WP05 pole profile. Its weighted reflection is a
complex-linear isometric involution. The odd projection removes the complete
pole term, with its actual source-dependent coefficient.
-/

open Complex Set Filter MeasureTheory Topology

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open WeilSpectral IntegerMassRigidity PhaseLockRigidity

/-- The Gamma profile of the actual pole subtracted from the completion. -/
def paperPoleGamma (y : ℝ) : ℂ := Gammaℝ (tracePoint 0 y - 1)

theorem paperPoleGamma_ne_zero (y : ℝ) : paperPoleGamma y ≠ 0 := by
  have hz : tracePoint 0 y - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [tracePoint] at this
  have hp : 0 < (tracePoint 0 y - 1 + 2).re := by
    norm_num [tracePoint]
  intro h
  have he := Complex.Gammaℝ_add_two hz
  rw [show Gammaℝ (tracePoint 0 y - 1) = 0 from h] at he
  exact (Complex.Gammaℝ_ne_zero_of_re_pos hp) (by simpa using he)

@[simp] theorem paperPoleGamma_neg (y : ℝ) :
    paperPoleGamma (-y) = (starRingEnd ℂ) (paperPoleGamma y) := by
  unfold paperPoleGamma
  rw [← Gammaℝ_conj]
  congr 1
  simp [tracePoint_conj]

theorem continuous_paperPoleGamma : Continuous paperPoleGamma := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hp : 0 < (tracePoint 0 y).re := by norm_num [tracePoint]
  have hn : tracePoint 0 y ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [tracePoint] at this
  exact (differentiableAt_Gammaℝ_sub_one hp hn).continuousAt.comp
    (f := tracePoint 0) (by unfold tracePoint; fun_prop)

/-- The quotient is everywhere defined and has unit modulus. -/
def paperGammaPhase (y : ℝ) : ℂ := paperPoleGamma y / paperPoleGamma (-y)

@[simp] theorem norm_paperGammaPhase (y : ℝ) : ‖paperGammaPhase y‖ = 1 := by
  simp only [paperGammaPhase, norm_div, paperPoleGamma_neg, norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (paperPoleGamma_ne_zero y))

theorem continuous_paperGammaPhase : Continuous paperGammaPhase :=
  continuous_paperPoleGamma.div (continuous_paperPoleGamma.comp continuous_neg)
    (fun y => paperPoleGamma_ne_zero (-y))

@[simp] theorem paperGammaPhase_mul_neg (y : ℝ) :
    paperGammaPhase y * paperGammaPhase (-y) = 1 := by
  simp only [paperGammaPhase, neg_neg]
  field_simp [paperPoleGamma_ne_zero y, paperPoleGamma_ne_zero (-y)]

/-- Reflection in height, weighted to fix the actual Gamma pole profile. -/
def paperGammaReflection (f : ℝ → ℂ) (y : ℝ) : ℂ := paperGammaPhase y * f (-y)

@[simp] theorem paperGammaReflection_involutive (f : ℝ → ℂ) :
    paperGammaReflection (paperGammaReflection f) = f := by
  funext y
  simp [paperGammaReflection, ← mul_assoc]

@[simp] theorem norm_paperGammaReflection (f : ℝ → ℂ) (y : ℝ) :
    ‖paperGammaReflection f y‖ = ‖f (-y)‖ := by
  simp [paperGammaReflection]

theorem paperGammaReflection_add (f g : ℝ → ℂ) :
    paperGammaReflection (fun y => f y + g y) =
      fun y => paperGammaReflection f y + paperGammaReflection g y := by
  funext y
  exact mul_add _ _ _

theorem paperGammaReflection_sub (f g : ℝ → ℂ) :
    paperGammaReflection (fun y => f y - g y) =
      fun y => paperGammaReflection f y - paperGammaReflection g y := by
  funext y
  exact mul_sub _ _ _

theorem paperGammaReflection_const_mul (c : ℂ) (f : ℝ → ℂ) :
    paperGammaReflection (fun y => c * f y) =
      fun y => c * paperGammaReflection f y := by
  funext y
  dsimp [paperGammaReflection]
  ring

@[simp] theorem paperGammaReflection_pole (c : ℂ) :
    paperGammaReflection (fun y => c * paperPoleGamma y) =
      fun y => c * paperPoleGamma y := by
  funext y
  dsimp [paperGammaReflection, paperGammaPhase]
  rw [mul_comm c, ← mul_assoc, div_mul_cancel₀ _ (paperPoleGamma_ne_zero (-y)), mul_comm]

/-- The source completion divided by its native quadratic factor. -/
def paperUnsubtractedTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℂ :=
  sourceTrace hW y / (tracePoint 0 y * (tracePoint 0 y - 1))

/-- Reflection removes the entire pole without knowing or estimating its coefficient. -/
theorem paperGammaReflection_pole_cancellation {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (y : ℝ) :
    remainderTrace hW y - paperGammaReflection (remainderTrace hW) y =
      paperUnsubtractedTrace hW y -
        paperGammaReflection (paperUnsubtractedTrace hW) y := by
  have hfix := congrFun (paperGammaReflection_pole (betaG (sourceCompletion hW))) y
  dsimp [paperGammaReflection] at hfix
  dsimp [remainderTrace, paperUnsubtractedTrace, paperGammaReflection, paperPoleGamma]
  dsimp [paperPoleGamma] at hfix
  linear_combination hfix

/-- The two spectral projections of the Gamma-weighted involution. -/
def paperGammaEven (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  (f y + paperGammaReflection f y) / 2

def paperGammaOdd (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  (f y - paperGammaReflection f y) / 2

theorem paperGammaEven_add_odd (f : ℝ → ℂ) (y : ℝ) :
    paperGammaEven f y + paperGammaOdd f y = f y := by
  dsimp [paperGammaEven, paperGammaOdd]
  ring

@[simp] theorem paperGammaReflection_even (f : ℝ → ℂ) :
    paperGammaReflection (paperGammaEven f) = paperGammaEven f := by
  funext y
  have h := congrFun (paperGammaReflection_involutive f) y
  dsimp [paperGammaEven, paperGammaReflection] at *
  linear_combination h / 2

@[simp] theorem paperGammaReflection_odd (f : ℝ → ℂ) :
    paperGammaReflection (paperGammaOdd f) = fun y => -paperGammaOdd f y := by
  funext y
  have h := congrFun (paperGammaReflection_involutive f) y
  dsimp [paperGammaOdd, paperGammaReflection] at *
  linear_combination -h / 2

@[simp] theorem paperGammaEven_idempotent (f : ℝ → ℂ) :
    paperGammaEven (paperGammaEven f) = paperGammaEven f := by
  funext y
  simp only [paperGammaEven, paperGammaReflection_even]
  ring

@[simp] theorem paperGammaOdd_idempotent (f : ℝ → ℂ) :
    paperGammaOdd (paperGammaOdd f) = paperGammaOdd f := by
  funext y
  simp only [paperGammaOdd, paperGammaReflection_odd]
  ring

theorem paperGammaOdd_remainderTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    paperGammaOdd (remainderTrace hW) = paperGammaOdd (paperUnsubtractedTrace hW) := by
  funext y
  exact congrArg (fun z : ℂ => z / 2) (paperGammaReflection_pole_cancellation hW y)

end RHTower.WeilWorkSettledPhase
