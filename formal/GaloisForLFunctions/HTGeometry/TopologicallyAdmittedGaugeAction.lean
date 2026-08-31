import Mathlib

/-!
# Gauge-covariant resolution action

Unconditional finite-path core of ULF-TAFM-5. Resolution edges act contravariantly on effects,
compose with multiplicative budgets, and transform covariantly under positive local gauge
rescaling. Intermediate gauges cancel from complete path budgets. The logarithmic composition
defect is nonnegative and obeys the exact two-cocycle identity.

Paper source:
`docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/gauge-covariant-resolution-action-composition-curvature-and-detector-transfer-law.md`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped NNReal

noncomputable section

/-- Nonnegative source-generated gauge on an effect type. -/
abbrev EffectGauge (E : Type*) := E → ℝ≥0

/-- An admitted pullback together with a certified resolution budget. -/
structure ResolutionArrow (E F : Type*) (qE : EffectGauge E) (qF : EffectGauge F) where
  pull : F → E
  cost : ℝ≥0
  bound : ∀ f, qE (pull f) ≤ cost * qF f

namespace ResolutionArrow

variable {E F G : Type*} {qE : EffectGauge E} {qF : EffectGauge F}
  {qG : EffectGauge G}

/-- Identity resolution edge. -/
def identity (qE : EffectGauge E) : ResolutionArrow E E qE qE where
  pull := id
  cost := 1
  bound := by intro f; simp

/-- Composition of admitted pullbacks multiplies their certified budgets. -/
def comp (K : ResolutionArrow E F qE qF) (L : ResolutionArrow F G qF qG) :
    ResolutionArrow E G qE qG where
  pull := K.pull ∘ L.pull
  cost := K.cost * L.cost
  bound := by
    intro g
    calc
      qE (K.pull (L.pull g)) ≤ K.cost * qF (L.pull g) := K.bound _
      _ ≤ K.cost * (L.cost * qG g) := by
        gcongr
        exact L.bound g
      _ = (K.cost * L.cost) * qG g := by rw [mul_assoc]

@[simp] theorem comp_pull (K : ResolutionArrow E F qE qF)
    (L : ResolutionArrow F G qF qG) (g : G) :
    (K.comp L).pull g = K.pull (L.pull g) := rfl

@[simp] theorem comp_cost (K : ResolutionArrow E F qE qF)
    (L : ResolutionArrow F G qF qG) :
    (K.comp L).cost = K.cost * L.cost := rfl

/-- Exact source action of a detector along two formation edges. -/
def pathAction (K : ResolutionArrow E F qE qF)
    (L : ResolutionArrow F G qF qG) (g : G) : ℝ≥0 :=
  qE (K.pull (L.pull g))

/-- Complete path action is bounded by edge-budget product times terminal detector gauge. -/
theorem pathAction_le (K : ResolutionArrow E F qE qF)
    (L : ResolutionArrow F G qF qG) (g : G) :
    K.pathAction L g ≤ K.cost * L.cost * qG g :=
  (K.comp L).bound g

/-- Rescale a gauge by a strictly positive local unit. -/
def scaleGauge (c : ℝ≥0ˣ) (qE : EffectGauge E) : EffectGauge E :=
  fun e => (c : ℝ≥0) * qE e

/-- Local gauge transformation of an edge. -/
def rescale (cE cF : ℝ≥0ˣ) (K : ResolutionArrow E F qE qF) :
    ResolutionArrow E F (scaleGauge cE qE) (scaleGauge cF qF) where
  pull := K.pull
  cost := (cE : ℝ≥0) * K.cost * (cF⁻¹ : ℝ≥0ˣ)
  bound := by
    intro f
    calc
      (cE : ℝ≥0) * qE (K.pull f) ≤
          (cE : ℝ≥0) * (K.cost * qF f) :=
        by
          gcongr
          exact K.bound f
      _ = ((cE : ℝ≥0) * K.cost * (cF⁻¹ : ℝ≥0ˣ)) *
          ((cF : ℝ≥0) * qF f) := by
        simp only [Units.val_inv_eq_inv_val]
        field_simp

@[simp] theorem rescale_pull (cE cF : ℝ≥0ˣ)
    (K : ResolutionArrow E F qE qF) (f : F) :
    (K.rescale cE cF).pull f = K.pull f := rfl

@[simp] theorem rescale_cost (cE cF : ℝ≥0ˣ)
    (K : ResolutionArrow E F qE qF) :
    (K.rescale cE cF).cost =
      (cE : ℝ≥0) * K.cost * (cF⁻¹ : ℝ≥0ˣ) := rfl

/-- Intermediate and target gauge changes cancel from a complete two-edge budget. -/
theorem rescale_path_budget (cE cF cG : ℝ≥0ˣ)
    (K : ResolutionArrow E F qE qF) (L : ResolutionArrow F G qF qG) (g : G) :
    (K.rescale cE cF).cost * (L.rescale cF cG).cost *
        (scaleGauge cG qG g) =
      (cE : ℝ≥0) * (K.cost * L.cost * qG g) := by
  simp only [rescale_cost, scaleGauge, Units.val_inv_eq_inv_val]
  field_simp

/-- With source gauge fixed, full path budget is gauge invariant. -/
theorem rescale_path_budget_source_fixed (cF cG : ℝ≥0ˣ)
    (K : ResolutionArrow E F qE qF) (L : ResolutionArrow F G qF qG) (g : G) :
    (K.rescale 1 cF).cost * (L.rescale cF cG).cost *
        (scaleGauge cG qG g) =
      K.cost * L.cost * qG g := by
  simpa using rescale_path_budget (K := K) (L := L) (g := g) 1 cF cG

end ResolutionArrow

/-- Positive composition data with certified submultiplicativity. -/
structure PositiveResolutionTriangle where
  first : ℝ≥0
  second : ℝ≥0
  composite : ℝ≥0
  first_pos : 0 < first
  second_pos : 0 < second
  composite_pos : 0 < composite
  submultiplicative : composite ≤ first * second

namespace PositiveResolutionTriangle

/-- Multiplicative curvature ratio. -/
def curvatureRatio (T : PositiveResolutionTriangle) : ℝ≥0 :=
  T.first * T.second / T.composite

theorem one_le_curvatureRatio (T : PositiveResolutionTriangle) :
    1 ≤ T.curvatureRatio := by
  exact (one_le_div₀ T.composite_pos).2 T.submultiplicative

/-- Logarithmic composition curvature. -/
def logCurvature (T : PositiveResolutionTriangle) : ℝ :=
  Real.log (T.first : ℝ) + Real.log (T.second : ℝ) -
    Real.log (T.composite : ℝ)

theorem logCurvature_nonneg (T : PositiveResolutionTriangle) :
    0 ≤ T.logCurvature := by
  have hf : (0 : ℝ) < T.first := by exact_mod_cast T.first_pos
  have hs : (0 : ℝ) < T.second := by exact_mod_cast T.second_pos
  have hc : (0 : ℝ) < T.composite := by exact_mod_cast T.composite_pos
  have hle : (T.composite : ℝ) ≤ (T.first : ℝ) * (T.second : ℝ) := by
    exact_mod_cast T.submultiplicative
  have hlog :
      Real.log (T.composite : ℝ) ≤
        Real.log ((T.first : ℝ) * (T.second : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn hc (mul_pos hf hs) hle
  rw [Real.log_mul hf.ne' hs.ne'] at hlog
  exact sub_nonneg.mpr hlog

end PositiveResolutionTriangle

/-- Additive curvature of two tensions and their composite tension. -/
def tensionCurvature (a b ab : ℝ) : ℝ := a + b - ab

/-- Gauge action on an edge tension. -/
def gaugeTension (source target tension : ℝ) : ℝ :=
  source + tension - target

/-- Curvature is invariant under local gauge shifts. -/
theorem tensionCurvature_gauge_invariant
    (s₀ s₁ s₂ a b ab : ℝ) :
    tensionCurvature (gaugeTension s₀ s₁ a) (gaugeTension s₁ s₂ b)
        (gaugeTension s₀ s₂ ab) =
      tensionCurvature a b ab := by
  simp only [tensionCurvature, gaugeTension]
  ring

/-- Exact two-cocycle identity forced by associativity. -/
theorem tensionCurvature_two_cocycle (a b c ab bc abc : ℝ) :
    tensionCurvature a b ab + tensionCurvature ab c abc =
      tensionCurvature b c bc + tensionCurvature a bc abc := by
  simp only [tensionCurvature]
  ring

end

end GaloisForLFunctions.HTGeometry
