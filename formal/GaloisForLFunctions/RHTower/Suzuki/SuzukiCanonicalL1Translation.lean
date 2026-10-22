import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelApertureDerivative
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Measure

/-!
# Continuity of translation in `L^1(ℝ)`

This module defines the translation operator `τ_t f(x) = f(t + x)` on `L^1(ℝ; ℂ)` as composition
with the measure-preserving map `x ↦ t + x`, and proves that translation is strongly continuous:
for every `f ∈ L^1(ℝ)` the orbit `t ↦ τ_t f` is continuous into `L^1(ℝ)`.

## Main results

- `realL1Translate_ae`: `τ_t f` agrees almost everywhere with `x ↦ f(t + x)`.
- `continuous_realL1Translate`: `t ↦ τ_t f` is continuous in `L^1(ℝ)`.

## Hypotheses

Unconditional.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

def realAddTranslationJoint : C(ℝ × ℝ, ℝ) where
  toFun p := p.1 + p.2
  continuous_toFun := continuous_fst.add continuous_snd

/-- The continuous family of real translations `t ↦ (x ↦ t + x)`. -/
def realAddTranslationFamily : C(ℝ, C(ℝ, ℝ)) :=
  realAddTranslationJoint.curry

@[simp] theorem realAddTranslationFamily_apply (t x : ℝ) :
    realAddTranslationFamily t x = t + x := rfl

theorem measurePreserving_realAddTranslationFamily (t : ℝ) :
    MeasurePreserving (realAddTranslationFamily t) volume volume := by
  exact MeasureTheory.measurePreserving_add_left volume t

/-- Translation `τ_t f(x) = f(t + x)` on `L^1(ℝ; ℂ)`, via composition with a measure-preserving
map. -/
def realL1Translate (t : ℝ) (f : Lp ℂ 1 (volume : Measure ℝ)) :
    Lp ℂ 1 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (realAddTranslationFamily t)
    (measurePreserving_realAddTranslationFamily t) f

/-- The translate `τ_t f` is almost everywhere equal to `x ↦ f(t + x)`. -/
theorem realL1Translate_ae (t : ℝ) (f : Lp ℂ 1 (volume : Measure ℝ)) :
    (realL1Translate t f : ℝ → ℂ) =ᵐ[volume] fun x => f (t + x) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (measurePreserving_realAddTranslationFamily t)] with x hx
  simpa only [realL1Translate, Function.comp_apply,
    realAddTranslationFamily_apply] using hx

/-- Strong continuity of translation: for `f ∈ L^1(ℝ)`, the orbit `t ↦ τ_t f` is continuous
in `L^1(ℝ)`. -/
theorem continuous_realL1Translate (f : Lp ℂ 1 (volume : Measure ℝ)) :
    Continuous fun t : ℝ => realL1Translate t f := by
  exact (continuous_const : Continuous fun _ : ℝ => f).compMeasurePreservingLp
    realAddTranslationFamily.continuous
    measurePreserving_realAddTranslationFamily (by norm_num)

end RHTower
