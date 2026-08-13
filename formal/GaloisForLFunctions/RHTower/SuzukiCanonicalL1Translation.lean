import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelApertureDerivative
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Measure

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

def realAddTranslationJoint : C(ℝ × ℝ, ℝ) where
  toFun p := p.1 + p.2
  continuous_toFun := continuous_fst.add continuous_snd

def realAddTranslationFamily : C(ℝ, C(ℝ, ℝ)) :=
  realAddTranslationJoint.curry

@[simp] theorem realAddTranslationFamily_apply (t x : ℝ) :
    realAddTranslationFamily t x = t + x := rfl

theorem measurePreserving_realAddTranslationFamily (t : ℝ) :
    MeasurePreserving (realAddTranslationFamily t) volume volume := by
  exact MeasureTheory.measurePreserving_add_left volume t

def realL1Translate (t : ℝ) (f : Lp ℂ 1 (volume : Measure ℝ)) :
    Lp ℂ 1 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (realAddTranslationFamily t)
    (measurePreserving_realAddTranslationFamily t) f

theorem realL1Translate_ae (t : ℝ) (f : Lp ℂ 1 (volume : Measure ℝ)) :
    (realL1Translate t f : ℝ → ℂ) =ᵐ[volume] fun x => f (t + x) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (measurePreserving_realAddTranslationFamily t)] with x hx
  simpa only [realL1Translate, Function.comp_apply,
    realAddTranslationFamily_apply] using hx

theorem continuous_realL1Translate (f : Lp ℂ 1 (volume : Measure ℝ)) :
    Continuous fun t : ℝ => realL1Translate t f := by
  exact (continuous_const : Continuous fun _ : ℝ => f).compMeasurePreservingLp
    realAddTranslationFamily.continuous
    measurePreserving_realAddTranslationFamily (by norm_num)

end RHTower
