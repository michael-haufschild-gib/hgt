/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael
-/
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Common-translation invariance of the CCM correlation

This is the literal content of Connes--Consani--Moscovici (2025), Lemma 2.2.  We define their
`L¹(ℝ)` source functions, translation, involution, additive convolution, and even Hermitian
correlation `q`.  Translating both inputs by the same real amount leaves `f* * g` and `q(f,g)`
unchanged.
-/

noncomputable section

open MeasureTheory Complex
open scoped ComplexConjugate

namespace RHTower

/-- A literal complex `L¹(ℝ,dx)` source function. -/
structure CCML1Source where
  toFun : ℝ → ℂ
  integrable : Integrable toFun (volume : Measure ℝ)

instance : CoeFun CCML1Source (fun _ => ℝ → ℂ) := ⟨CCML1Source.toFun⟩

/-- CCM translation convention `f_a(x) = f(x-a)`. -/
def CCML1Source.translate (f : CCML1Source) (a : ℝ) : CCML1Source where
  toFun x := f (x - a)
  integrable := f.integrable.comp_sub_right a

/-- CCM involution `f*(y) = conj (f(-y))`. -/
def ccmL1Involution (f : CCML1Source) (y : ℝ) : ℂ :=
  conj (f (-y))

/-- CCM additive convolution `(f * g)(y) = ∫ f(x) g(y-x) dx`. -/
def ccmL1Convolution (f g : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, f x * g (y - x)

/-- The source correlation `(f* * g)(y)`. -/
def ccmStarConvolution (f g : CCML1Source) (y : ℝ) : ℂ :=
  ccmL1Convolution (ccmL1Involution f) g y

/-- Source equation (2.5), the even Hermitian correlation. -/
def ccmEvenHermitianCorrelation (f g : CCML1Source) (y : ℝ) : ℂ :=
  ccmStarConvolution f g y + ccmStarConvolution f g (-y)

/-- Common translation leaves the literal source convolution `(f* * g)` unchanged. -/
theorem ccmStarConvolution_translate (f g : CCML1Source) (a y : ℝ) :
    ccmStarConvolution (f.translate a) (g.translate a) y =
      ccmStarConvolution f g y := by
  let F : ℝ → ℂ := fun x => conj (f (-x)) * g (y - x)
  have hshift := integral_add_right_eq_self (μ := (volume : Measure ℝ)) F a
  change (∫ x : ℝ, conj (f (-x - a)) * g (y - x - a)) =
    ∫ x : ℝ, conj (f (-x)) * g (y - x)
  convert hshift using 1 <;> apply integral_congr_ae <;> filter_upwards with x <;>
    dsimp [F] <;> congr 2 <;> ring

/-- CCM Lemma 2.2: the even correlation `q` is common-translation invariant. -/
theorem ccmEvenHermitianCorrelation_translate (f g : CCML1Source) (a : ℝ) :
    ccmEvenHermitianCorrelation (f.translate a) (g.translate a) =
      ccmEvenHermitianCorrelation f g := by
  funext y
  unfold ccmEvenHermitianCorrelation
  rw [ccmStarConvolution_translate, ccmStarConvolution_translate]

end RHTower
