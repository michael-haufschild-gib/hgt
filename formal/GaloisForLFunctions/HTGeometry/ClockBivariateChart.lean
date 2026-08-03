import Mathlib.Analysis.Calculus.FDeriv.Partial
import GaloisForLFunctions.HTGeometry.ClockGoursatMixed

/-!
# From partial derivatives to the chart calculus

The Goursat solution is a function of two real variables given by its partial derivatives, whereas
the chart calculus works with functions on `Fin 2 → ℝ` and reads their partial derivatives off the
total derivative. The bridge is the classical theorem that continuous partial derivatives imply
total differentiability, composed with the linear identification `x ↦ (x⁰, x¹)`.

This file records that bridge: a bivariate function whose two partial derivatives exist near a point
and are continuous there yields a chart function which is differentiable, with `coordPartial` in the
two coordinate directions equal to those partial derivatives.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Filter

/-- The linear identification of a two-dimensional chart with a plane. -/
noncomputable def pairCLM : (Fin (1 + 1) → ℝ) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + 1) => ℝ) 0).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + 1) => ℝ) 1)

theorem pairCLM_apply (x : Fin (1 + 1) → ℝ) : pairCLM x = (x 0, x 1) := rfl

/-- The scalar-to-operator embedding used to state a real derivative as a differential. -/
noncomputable def toCLM (a : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a

theorem toCLM_apply (a z : ℝ) : toCLM a z = z * a := rfl

theorem continuous_toCLM : Continuous toCLM := by
  unfold toCLM
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous

/-- **Continuous partial derivatives give a differentiable chart function.** -/
theorem hasFDerivAt_bivariateChart {f A B : ℝ → ℝ → ℝ} {x : Fin (1 + 1) → ℝ}
    (dA : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasDerivAt (fun z => f z v.2) (A v.1 v.2) v.1)
    (dB : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasDerivAt (fun z => f v.1 z) (B v.1 v.2) v.2)
    (cA : ContinuousAt (fun p : ℝ × ℝ => A p.1 p.2) (x 0, x 1))
    (cB : ContinuousAt (fun p : ℝ × ℝ => B p.1 p.2) (x 0, x 1)) :
    HasFDerivAt (fun y : Fin (1 + 1) → ℝ => f (y 0) (y 1))
      (((toCLM (A (x 0) (x 1))).coprod (toCLM (B (x 0) (x 1)))).comp pairCLM) x := by
  have dA' : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasFDerivAt (fun z => f z v.2) (Function.uncurry (fun s t => toCLM (A s t)) v) v.1 := by
    filter_upwards [dA] with v hv
    exact hv.hasFDerivAt
  have dB' : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasFDerivAt (fun z => f v.1 z) (Function.uncurry (fun s t => toCLM (B s t)) v) v.2 := by
    filter_upwards [dB] with v hv
    exact hv.hasFDerivAt
  have cA' : ContinuousAt (Function.uncurry fun s t => toCLM (A s t)) (x 0, x 1) :=
    continuous_toCLM.continuousAt.comp cA
  have cB' : ContinuousAt (Function.uncurry fun s t => toCLM (B s t)) (x 0, x 1) :=
    continuous_toCLM.continuousAt.comp cB
  have hstrict := hasStrictFDerivAt_uncurry_coprod
    (f := f) (f₁ := fun s t => toCLM (A s t)) (f₂ := fun s t => toCLM (B s t))
    dA' dB' cA' cB'
  have huncurry : HasFDerivAt (Function.uncurry f)
      ((toCLM (A (x 0) (x 1))).coprod (toCLM (B (x 0) (x 1)))) (x 0, x 1) :=
    hstrict.hasFDerivAt
  have hpair : HasFDerivAt (fun y : Fin (1 + 1) → ℝ => ((y 0, y 1) : ℝ × ℝ)) pairCLM x :=
    pairCLM.hasFDerivAt
  exact huncurry.comp x hpair

theorem differentiableAt_bivariateChart {f A B : ℝ → ℝ → ℝ} {x : Fin (1 + 1) → ℝ}
    (dA : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasDerivAt (fun z => f z v.2) (A v.1 v.2) v.1)
    (dB : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasDerivAt (fun z => f v.1 z) (B v.1 v.2) v.2)
    (cA : ContinuousAt (fun p : ℝ × ℝ => A p.1 p.2) (x 0, x 1))
    (cB : ContinuousAt (fun p : ℝ × ℝ => B p.1 p.2) (x 0, x 1)) :
    DifferentiableAt ℝ (fun y : Fin (1 + 1) → ℝ => f (y 0) (y 1)) x :=
  (hasFDerivAt_bivariateChart dA dB cA cB).differentiableAt

/-- **The chart partial derivatives are the bivariate ones.** -/
theorem coordPartial_bivariateChart_zero {f A B : ℝ → ℝ → ℝ} {x : Fin (1 + 1) → ℝ}
    (dA : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasDerivAt (fun z => f z v.2) (A v.1 v.2) v.1)
    (dB : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasDerivAt (fun z => f v.1 z) (B v.1 v.2) v.2)
    (cA : ContinuousAt (fun p : ℝ × ℝ => A p.1 p.2) (x 0, x 1))
    (cB : ContinuousAt (fun p : ℝ × ℝ => B p.1 p.2) (x 0, x 1)) :
    coordPartial 0 (fun y : Fin (1 + 1) → ℝ => f (y 0) (y 1)) x = A (x 0) (x 1) := by
  rw [coordPartial, (hasFDerivAt_bivariateChart dA dB cA cB).fderiv]
  simp [pairCLM_apply, toCLM_apply, Ne.symm fin_zero_ne_one]

theorem coordPartial_bivariateChart_one {f A B : ℝ → ℝ → ℝ} {x : Fin (1 + 1) → ℝ}
    (dA : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasDerivAt (fun z => f z v.2) (A v.1 v.2) v.1)
    (dB : ∀ᶠ v in nhds ((x 0, x 1) : ℝ × ℝ),
      HasDerivAt (fun z => f v.1 z) (B v.1 v.2) v.2)
    (cA : ContinuousAt (fun p : ℝ × ℝ => A p.1 p.2) (x 0, x 1))
    (cB : ContinuousAt (fun p : ℝ × ℝ => B p.1 p.2) (x 0, x 1)) :
    coordPartial 1 (fun y : Fin (1 + 1) → ℝ => f (y 0) (y 1)) x = B (x 0) (x 1) := by
  rw [coordPartial, (hasFDerivAt_bivariateChart dA dB cA cB).fderiv]
  simp [pairCLM_apply, toCLM_apply]

end GaloisForLFunctions.HTGeometry
