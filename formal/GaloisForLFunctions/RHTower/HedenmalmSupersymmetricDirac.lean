import GaloisForLFunctions.RHTower.HedenmalmShiftedSourceEquationExact
import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Supersymmetric Dirac operator of the closed Hedenmalm derivative

This module constructs the actual off-diagonal unbounded operator

`Q = [[0, A†], [A, 0]]`

on the Hilbert direct sum.  Its nonreal resolvent is built from the compact graph coordinate of
`A`, rather than postulated abstractly.
-/

open Complex Function MeasureTheory Module Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmClosedWeightedDerivative

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmThetaSource

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev D := WithLp 2 (H × H)

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance : CompleteSpace thetaCentered := thetaCentered_isClosed.completeSpace_coe

/-! ### Bounded Gram inverse used by the nonreal Dirac resolvent -/

/-- Coercive bounded Gram operator `1 + B†B` on the centered graph coordinate. -/
def thetaDiracGram : thetaCentered →L[ℂ] thetaCentered :=
  1 + thetaCenteredSourceInverse.adjoint.comp thetaCenteredSourceInverse

theorem thetaDiracGram_reCoercive (k : thetaCentered) :
    1 * ‖k‖ ^ 2 ≤ (inner ℂ (thetaDiracGram k) k).re := by
  calc
    1 * ‖k‖ ^ 2 ≤ ‖k‖ ^ 2 + ‖thetaCenteredSourceInverse k‖ ^ 2 := by
      rw [one_mul]
      exact le_add_of_nonneg_right (sq_nonneg _)
    _ = (inner ℂ (thetaDiracGram k) k).re := by
      rw [thetaDiracGram, add_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply, inner_add_left,
        thetaCenteredSourceInverse.adjoint_inner_left, Complex.add_re]
      exact congrArg₂ (fun a b : ℝ => a + b)
        (norm_sq_eq_re_inner (𝕜 := ℂ) k)
        (norm_sq_eq_re_inner (𝕜 := ℂ) (thetaCenteredSourceInverse k))

theorem thetaDiracGram_injective : Function.Injective thetaDiracGram := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hco := thetaDiracGram_reCoercive (x - y)
  have hzero : thetaDiracGram (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  simp only [hzero, inner_zero_left, Complex.zero_re, one_mul] at hco
  have hnorm : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact norm_eq_zero.mp hnorm

theorem thetaDiracGram_surjective : Function.Surjective thetaDiracGram :=
  ContinuousLinearMap.surjective_of_reCoercive (c := 1) one_pos
    thetaDiracGram_reCoercive

/-- Bounded inverse of `1 + B†B`. -/
def thetaDiracGramEquiv : thetaCentered ≃L[ℂ] thetaCentered :=
  ContinuousLinearEquiv.ofBijective thetaDiracGram
    (LinearMap.ker_eq_bot.mpr thetaDiracGram_injective)
    (LinearMap.range_eq_top.mpr thetaDiracGram_surjective)

def thetaDiracGramInverse : thetaCentered →L[ℂ] thetaCentered :=
  thetaDiracGramEquiv.symm.toContinuousLinearMap

theorem thetaDiracGram_apply_inverse (k : thetaCentered) :
    thetaDiracGram (thetaDiracGramInverse k) = k :=
  thetaDiracGramEquiv.apply_symm_apply k

theorem thetaDiracGram_inverse_apply (k : thetaCentered) :
    thetaDiracGramInverse (thetaDiracGram k) = k :=
  thetaDiracGramEquiv.symm_apply_apply k

/-! ### Actual off-diagonal partial operator -/

def thetaSupersymmetricDiracDomain : Submodule ℂ D where
  carrier := {p | p.ofLp.1 ∈ thetaWeightedDerivative.domain ∧
    p.ofLp.2 ∈ thetaWeightedDerivative.adjoint.domain}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  add_mem' := by
    rintro x y hx hy
    exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' := by
    intro c x hx
    exact ⟨Submodule.smul_mem _ c hx.1, Submodule.smul_mem _ c hx.2⟩

/-- The unbounded supersymmetric block `[[0,A†],[A,0]]` on its natural product domain. -/
def thetaSupersymmetricDirac : D →ₗ.[ℂ] D where
  domain := thetaSupersymmetricDiracDomain
  toFun :=
    { toFun := fun p => WithLp.toLp 2
        (thetaWeightedDerivative.adjoint ⟨p.1.ofLp.2, p.2.2⟩,
          thetaWeightedDerivative ⟨p.1.ofLp.1, p.2.1⟩)
      map_add' := by
        intro x y
        apply (WithLp.prodContinuousLinearEquiv 2 ℂ H H).injective
        apply Prod.ext
        · exact LinearPMap.map_add thetaWeightedDerivative.adjoint
            ⟨x.1.ofLp.2, x.2.2⟩ ⟨y.1.ofLp.2, y.2.2⟩
        · exact LinearPMap.map_add thetaWeightedDerivative
            ⟨x.1.ofLp.1, x.2.1⟩ ⟨y.1.ofLp.1, y.2.1⟩
      map_smul' := by
        intro c x
        apply (WithLp.prodContinuousLinearEquiv 2 ℂ H H).injective
        apply Prod.ext
        · exact LinearPMap.map_smul thetaWeightedDerivative.adjoint c
            ⟨x.1.ofLp.2, x.2.2⟩
        · exact LinearPMap.map_smul thetaWeightedDerivative c
            ⟨x.1.ofLp.1, x.2.1⟩ }

theorem thetaSupersymmetricDirac_domain :
    thetaSupersymmetricDirac.domain = thetaSupersymmetricDiracDomain := rfl

theorem thetaSupersymmetricDirac_apply
    (p : thetaSupersymmetricDirac.domain) :
    thetaSupersymmetricDirac p = WithLp.toLp 2
      (thetaWeightedDerivative.adjoint ⟨p.1.ofLp.2, p.2.2⟩,
        thetaWeightedDerivative ⟨p.1.ofLp.1, p.2.1⟩) := rfl

end HedenmalmClosedWeightedDerivative

end

end RHTower
