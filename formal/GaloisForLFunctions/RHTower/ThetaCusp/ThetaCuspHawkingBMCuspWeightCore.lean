import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularCuspWeight

/-! Multiplication of the original modular differential core by the constructed cusp weights. -/
open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The literal hyperbolic frame derivative retains both product-rule contributions. -/
theorem weightedDeriv_mul (f g : UpperHalfPlane → ℂ) (hf : ChartSmooth f) (hg : ChartSmooth g)
    (v : ℂ) (z : UpperHalfPlane) :
    weightedDeriv v (fun w => f w*g w) z =
      weightedDeriv v f z*g z+f z*weightedDeriv v g z := by
  have hF := ((hf z).differentiableAt (by simp)).hasFDerivAt
  have hG := ((hg z).differentiableAt (by simp)).hasFDerivAt
  have hprod := hF.mul hG
  unfold weightedDeriv
  change (z.im:ℂ)*fderiv ℝ ((f ∘ UpperHalfPlane.ofComplex)*(g ∘ UpperHalfPlane.ofComplex))
      (z:ℂ) v = _
  rw [hprod.fderiv]
  simp only [add_apply,smul_apply,
    Function.comp_apply,UpperHalfPlane.ofComplex_apply,smul_eq_mul]
  ring

end
end RHTower.D4BMModularCore

namespace RHTower.D4BMJointWave
open D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The bounded weight preserves the original full modular core and its quotient support. -/
def cuspWeightedCore (N : ℝ) (hN : 0 < N) (f : CoreField) : CoreField where
  field z := modularCuspWeight N z*f.field z
  smooth z := (modularCuspWeight_smooth N hN z).mul (f.smooth z)
  invariant γ z := by rw [modularCuspWeight_invariant,f.invariant]
  compact := by
    obtain ⟨K,hK,hf⟩ := f.compact
    refine ⟨K,hK,?_⟩
    intro z hz hn
    change modularCuspWeight N z*f.field z = 0
    rw [hf z hz hn,mul_zero]

/-- On the original cell the horizontal derivative has no commutator term. -/
theorem cuspWeightedCore_horizontal (N : ℝ) (hN : 0 < N) (f : CoreField)
    (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    weightedDeriv 1 (cuspWeightedCore N hN f).field z =
      modularCuspWeight N z*weightedDeriv 1 f.field z := by
  rw [cuspWeightedCore,weightedDeriv_mul _ _ (modularCuspWeight_smooth N hN) f.smooth,
    modularCuspWeight_horizontal_zero N hN z hz,zero_mul,zero_add]

/-- The vertical cutoff-gradient contribution is retained in the same original core. -/
theorem cuspWeightedCore_vertical (N : ℝ) (hN : 0 < N) (f : CoreField) (z : UpperHalfPlane) :
    weightedDeriv Complex.I (cuspWeightedCore N hN f).field z =
      weightedDeriv Complex.I (modularCuspWeight N) z*f.field z+
        modularCuspWeight N z*weightedDeriv Complex.I f.field z :=
  weightedDeriv_mul _ _ (modularCuspWeight_smooth N hN) f.smooth _ _

end
end RHTower.D4BMJointWave
