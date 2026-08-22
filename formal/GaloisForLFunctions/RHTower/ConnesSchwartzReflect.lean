import GaloisForLFunctions.RHTower.ConnesLogHalfLine

/-!
# Reflection of a Schwartz map, and the negative half line

Step 2 of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The negative half of `∫ G'(u) log|u| du = −PV ∫ G/u` follows from the positive half applied to the
reflected Schwartz map `u ↦ G(−u)`: reflection negates both the derivative and the
principal-value integrand, and the substitution `u ↦ −u` exchanges the two half lines.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The reflected Schwartz map `u ↦ G(−u)`. -/
def connesReflect (G : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) G

@[simp] theorem connesReflect_apply (G : 𝓢(ℝ, ℂ)) (u : ℝ) :
    (connesReflect G : ℝ → ℂ) u = (G : ℝ → ℂ) (-u) := rfl

/-- Reflection negates the derivative. -/
theorem connes_deriv_reflect (G : 𝓢(ℝ, ℂ)) (u : ℝ) :
    deriv ((connesReflect G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u
      = - deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-u) := by
  have hval : ((connesReflect G : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun v : ℝ => (G : ℝ → ℂ) (-v) := rfl
  rw [hval, deriv_comp_neg]

/-- Reflection negates the principal-value integrand. -/
theorem connes_pvIntegrand_reflect (G : 𝓢(ℝ, ℂ)) (v : ℝ) :
    connesPVintegrand ((connesReflect G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) v
      = - connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-v) := by
  have hzero : (connesReflect G : ℝ → ℂ) 0 = (G : ℝ → ℂ) 0 := by
    rw [connesReflect_apply, neg_zero]
  have hmem : (v ∈ {w : ℝ | |w| ≤ 1}) ↔ ((-v) ∈ {w : ℝ | |w| ≤ 1}) := by
    simp [abs_neg]
  rw [connesPVintegrand, connesPVintegrand, connesReflect_apply, hzero]
  by_cases hv : v ∈ {w : ℝ | |w| ≤ 1}
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hmem.mp hv)]
    push_cast
    rw [div_neg]
    ring
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun hc => hv (hmem.mpr hc))]
    push_cast
    rw [div_neg]
    ring

end

end GaloisForLFunctions.RHTower
