import Mathlib

/-!
# Mellin poles force boundary growth

A Dirichlet-type function `D` recovered from a Mellin transform through the Gamma factor,
`mellin f = Γ · D`, inherits growth information from `D`'s singularities.  If `D` fails to be
holomorphic at a point `ρ` in the right half-plane, then the transformed profile `f` cannot decay
(or stay bounded) fast enough at the origin: `f` is not `O(x^{-b})` for any `b < Re ρ`
(`not_isBigO_zero_of_mellin_eq_Gamma_mul`).

The mechanism is two elementary steps.  A non-differentiable factor survives multiplication by a
holomorphic nonvanishing factor (`not_differentiableAt_of_eventuallyEq_mul`), so the Mellin transform
`Γ · D` is non-holomorphic at `ρ`; and Mellin transforms of functions with controlled decay are
holomorphic to the right of their abscissa (`mellin_differentiableAt_of_isBigO_rpow_exp`), whose
contrapositive is exactly the boundary-growth statement.  This converts a Dirichlet pole frontier into
a radial blow-up of the associated power-series profile.
-/

open Complex Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- **Non-holomorphy survives a nonvanishing holomorphic factor.**  If `f = g · h` near `ρ` with `g`
holomorphic and nonzero at `ρ`, then non-differentiability of `h` at `ρ` forces non-differentiability
of `f` there (else `h = f / g` would be differentiable). -/
theorem not_differentiableAt_of_eventuallyEq_mul {f g h : ℂ → ℂ} {ρ : ℂ}
    (hfg : ∀ᶠ s in 𝓝 ρ, f s = g s * h s)
    (hg : DifferentiableAt ℂ g ρ) (hg0 : g ρ ≠ 0)
    (hh : ¬ DifferentiableAt ℂ h ρ) :
    ¬ DifferentiableAt ℂ f ρ := by
  intro hf
  apply hh
  have hdiv : DifferentiableAt ℂ (fun s => f s / g s) ρ := hf.div hg hg0
  refine hdiv.congr_of_eventuallyEq ?_
  filter_upwards [hfg, hg.continuousAt.eventually_ne hg0] with s hs hsg
  rw [hs, mul_comm (g s) (h s), mul_div_assoc, div_self hsg, mul_one]

/-- **Non-holomorphy of a Mellin transform forbids origin decay.**  Contrapositive of the Mellin
holomorphy criterion: if `mellin f` is not differentiable at `ρ`, yet `f` decays exponentially at
infinity and is locally integrable, then `f` is not `O(x^{-b})` at the origin for any `b < Re ρ`. -/
theorem not_isBigO_zero_rpow_of_not_differentiableAt_mellin {f : ℝ → ℂ} {ρ : ℂ} {a b : ℝ}
    (ha : 0 < a) (hint : LocallyIntegrableOn f (Set.Ioi 0) volume)
    (htop : f =O[atTop] fun t => Real.exp (-a * t)) (hb : b < ρ.re)
    (hnd : ¬ DifferentiableAt ℂ (mellin f) ρ) :
    ¬ (f =O[𝓝[>] 0] fun x => (x : ℝ) ^ (-b)) :=
  fun hzero => hnd (mellin_differentiableAt_of_isBigO_rpow_exp ha hint htop hzero hb)

/-- **A right half-plane Dirichlet pole forces boundary growth.**  If `mellin f = Γ · D` near `ρ`
with `Re ρ > 0` and `D` is not holomorphic at `ρ`, then—given exponential decay of `f` at infinity—
`f` is not `O(x^{-b})` at the origin for any `b < Re ρ`.  Combining the two elementary steps: `Γ` is
holomorphic and nonzero on the right half-plane, so `Γ · D` is non-holomorphic at `ρ`, and the Mellin
holomorphy criterion then rules out the origin decay. -/
theorem not_isBigO_zero_of_mellin_eq_Gamma_mul {f : ℝ → ℂ} {D : ℂ → ℂ} {ρ : ℂ} {a b : ℝ}
    (ha : 0 < a) (hint : LocallyIntegrableOn f (Set.Ioi 0) volume)
    (htop : f =O[atTop] fun t => Real.exp (-a * t)) (hb : b < ρ.re) (hρ : 0 < ρ.re)
    (hMellin : ∀ᶠ s in 𝓝 ρ, mellin f s = Complex.Gamma s * D s)
    (hpole : ¬ DifferentiableAt ℂ D ρ) :
    ¬ (f =O[𝓝[>] 0] fun x => (x : ℝ) ^ (-b)) := by
  refine not_isBigO_zero_rpow_of_not_differentiableAt_mellin ha hint htop hb ?_
  refine not_differentiableAt_of_eventuallyEq_mul hMellin ?_ ?_ hpole
  · exact Complex.differentiableAt_Gamma ρ (fun m h => by rw [h] at hρ; simp at hρ; linarith)
  · exact Complex.Gamma_ne_zero (fun m h => by rw [h] at hρ; simp at hρ; linarith)

end GaloisForLFunctions.HTGeometry
