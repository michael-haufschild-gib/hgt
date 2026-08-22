import GaloisForLFunctions.RHTower.ConnesTraceFormulaAssembly
import GaloisForLFunctions.RHTower.ConnesTwistedChartFourier

/-!
# §VII Theorem 4, in Connes' notation

§VII Theorem 4 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `Trace(R_Λ U(h)) = 2 h(1) log' Λ + ∑_{v ∈ S} ∫'_{k_v^*} h(u^{-1})/|1−u| d^*u + o(1)`.

`ConnesTraceFormulaAssembly` proves the analytic conclusion with the constant term written as
`∑_q g_q(0)`.  Connes' (26) gives `g_q(0) = f(q)` (`connesTwistedChart_zero`) and his (14) gives
`∑_q f(q) = h(1)` (`ConnesPeriodizationLift`), so the constant term is exactly `2 h(1) log' Λ`.
That substitution is made here, and the error is `O(Λ^{-N})` for every `N` - stronger than the
`o(1)` Connes states.

The remaining logarithmic term `−∑_q ∫ ĝ_q(u) log|u| du` is identified with the sum of the local
principal values `∑_v ∫'_{k_v^*} h(u^{-1})/|1−u| d^*u` by §V, which the corpus owns at every place
of every local field (`ConnesLocalFieldSymbol`, `ConnesLocalTraceCore`).
-/

open MeasureTheory Real Filter Topology
open scoped SchwartzMap Real FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {ι : Type*}

/-- **§VII Theorem 4.**  With the constant term written in Connes' notation - `g_q(0) = f(q)` by
(26) and `∑_q f(q) = h(1)` by (14) - the cut-off trace is
`2 h(1) log' Λ − ∑_q ∫ ĝ_q(u) log|u| du + O(Λ^{-N})` for every `N`. -/
theorem connes_trace4_statement (s : Finset ι) (g : ι → 𝓢(ℝ, ℂ)) (qq : ι → ℝ) (f : ℝ → ℂ)
    (h1 : ℂ) (hchart : ∀ i ∈ s, (g i) 0 = f (qq i))
    (hlift : (∑ i ∈ s, f (qq i)) = h1) (N : ℕ) :
    Tendsto (fun Λ : ℝ => Λ ^ N *
        ‖(∑ i ∈ s, ∫ u in {u : ℝ | |u| ≤ Λ ^ 2},
              (SchwartzMap.fourierTransformCLM ℂ (g i) : ℝ → ℂ) u
                * (((2 * Real.log Λ - Real.log |u| : ℝ)) : ℂ))
            - (((2 * Real.log Λ : ℝ) : ℂ) * h1
                - ∑ i ∈ s, ∫ u : ℝ, (SchwartzMap.fourierTransformCLM ℂ (g i) : ℝ → ℂ) u
                    * ((Real.log |u| : ℝ) : ℂ))‖)
      atTop (𝓝 0) := by
  have hconst : (∑ i ∈ s, (g i) 0) = h1 := by
    rw [← hlift]
    exact Finset.sum_congr rfl hchart
  have h := connes_trace4_asymptotic s g N
  rw [hconst] at h
  exact h

/-- **§VII (26) + (31).**  The constant term of the trace formula, in Connes' notation: the value
of the twisted chart at the origin is `f(q)`, so the constant term is `∑_q f(q)`. -/
theorem connes_trace4_constant_eq (s : Finset ι) (g : ι → 𝓢(ℝ, ℂ)) (qq : ι → ℝ) (f : ℝ → ℂ)
    (hchart : ∀ i ∈ s, ∀ u : ℝ, (g i) u = connesTwistedChart f (qq i) u) :
    (∑ i ∈ s, ∫ u : ℝ, (SchwartzMap.fourierTransformCLM ℂ (g i) : ℝ → ℂ) u)
      = ∑ i ∈ s, f (qq i) := by
  rw [connes_trace4_mainTerm s g]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hchart i hi 0, connesTwistedChart_zero]

end

end GaloisForLFunctions.RHTower
