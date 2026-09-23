import GaloisForLFunctions.RHTower.ConnesTraceFormulaStatement
import GaloisForLFunctions.RHTower.ConnesTwistedWeilChange

/-!
# §VII Theorem 4 with the local Weil terms

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068, §VII Theorem 4:

  `Trace(R_Λ U(h)) = 2 h(1) log' Λ + ∑_v ∫'_{k_v^*} h(u^{-1})/|1−u| d^*u + o(1)`.

`ConnesTraceFormulaStatement` proves the asymptotic with the logarithmic term written as
`−∑_q ∫ ĝ_q(u) log|u| du`.  `ConnesTwistedWeilChange` identifies each such term with Connes'
regularized local Weil integral, so the two combine into Theorem 4 verbatim.  The error is
`O(Λ^{-N})` for every `N`, stronger than the `o(1)` of the paper.
-/

open MeasureTheory Real Filter Topology Set
open scoped SchwartzMap Real FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {ι : Type*}

/-- The regularized local Weil integral is the Fourier log moment of the twisted chart. -/
theorem connes_trace4_weil_local (f : ℝ → ℂ) (q : ℝ) (G : 𝓢(ℝ, ℂ)) (W : ℂ)
    (hG : ∀ u : ℝ, (G : ℝ → ℂ) u = connesTwistedChart f q u)
    (hW : Tendsto (fun ε : ℝ =>
        (∫ u in {u : ℝ | ε ≤ |u - 1|}, connesTwistedWeilIntegrand f q u)
          + f q * ((Real.log ε + Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 W)) :
    W = - ∫ u : ℝ, ((SchwartzMap.fourierTransformCLM ℂ G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u
        * ((Real.log |u| : ℝ) : ℂ) := by
  have hlim := tendsto_nhds_unique hW (connes_arch_weil_regularized f q G hG)
  rw [hlim, connesFourierLogMoment]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ((SchwartzMap.fourierTransformCLM ℂ G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)
      = ((SchwartzMap.fourierTransformCLM ℂ G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log |u| : ℝ) : ℂ)
  rw [Real.log_abs]

/-- **§VII Theorem 4, verbatim.**  If for each lattice element the regularized local Weil integral
converges to `W i`, then the cut-off trace sum is
`2 h(1) log' Λ + ∑_q W_q + O(Λ^{-N})` for every `N`. -/
theorem connes_trace4_weil (s : Finset ι) (g : ι → 𝓢(ℝ, ℂ)) (qq : ι → ℝ) (f : ℝ → ℂ)
    (h1 : ℂ) (W : ι → ℂ)
    (hchart : ∀ i ∈ s, ∀ u : ℝ, (g i) u = connesTwistedChart f (qq i) u)
    (hlift : (∑ i ∈ s, f (qq i)) = h1)
    (hW : ∀ i ∈ s, Tendsto (fun ε : ℝ =>
        (∫ u in {u : ℝ | ε ≤ |u - 1|}, connesTwistedWeilIntegrand f (qq i) u)
          + f (qq i)
            * ((Real.log ε + Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (W i))) (N : ℕ) :
    Tendsto (fun Λ : ℝ => Λ ^ N *
        ‖(∑ i ∈ s, ∫ u in {u : ℝ | |u| ≤ Λ ^ (2 : ℕ)},
              (SchwartzMap.fourierTransformCLM ℂ (g i) : ℝ → ℂ) u
                * (((2 * Real.log Λ - Real.log |u| : ℝ)) : ℂ))
            - (((2 * Real.log Λ : ℝ) : ℂ) * h1 + ∑ i ∈ s, W i)‖)
      atTop (𝓝 0) := by
  have hzero : ∀ i ∈ s, (g i) 0 = f (qq i) := by
    intro i hi
    rw [hchart i hi 0, connesTwistedChart_zero]
  have hWsum : (∑ i ∈ s, W i)
      = - ∑ i ∈ s, ∫ u : ℝ, (SchwartzMap.fourierTransformCLM ℂ (g i) : ℝ → ℂ) u
          * ((Real.log |u| : ℝ) : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact connes_trace4_weil_local f (qq i) (g i) (W i) (hchart i hi) (hW i hi)
  have hstate := connes_trace4_statement s g qq f h1 hzero hlift N
  refine hstate.congr fun Λ => ?_
  rw [hWsum]
  ring_nf

/-- The hypothesis of `connes_trace4_weil` always has a model: the regularized local Weil integral
does converge, to the Fourier log moment of the twisted chart. -/
theorem connes_trace4_weil_hypothesis_model (f : ℝ → ℂ) (q : ℝ) (G : 𝓢(ℝ, ℂ))
    (hG : ∀ u : ℝ, (G : ℝ → ℂ) u = connesTwistedChart f q u) :
    Tendsto (fun ε : ℝ =>
        (∫ u in {u : ℝ | ε ≤ |u - 1|}, connesTwistedWeilIntegrand f q u)
          + f q * ((Real.log ε + Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (- connesFourierLogMoment G)) :=
  connes_arch_weil_regularized f q G hG

end

end GaloisForLFunctions.RHTower
