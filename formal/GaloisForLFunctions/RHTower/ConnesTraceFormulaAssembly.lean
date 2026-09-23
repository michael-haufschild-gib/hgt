import GaloisForLFunctions.RHTower.ConnesTraceErrorRapidDecay
import GaloisForLFunctions.RHTower.ConnesTraceMainTerm

/-!
# §VII Theorem 4: the summed asymptotic

§VII (30)–(33) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`ConnesLatticeFiniteSupport` shows that only finitely many lattice elements contribute, so the
sums of Theorem 4 are finite sums.  This module sums the per-term expansion of
`ConnesCutoffTraceDecomposition` / `ConnesTraceErrorRapidDecay` over a finite index set and
identifies the constant term through Fourier inversion at the origin, giving

  `∑_q ∫_{|u| ≤ Λ²} ĝ_q(u) (2 log Λ − log|u|) du
      = 2 log Λ · ∑_q g_q(0)  −  ∑_q ∫ ĝ_q(u) log|u| du  +  O(Λ^{-N})`

for every `N` — which is Theorem 4's asymptotic, with `∑_q g_q(0) = ∑_q f(q) = h(1)` by Connes'
(14)/(31) (`ConnesTraceMainTerm`, `ConnesPeriodizationLift`) and `∑_q ∫ ĝ_q log|u|` the sum of the
local principal values by §V (`ConnesLocalTraceCore`).

Everything is unconditional: no hypothesis beyond the data (a finite index set and a family of
Schwartz functions).
-/

open MeasureTheory Real Filter Topology
open scoped SchwartzMap Real FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {ι : Type*}

/-- **§VII (31), summed.**  The constant term of the finite trace sum is `∑_q g_q(0)`. -/
theorem connes_trace4_mainTerm (s : Finset ι) (g : ι → 𝓢(ℝ, ℂ)) :
    (∑ i ∈ s, ∫ u : ℝ, (SchwartzMap.fourierTransformCLM ℂ (g i) : ℝ → ℂ) u)
      = ∑ i ∈ s, (g i) 0 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoe : ((SchwartzMap.fourierTransformCLM ℂ (g i) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = 𝓕 ((g i : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  rw [hcoe, connes_integral_fourier_eq_zero_value (g i)]

/-- **§VII Theorem 4, the analytic conclusion.**  The finite trace sum of (30) equals
`2 log Λ · ∑_q g_q(0) − ∑_q ∫ ĝ_q(u) log|u| du` up to an error that decays faster than every power
of the cut-off. -/
theorem connes_trace4_asymptotic (s : Finset ι) (g : ι → 𝓢(ℝ, ℂ)) (N : ℕ) :
    Tendsto (fun Λ : ℝ => Λ ^ N *
        ‖(∑ i ∈ s, ∫ u in {u : ℝ | |u| ≤ Λ ^ (2 : ℕ)},
              (SchwartzMap.fourierTransformCLM ℂ (g i) : ℝ → ℂ) u
                * (((2 * Real.log Λ - Real.log |u| : ℝ)) : ℂ))
            - (((2 * Real.log Λ : ℝ) : ℂ) * (∑ i ∈ s, (g i) 0)
                - ∑ i ∈ s, ∫ u : ℝ, (SchwartzMap.fourierTransformCLM ℂ (g i) : ℝ → ℂ) u
                    * ((Real.log |u| : ℝ) : ℂ))‖)
      atTop (𝓝 0) := by
  set G : ι → 𝓢(ℝ, ℂ) := fun i => SchwartzMap.fourierTransformCLM ℂ (g i) with hG
  set Rem : ι → ℝ → ℂ := fun i Λ =>
    (∫ u in {u : ℝ | |u| ≤ Λ ^ (2 : ℕ)}, (G i : ℝ → ℂ) u * (((2 * Real.log Λ - Real.log |u| : ℝ)) : ℂ))
      - (((2 * Real.log Λ : ℝ) : ℂ) * (∫ u : ℝ, (G i : ℝ → ℂ) u)
          - ∫ u : ℝ, (G i : ℝ → ℂ) u * ((Real.log |u| : ℝ) : ℂ)) with hRem
  have hper : ∀ i : ι, Tendsto (fun Λ : ℝ => Λ ^ N * ‖Rem i Λ‖) atTop (𝓝 0) := by
    intro i
    exact connes_cutoffTrace_remainder_rapidDecay (G i) N
  have hsum : Tendsto (fun Λ : ℝ => ∑ i ∈ s, Λ ^ N * ‖Rem i Λ‖) atTop (𝓝 0) := by
    have := tendsto_finsetSum s (fun i (_ : i ∈ s) => hper i)
    simpa using this
  have hEq : ∀ Λ : ℝ,
      (∑ i ∈ s, ∫ u in {u : ℝ | |u| ≤ Λ ^ (2 : ℕ)}, (G i : ℝ → ℂ) u
            * (((2 * Real.log Λ - Real.log |u| : ℝ)) : ℂ))
          - (((2 * Real.log Λ : ℝ) : ℂ) * (∑ i ∈ s, (g i) 0)
              - ∑ i ∈ s, ∫ u : ℝ, (G i : ℝ → ℂ) u * ((Real.log |u| : ℝ) : ℂ))
        = ∑ i ∈ s, Rem i Λ := by
    intro Λ
    rw [hRem]
    simp only []
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      connes_trace4_mainTerm s g]
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with Λ hΛ
    exact mul_nonneg (pow_nonneg hΛ N) (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with Λ hΛ
    rw [hEq Λ]
    calc Λ ^ N * ‖∑ i ∈ s, Rem i Λ‖
        ≤ Λ ^ N * ∑ i ∈ s, ‖Rem i Λ‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hΛ N)
      _ = ∑ i ∈ s, Λ ^ N * ‖Rem i Λ‖ := by rw [Finset.mul_sum]

end

end GaloisForLFunctions.RHTower
