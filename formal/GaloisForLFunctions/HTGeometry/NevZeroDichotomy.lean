import GaloisForLFunctions.HTGeometry.NevanlinnaPluecker

/-!
# Zeros of the Nevanlinna combination are isolated

On an open set carrying uniform kernel bounds, the series defining `B` and `D` are holomorphic, so
`B(z)τ − D(z)` is analytic there and its zeros obey the identity-theorem dichotomy: near any
point it
either vanishes identically or has no other zero nearby.

The hypotheses are the same uniform bounds the holomorphy results of this file already take.
Getting
the dichotomy on all of `ℂ` — which is what a leaf construction needs — requires those bounds
globally, and that is the transfer left open in `ComplexKernelTransfer`.
-/

open scoped BigOperators
open Filter Topology

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The `B` entry as a series. -/
noncomputable def nevBseries (s : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' k, monicOrthoC s k z * secondKindC s k 0 /
    ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

/-- The `D` entry as a series. -/
noncomputable def nevDseries (s : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' k, monicOrthoC s k 0 * monicOrthoC s k z /
    ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

/-- **The Nevanlinna combination is analytic on a uniformly bounded open set.** -/
theorem analyticAt_nevCombination (h : PositiveMomentForm s) {U : Set ℂ} (hU : IsOpen U)
    {S0 P0 Sz : ℝ}
    (hS0 : ∀ n, kernelRoot s (fun j => monicOrthoC s j 0) n ≤ S0)
    (hP0 : ∀ n, kernelRoot s (fun j => secondKindC s j 0) n ≤ P0)
    (hUS : ∀ z ∈ U, ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n ≤ Sz)
    (tau : ℂ) {z : ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ (fun w => nevBseries s w * tau - nevDseries s w) z := by
  have hB : DifferentiableOn ℂ (fun w => nevBseries s w) U :=
    differentiableOn_nevB_series h U hU hP0 hUS
  have hD : DifferentiableOn ℂ (fun w => nevDseries s w) U :=
    differentiableOn_nevD_series h U hU hS0 hUS
  have hcomb : DifferentiableOn ℂ (fun w => nevBseries s w * tau - nevDseries s w) U :=
    (hB.mul_const tau).sub hD
  exact hcomb.analyticAt (hU.mem_nhds hz)

/-- **The identity-theorem dichotomy at a point.**  Near `z` the combination either vanishes
identically or has no other zero. -/
theorem eventually_eq_zero_or_eventually_ne_zero_nevCombination (h : PositiveMomentForm s)
    {U : Set ℂ} (hU : IsOpen U) {S0 P0 Sz : ℝ}
    (hS0 : ∀ n, kernelRoot s (fun j => monicOrthoC s j 0) n ≤ S0)
    (hP0 : ∀ n, kernelRoot s (fun j => secondKindC s j 0) n ≤ P0)
    (hUS : ∀ z ∈ U, ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n ≤ Sz)
    (tau : ℂ) {z : ℂ} (hz : z ∈ U) :
    (∀ᶠ w in 𝓝 z, nevBseries s w * tau - nevDseries s w = 0) ∨
      (∀ᶠ w in 𝓝[≠] z, nevBseries s w * tau - nevDseries s w ≠ 0) :=
  (analyticAt_nevCombination h hU hS0 hP0 hUS tau hz).eventually_eq_zero_or_eventually_ne_zero

end HTGeometry
