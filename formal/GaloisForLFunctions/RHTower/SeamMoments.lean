/-
Cross-level (seam) mixed second-moment Bohr identity.

`dpoly_mul` makes the product of two Dirichlet polynomials on possibly different supports a
Dirichlet polynomial with the convolution coefficients. So the mixed second moment `‖F·G‖²` is
the second moment of the product, and the second-moment Bohr transfer applies: the vertical time
average of `‖F·G‖²` equals the Steinhaus-model second moment `E‖(∑ aₙ Xₙ)(∑ bₙ Xₙ)‖²`, both equal
to the convolution diagonal `∑ (dpolyConv a b s t)²`. This is the native handle for correlating
two carriers (two levels) across the seam.
-/
import GaloisForLFunctions.RHTower.BohrMoments

open MeasureTheory intervalIntegral Filter Topology Complex Finset
open scoped Classical

namespace RHTower

open SteinhausModel

/-- **Cross-level (seam) second-moment Bohr identity.** For two carriers `F = ∑_{s} aₙ n^{-it}`
and `G = ∑_{t} bₙ n^{-it}` on possibly different supports, the vertical time average of
`‖F·G‖²` equals the Steinhaus-model second moment `E‖(∑ aₙ Xₙ)(∑ bₙ Xₙ)‖²`. Both collapse to
the convolution diagonal `∑ (dpolyConv a b s t)²`, via `dpoly_mul` / `model_mul`: the product of
two Dirichlet polynomials is a Dirichlet polynomial, so the mixed second moment is the second
moment of the product. -/
theorem tendsto_mixedSecondMoment_average_steinhaus
    (a b : ℕ → ℝ) (s t : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n) :
    Tendsto (fun U : ℝ => (∫ τ in (0:ℝ)..U, ‖dpoly a s τ * dpoly b t τ‖ ^ 2) / U) atTop
      (𝓝 (∫ ω, ‖(∑ n ∈ s, (a n : ℂ) * X n ω) * (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ 2
              ∂steinhausMeasure)) := by
  have hsne : ∀ n ∈ s, n ≠ 0 := fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 := fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hspos : ∀ k ∈ prodSupport s t, 1 ≤ k := fun k hk => one_le_of_mem_prodSupport hs ht hk
  have hmodel : ∫ ω, ‖(∑ n ∈ s, (a n : ℂ) * X n ω) * (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ 2
              ∂steinhausMeasure
        = ∑ k ∈ prodSupport s t, dpolyConv a b s t k ^ 2 := by
    have hrwM : ∀ ω : Omega,
        ‖(∑ n ∈ s, (a n : ℂ) * X n ω) * (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ 2
          = ‖∑ k ∈ prodSupport s t, (dpolyConv a b s t k : ℂ) * X k ω‖ ^ 2 := by
      intro ω; rw [model_mul a b s t hsne htne ω]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrwM)]
    exact integral_normSq_dpoly (dpolyConv a b s t) (prodSupport s t)
      (fun k hk => Nat.one_le_iff_ne_zero.mp (hspos k hk))
  rw [hmodel]
  have hrw : ∀ τ : ℝ,
      ‖dpoly a s τ * dpoly b t τ‖ ^ 2
        = ‖dpoly (dpolyConv a b s t) (prodSupport s t) τ‖ ^ 2 := by
    intro τ; rw [dpoly_mul a b s t hsne htne τ]
  simp_rw [hrw]
  have := tendsto_secondMoment_average (dpolyConv a b s t) (prodSupport s t) 0 hspos
  simpa only [zero_add] using this

end RHTower
