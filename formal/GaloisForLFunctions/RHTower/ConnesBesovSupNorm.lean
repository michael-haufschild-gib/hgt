import GaloisForLFunctions.RHTower.DeningerCapDerivBound
import GaloisForLFunctions.HTGeometry.SchwartzComplete

/-!
# The all-order Besov–Fourier supremum bound

A supporting estimate for §VII of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Throughout §VII Connes controls a test function and its derivatives by weighted `L¹` norms of the
Fourier transform.  (Connes' own equation (41) is a different statement — the fractional-multiplier
inequality, proved in `ConnesBesovSupInequality`.)  What is assembled here is the all-order
supremum bound: the corpus already owns the
one-order statements (`RHTower.norm_iterate_derivSCLM_le`,
`RHTower.integral_pow_norm_fourier_le`); this module assembles them into the all-order form: one
quantity `connesBesovSeminorm N` which is finite for every Schwartz function and dominates
`sup_x |h^{(n)}(x)|` for every `n ≤ N` simultaneously.

The additive shape `∑_{n ≤ N} ∫ (2π|ξ|)^n ‖ĥ(ξ)‖ dξ` is used rather than the multiplicative
`∫ (1+2π|ξ|)^N ‖ĥ‖` because each summand is separately a nonnegative integral, so dominating one
summand by the whole sum needs no integrability side condition at all.
-/

open MeasureTheory Real
open scoped FourierTransform SchwartzMap Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **The all-order Besov quantity.**  The weighted `L¹` norms of the Fourier transform, summed
over all orders up to `N`. -/
def connesBesovSeminorm (N : ℕ) (f : 𝓢(ℝ, ℂ)) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    ∫ ξ : ℝ, (2 * π * |ξ|) ^ n * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖

theorem connes_besov_term_nonneg (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    0 ≤ ∫ ξ : ℝ, (2 * π * |ξ|) ^ n * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖ := by
  refine integral_nonneg fun ξ => ?_
  have hpi : (0 : ℝ) ≤ π := Real.pi_pos.le
  have h1 : (0 : ℝ) ≤ (2 * π * |ξ|) ^ n := by positivity
  exact mul_nonneg h1 (norm_nonneg _)

theorem connes_besov_seminorm_nonneg (N : ℕ) (f : 𝓢(ℝ, ℂ)) :
    0 ≤ connesBesovSeminorm N f :=
  Finset.sum_nonneg fun n _ => connes_besov_term_nonneg n f

/-- **The all-order supremum bound.**  The supremum of *every* derivative of order at most `N` is
bounded by the one Besov quantity of order `N`. -/
theorem connes_besov_sup_bound {N n : ℕ} (hn : n ≤ N) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖iteratedDeriv n ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ≤ connesBesovSeminorm N f := by
  have hiter : ((GaloisForLFunctions.derivSCLM^[n]) f) x
      = iteratedDeriv n ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x := by
    rw [← GaloisForLFunctions.derivPowSCLM_apply]
    exact GaloisForLFunctions.coe_derivPowSCLM_apply n f x
  have hstep := _root_.RHTower.norm_iterate_derivSCLM_le n f x
  rw [hiter] at hstep
  refine le_trans hstep ?_
  refine Finset.single_le_sum (f := fun m : ℕ =>
    ∫ ξ : ℝ, (2 * π * |ξ|) ^ m * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖)
    (fun m _ => connes_besov_term_nonneg m f) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- The Besov quantity is finite: it is bounded by finitely many Schwartz seminorms of the Fourier
transform. -/
theorem connes_besov_le_schwartz_seminorms (N : ℕ) (f : 𝓢(ℝ, ℂ)) :
    connesBesovSeminorm N f
      ≤ ∑ n ∈ Finset.range (N + 1), (2 * π) ^ n * π *
          (SchwartzMap.seminorm ℂ n 0 (GaloisForLFunctions.fourierSCLM f)
            + SchwartzMap.seminorm ℂ (n + 2) 0 (GaloisForLFunctions.fourierSCLM f)) := by
  refine Finset.sum_le_sum fun n _ => _root_.RHTower.integral_pow_norm_fourier_le n f

end

end GaloisForLFunctions.RHTower
