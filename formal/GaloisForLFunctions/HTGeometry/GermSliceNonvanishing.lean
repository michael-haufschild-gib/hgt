import GaloisForLFunctions.HTGeometry.GermWeierstrassPreparation
import GaloisForLFunctions.HTGeometry.SliceDivisionIndependence

/-!
# A regular germ has nowhere identically vanishing slices

Weierstrass preparation writes a function whose slice at the origin is not identically zero as a
monic polynomial in the distinguished coordinate times a nowhere vanishing factor.  The polynomial
is monic, hence nonzero, hence its value function does not vanish identically on any disc; so the
slice of the function at *every* parameter of the preparation polydisc is not identically zero
near any point of the disc.

This upgrades regularity at one point to regularity at every point of a polydisc, which is what
lets a divisor of the function be prepared in the same coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric Polynomial

variable {n : ℕ}

/-- **Regularity spreads over the preparation polydisc.** -/
theorem exists_polydisc_slice_ne_zero {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ))
    (hreg : ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ t δ : ℝ, 0 < t ∧ 0 < δ ∧ ∀ y : Fin n → ℂ, ‖y‖ < δ → ∀ z₀ : ℂ, ‖z₀‖ < t →
      ¬ (fun z : ℂ => f (Fin.cons z y)) =ᶠ[𝓝 z₀] 0 := by
  classical
  obtain ⟨r, hr, hfr⟩ := exists_ball_analyticOnNhd hf
  have hfd : DifferentiableOn ℂ f (ball (0 : Fin (n + 1) → ℂ) r) := hfr.differentiableOn
  obtain ⟨t, δ, d, a, u, htpos, hδpos, -, -, -, hmain⟩ :=
    HTGeometry.germ_weierstrass_preparation isOpen_ball (mem_ball_self hr) hfd hreg
  refine ⟨t, δ, htpos, hδpos, ?_⟩
  intro y hy z₀ hz₀ hcon
  have hyball : y ∈ ball (0 : Fin n → ℂ) δ := by simpa [mem_ball_zero_iff] using hy
  -- the monic polynomial of the preparation at the parameter `y`
  set Pol : Polynomial ℂ :=
    Polynomial.X ^ d + lowDegreePoly (fun j => a j y) d with hPol
  have hPolMonic : Pol.Monic := monic_X_pow_add (degree_lowDegreePoly_lt _ d)
  have hPolEval : ∀ z : ℂ, Pol.eval z = z ^ d + ∑ j ∈ Finset.range d, a j y * z ^ j := by
    intro z
    rw [hPol, eval_add, eval_pow, eval_X, eval_lowDegreePoly]
  -- the value function of the polynomial is entire
  have hana : AnalyticOnNhd ℂ (fun z : ℂ => Pol.eval z) Set.univ := by
    intro z _
    have hsum : (fun z : ℂ => ∑ j ∈ Finset.range d, a j y * z ^ j)
        = ∑ j ∈ Finset.range d, fun z : ℂ => a j y * z ^ j := by
      funext w
      simp
    have h1 : AnalyticAt ℂ (fun z : ℂ => z ^ d) z := (analyticAt_id (𝕜 := ℂ) (z := z)).pow d
    have h2 : AnalyticAt ℂ (fun z : ℂ => ∑ j ∈ Finset.range d, a j y * z ^ j) z := by
      rw [hsum]
      exact Finset.analyticAt_sum _ fun j _ =>
        analyticAt_const.mul ((analyticAt_id (𝕜 := ℂ) (z := z)).pow j)
    have h3 : AnalyticAt ℂ (fun z : ℂ => z ^ d + ∑ j ∈ Finset.range d, a j y * z ^ j) z :=
      h1.add h2
    exact h3.congr (Filter.Eventually.of_forall fun w => (hPolEval w).symm)
  -- the polynomial vanishes near `z₀`
  obtain ⟨ε, hε, hεspec⟩ := Metric.eventually_nhds_iff.mp hcon
  set ε' : ℝ := min ε (t - ‖z₀‖) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by linarith)
  have hvanish : ∀ z ∈ ball z₀ ε', Pol.eval z = 0 := by
    intro z hz
    have hzt : ‖z‖ < t := by
      have h1 : dist z z₀ < ε' := mem_ball.mp hz
      have h2 : ‖z - z₀‖ < t - ‖z₀‖ := lt_of_lt_of_le (by rwa [dist_eq_norm] at h1)
        (min_le_right _ _)
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ < t := by linarith
    have hzero : f (Fin.cons z y) = 0 :=
      hεspec (lt_of_lt_of_le (mem_ball.mp hz) (min_le_left _ _))
    obtain ⟨hfact, hune⟩ := hmain y hyball z hzt
    rw [hzero] at hfact
    have := (mul_eq_zero.mp hfact.symm).resolve_right hune
    rw [hPolEval]
    exact this
  have hev : (fun z : ℂ => Pol.eval z) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [Metric.ball_mem_nhds z₀ hε'pos] with z hz
    exact hvanish z hz
  have hall : ∀ z : ℂ, Pol.eval z = 0 := by
    intro z
    exact hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z₀) hev (Set.mem_univ z)
  have : Pol = 0 := Polynomial.funext (by simpa using hall)
  exact hPolMonic.ne_zero this

end GaloisForLFunctions.HTGeometry
