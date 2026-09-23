import GaloisForLFunctions.Bottcher.InverseBranchPeriodic

/-!
# Periodic points from contracting inverse branches of an expanding iterate

The density of (strongly) repelling cycles in the Julia frontier — the residual dynamical supplier of
the connected-transcendence gap — is produced, in the classical Fatou/Milnor argument, by the
following mechanism: at a repelling periodic point the iterate `f_c^[p]` is expanding, so a single-valued
inverse branch of `f_c^[p]` is a **contraction**, and Banach's fixed-point theorem turns that contraction
into a genuine period-`p` point inside the target ball.

The tree already has the Banach half (`exists_periodic_point_of_lipschitz_inverse_branch_on_closedBall`)
but consumes a *hypothesised* contracting branch.  This file supplies the missing quantitative fact —
**an analytic right inverse of an `L`-expanding map (`L > 1`) contracts by `1/L`** — and packages it with
the Banach lemma into a periodic-point producer whose only inputs are (i) an analytic inverse branch `g`
of `f_c^[p]` on a ball, (ii) `f_c^[p]` expanding on the branch's image, and (iii) `g` mapping a closed
sub-ball into itself.  These are exactly the data the blowing-up step hands the density argument.

- `norm_inverse_image_sub_le_of_expanding_on_ball` — contraction estimate `‖g y − g x‖ ≤ (1/L)‖y − x‖`.
- `exists_periodic_point_of_expanding_inverse_branch` — the period-`p` point in the closed sub-ball.
-/

open Complex Metric Set Topology Filter

namespace Bottcher

/-- **An inverse branch of an expanding map contracts.**  If `g` is an analytic right inverse of `F` on
`ball a r` (`F ∘ g = id`) whose image lies where `F` expands (`L ≤ ‖F'(g w)‖`, `L > 1`), then `g` is
`(1/L)`-Lipschitz on the ball: `‖g y − g x‖ ≤ (1/L)‖y − x‖`.  Mechanism: differentiating `F ∘ g = id`
gives `g'(w) = 1/F'(g w)`, so `‖g'‖ ≤ 1/L < 1`; the convex mean-value inequality does the rest. -/
theorem norm_inverse_image_sub_le_of_expanding_on_ball {F g : ℂ → ℂ} {a : ℂ} {r L : ℝ}
    (hL : 1 < L)
    (hg : ∀ w ∈ ball a r, F (g w) = w)
    (hgd : ∀ w ∈ ball a r, DifferentiableAt ℂ g w)
    (hFd : ∀ w ∈ ball a r, HasDerivAt F (deriv F (g w)) (g w))
    (hFexp : ∀ w ∈ ball a r, L ≤ ‖deriv F (g w)‖)
    {x y : ℂ} (hx : x ∈ ball a r) (hy : y ∈ ball a r) :
    ‖g y - g x‖ ≤ (1 / L) * ‖y - x‖ := by
  refine (convex_ball a r).norm_image_sub_le_of_norm_deriv_le hgd ?_ hx hy
  intro w hw
  have hLpos : (0:ℝ) < L := by linarith
  have hFexpw := hFexp w hw
  have hFne : deriv F (g w) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hFexpw; linarith
  have hEq : (F ∘ g) =ᶠ[𝓝 w] id := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
    simp [Function.comp, hg w' hw']
  have hcomp1 : HasDerivAt (F ∘ g) 1 w := (hEq.hasDerivAt_iff).mpr (hasDerivAt_id w)
  have hcomp2 : HasDerivAt (F ∘ g) (deriv F (g w) * deriv g w) w :=
    (hFd w hw).comp w (hgd w hw).hasDerivAt
  have hprod : deriv F (g w) * deriv g w = 1 := hcomp2.unique hcomp1
  have hdg : deriv g w = 1 / deriv F (g w) := by
    rw [eq_div_iff hFne, mul_comm]; exact hprod
  rw [hdg, norm_div, norm_one]
  exact one_div_le_one_div_of_le hLpos hFexpw

/-- **Periodic point from an expanding inverse branch.**  If `g` is an analytic right inverse of
`f_c^[p]` on `ball a R` whose image lies in the expanding region (`L ≤ ‖(f_c^[p])'(g w)‖`, `L > 1`), and
`g` maps the smaller closed ball `closedBall a r` (`r < R`) into itself, then `f_c^[p]` has a fixed
point in `closedBall a r` — a period-`p` point.  The inverse branch contracts by `1/L < 1`
(`norm_inverse_image_sub_le_of_expanding_on_ball`), so Banach's fixed-point theorem
(`exists_periodic_point_of_lipschitz_inverse_branch_on_closedBall`) yields the periodic point.  This is
the concrete supplier the frontier-ball density argument needs after the blowing-up step produces the
inverse branch into the ball. -/
theorem exists_periodic_point_of_expanding_inverse_branch {c a : ℂ} {r R L : ℝ} {p : ℕ} {g : ℂ → ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (hL : 1 < L)
    (hg : ∀ w ∈ ball a R, (quadratic c)^[p] (g w) = w)
    (hgd : ∀ w ∈ ball a R, DifferentiableAt ℂ g w)
    (hFexp : ∀ w ∈ ball a R, L ≤ ‖deriv ((quadratic c)^[p]) (g w)‖)
    (hmaps : Set.MapsTo g (closedBall a r) (closedBall a r)) :
    ∃ z ∈ closedBall a r, (quadratic c)^[p] z = z := by
  have hsub : closedBall a r ⊆ ball a R := closedBall_subset_ball hrR
  have hLpos : (0:ℝ) < L := by linarith
  have hFd : ∀ w ∈ ball a R,
      HasDerivAt ((quadratic c)^[p]) (deriv ((quadratic c)^[p]) (g w)) (g w) :=
    fun w _ => ((differentiable_quadratic_iterate_repellingFixedPoint c p) (g w)).hasDerivAt
  set K : NNReal := ⟨1 / L, by positivity⟩ with hKdef
  have hKcoe : (K : ℝ) = 1 / L := rfl
  have hK1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe, NNReal.coe_one, div_lt_one hLpos]; exact hL
  have hlip : LipschitzOnWith K g (closedBall a r) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Complex.dist_eq, Complex.dist_eq, hKcoe]
    have hest := norm_inverse_image_sub_le_of_expanding_on_ball hL hg hgd hFd hFexp
      (hsub hx) (hsub hy)
    rw [norm_sub_rev x y]
    calc ‖g x - g y‖ = ‖g y - g x‖ := norm_sub_rev _ _
      _ ≤ (1 / L) * ‖y - x‖ := hest
  exact exists_periodic_point_of_lipschitz_inverse_branch_on_closedBall hr hK1 hmaps hlip
    (fun z hz => hg z (hsub hz))

end Bottcher
