/-
# Böttcher tower — fractional period from a lift of the base circle

The dyadic monodromy multiplier exponent `2πi/2ⁿ` produced WITHOUT the equilibrium measure: if a
path `γ` in the escape set is a *lift* of the outer base circle `C(0,R)` through the `n`-fold
dynamics `f_c^[n]` — i.e. `f_c^[n] ∘ γ = C(0,R)` with the chain-rule velocity match — then its
`d log φ_c` period is exactly `2πi / 2ⁿ`. This is the functional-equation route
(`pathInt_iterate_comp`, anchored at `circleIntegral_dlog_bottcher`) carried to the genuine `φ_c`:
the `2ⁿ`-fold period scaling on the lift, pinned at the base period `2πi`.

The remaining geometric input of the whole disconnected case is hereby isolated as a single clean
statement — *the closed lift exists* (one loop around a depth-`n` Cantor lobe maps onto the outer
circle), which the figure-eight / two-lobe split (`FigureEightCapstone.lean`,
`disconnected_two_lobes`) is what supplies the topology for.
-/
import GaloisForLFunctions.Bottcher.Winding
import GaloisForLFunctions.Bottcher.FigureEight

open Complex Metric

namespace Bottcher

/-- **Base loop period for `logDeriv φ_c`.** The honest logarithmic derivative `d log φ_c = φ_c'/φ_c`
integrates to `2πi` around any escape-regime circle `C(0,R)` (`R > max 2 ‖c‖`). Restates
`circleIntegral_dlog_bottcher` with the genuine `logDeriv (bottcherCoord c)` replacing its escape-set
expansion `z⁻¹ + deriv ∑`, via `logDeriv_bottcherCoord_escape` on the circle (which lies in the
escape set). The winding number of `φ_c` around `K_c` is `1`. -/
theorem circleIntegral_logDeriv_bottcher {c : ℂ} {R : ℝ} (hR : max 2 ‖c‖ < R) :
    (∮ z in C(0, R), logDeriv (bottcherCoord c) z) = 2 * (Real.pi : ℂ) * Complex.I := by
  have hRpos : 0 < R := lt_of_le_of_lt (le_trans (by norm_num) (le_max_left 2 ‖c‖)) hR
  have hcong : (∮ z in C(0, R), logDeriv (bottcherCoord c) z)
      = ∮ z in C(0, R), z⁻¹ + deriv (fun w => ∑' k, bottcherLogTerm c w k) z := by
    refine circleIntegral.integral_congr hRpos.le ?_
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hesc : z ∈ escapeOpen c := by
      rw [escapeOpen, Set.mem_setOf_eq, hz]; exact hR
    exact logDeriv_bottcherCoord_escape hesc
  rw [hcong]; exact circleIntegral_dlog_bottcher hR

/-- **Fractional period from a lift — the dyadic monodromy multiplier exponent `2πi/2ⁿ`.**
Let `γ` be a path in the escape set that lifts the outer base circle through the `n`-fold dynamics:
`f_c^[n] (γ θ) = circleMap 0 R θ` for all `θ ∈ [0,2π]`, with the matching velocity
`2ⁿ · (∏_{k<n} f_c^[k] (γ θ)) · γ' θ = deriv (circleMap 0 R) θ` (the chain rule for `f_c^[n] ∘ γ`).
Then the contour integral of `d log φ_c` over `γ` is `2πi / 2ⁿ`. No equilibrium measure: the value
is forced by the `2ⁿ`-fold period scaling (`pathInt_iterate_comp`) anchored at the base period
(`circleIntegral_logDeriv_bottcher`). This is the order-`2ⁿ` monodromy-multiplier exponent — the
analytic core of the dyadic tower — realized for the genuine `φ_c`. The only remaining hypothesis is
the geometric existence of such a lift (a closed loop around one depth-`n` lobe). -/
theorem fractional_period_of_lift {c : ℂ} {R : ℝ} (hR : max 2 ‖c‖ < R) (n : ℕ)
    {γ γ' : ℝ → ℂ}
    (hmem : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), γ θ ∈ escapeOpen c)
    (hlift : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        (quadratic c)^[n] (γ θ) = circleMap 0 R θ)
    (hvel : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        2 ^ n * (∏ k ∈ Finset.range n, (quadratic c)^[k] (γ θ)) * γ' θ
          = deriv (circleMap 0 R) θ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
      = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n := by
  have key := pathInt_iterate_comp (c := c) (γ := γ) (γ' := γ') n hmem
  have hcong : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        logDeriv (bottcherCoord c) ((quadratic c)^[n] (γ θ))
          * (2 ^ n * (∏ k ∈ Finset.range n, (quadratic c)^[k] (γ θ)) * γ' θ))
      = ∮ z in C(0, R), logDeriv (bottcherCoord c) z := by
    have hdef : (∮ z in C(0, R), logDeriv (bottcherCoord c) z)
        = ∫ θ in (0 : ℝ)..(2 * Real.pi),
            deriv (circleMap 0 R) θ • logDeriv (bottcherCoord c) (circleMap 0 R θ) := rfl
    rw [hdef]
    refine intervalIntegral.integral_congr ?_
    intro θ hθ
    dsimp only
    rw [hlift θ hθ, hvel θ hθ, smul_eq_mul]
    ring
  rw [hcong, circleIntegral_logDeriv_bottcher hR] at key
  rw [eq_div_iff (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))]
  linear_combination -key

/-- **Chain rule for the iterate `f_c^[n]`.** `HasDerivAt (f_c^[n]) (∏_{k<n} 2·f_c^[k] x) x` — the
derivative of the `n`-fold quadratic iterate is the product of the linear factors `f_c'(f_c^[k] x) =
2·f_c^[k] x` along the orbit. This is the analytic content of "`deg f_c^[n] = 2ⁿ`" at the derivative
level; it is what turns a differentiable lift of the base circle into the velocity match `hvel`. -/
theorem hasDerivAt_quadratic_iterate (c x : ℂ) (n : ℕ) :
    HasDerivAt (fun y => (quadratic c)^[n] y)
      (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] x) x := by
  induction n with
  | zero =>
      simpa only [Function.iterate_zero_apply, Finset.range_zero, Finset.prod_empty]
        using hasDerivAt_id' x
  | succ n ih =>
    have hcomp : HasDerivAt ((fun y => quadratic c y) ∘ (fun y => (quadratic c)^[n] y))
        (2 * (quadratic c)^[n] x * ∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] x) x :=
      (hasStrictDerivAt_quadratic c ((quadratic c)^[n] x)).hasDerivAt.comp x ih
    have hfun : (fun y => (quadratic c)^[n + 1] y)
        = (fun y => quadratic c y) ∘ (fun y => (quadratic c)^[n] y) := by
      funext y; simp [Function.iterate_succ_apply']
    rw [hfun, Finset.prod_range_succ]
    convert hcomp using 1
    ring

/-- **The velocity match `hvel` is the chain rule.** If `γ` is differentiable at `θ` and the lifted
path `f_c^[n] ∘ γ` has derivative `D` at `θ`, then `2ⁿ · (∏_{k<n} f_c^[k](γ θ)) · γ' θ = D`. So in
`fractional_period_of_lift` the hypothesis `hvel` is *not* an extra geometric assumption — it follows
automatically from a differentiable lift, by `hasDerivAt_quadratic_iterate` and uniqueness of
derivatives. The remaining input of the disconnected case is thus exactly: *a differentiable lift of
the base circle through `f_c^[n]` exists*. -/
theorem hvel_of_diff_lift {c : ℂ} {γ γ' : ℝ → ℂ} {θ : ℝ} {D : ℂ} {n : ℕ}
    (hγ : HasDerivAt γ (γ' θ) θ)
    (hlift : HasDerivAt (fun t => (quadratic c)^[n] (γ t)) D θ) :
    2 ^ n * (∏ k ∈ Finset.range n, (quadratic c)^[k] (γ θ)) * γ' θ = D := by
  have hcomp : HasDerivAt (fun t => (quadratic c)^[n] (γ t))
      ((∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] (γ θ)) * γ' θ) θ :=
    (hasDerivAt_quadratic_iterate c (γ θ) n).comp θ hγ
  have huniq := hcomp.unique hlift
  rw [← huniq, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

end Bottcher
