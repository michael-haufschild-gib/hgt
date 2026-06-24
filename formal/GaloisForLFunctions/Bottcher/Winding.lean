/-
# Böttcher tower — the base period `∮ d log φ_c = 2πi` (total mass / cap normalization)

The logarithmic derivative `d log φ_c = φ_c'/φ_c = z⁻¹ + ∑ₖ deriv(termₖ)` is the Cauchy
transform of the equilibrium measure `μ_c` (Brolin). Its period around a large circle `C(0,R)`
is the **total mass**:

  `∮_{C(0,R)} d log φ_c = 2πi · μ_c(ℂ) = 2πi`,    i.e. `cap(K_c) = 1` and winding `= 1`.

Proof: split `d log φ_c = z⁻¹ + deriv(∑ₖ termₖ)`. The pole term integrates to `2πi`
(`integral_sub_inv_of_mem_ball`); the series part is the derivative of a single-valued analytic
function on the escape annulus, so its loop integral vanishes (FTC,
`integral_eq_zero_of_hasDerivWithinAt`). This is the `n = 0` case of the dyadic period tower:
the deeper cylinder periods `2πi/2ⁿ` (the monodromy multipliers) are the same integral around
inner loops enclosing equilibrium mass `2⁻ⁿ`, fed to `multiplier_orderOf_of_mass`.
-/
import GaloisForLFunctions.Bottcher.BottcherCoord
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.LogDeriv

open Complex Metric

namespace Bottcher

/-- **Base period / total mass.** The logarithmic derivative of `φ_c` integrates to `2πi`
around any escape-regime circle `C(0,R)` (`R > max 2 ‖c‖`): the winding number of `φ_c` is `1`
and the equilibrium measure has total mass `1` (`cap K_c = 1`). The `n = 0` rung of the dyadic
period tower. -/
theorem circleIntegral_dlog_bottcher {c : ℂ} {R : ℝ} (hR : max 2 ‖c‖ < R) :
    (∮ z in C(0, R), z⁻¹ + deriv (fun w => ∑' k, bottcherLogTerm c w k) z)
      = 2 * (Real.pi : ℂ) * Complex.I := by
  have hRpos : 0 < R := lt_of_le_of_lt (le_max_left _ _ |>.trans' (by norm_num)) hR
  have hR0 : 0 ≤ R := le_of_lt hRpos
  have hsub : sphere (0 : ℂ) R ⊆ escapeOpen c := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    rw [escapeOpen, Set.mem_setOf_eq, hz]; exact hR
  have hSan : AnalyticOnNhd ℂ (fun w => ∑' k, bottcherLogTerm c w k) (escapeOpen c) :=
    (differentiableOn_bottcherLogSum c).analyticOnNhd (isOpen_escapeOpen c)
  have hci1 : CircleIntegrable (fun z : ℂ => z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR0
    apply continuousOn_inv₀.mono
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h; rw [h, norm_zero] at hz; linarith
  have hci2 : CircleIntegrable (deriv (fun w => ∑' k, bottcherLogTerm c w k)) 0 R :=
    ((hSan.deriv).continuousOn.mono hsub).circleIntegrable hR0
  rw [circleIntegral.integral_add hci1 hci2]
  have h1 : (∮ z in C(0, R), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    have key := circleIntegral.integral_sub_inv_of_mem_ball (c := (0:ℂ)) (w := (0:ℂ)) (R := R)
      (by simp [hRpos])
    simp only [sub_zero] at key
    exact key
  have h2 : (∮ z in C(0, R), deriv (fun w => ∑' k, bottcherLogTerm c w k) z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR0
    intro z hz
    exact (((hSan z (hsub hz)).differentiableAt).hasDerivAt).hasDerivWithinAt
  rw [h1, h2, add_zero]

/-- **Self-similarity of the logarithmic derivative.** `logDeriv φ_c (z) = z · logDeriv φ_c (f_c z)`
on the escape set. This is the functional equation `φ_c ∘ f_c = φ_c²` differentiated: `d log φ_c`
pulls back through `f_c` with a factor `½` (here in pointwise/multiplicative form). It is the engine
of the dyadic period tower — iterating, `d log φ_c` at `z` equals `(∏_{k<n} f_c^[k] z) · d log φ_c`
at `f_c^[n] z`, so the period around the `n`-fold loop pullback is `2⁻ⁿ` of the base period `2πi`,
i.e. `2πi/2ⁿ` — the order-`2ⁿ` monodromy multiplier. No equilibrium measure needed for the value. -/
theorem logDeriv_bottcherCoord_self_similar {c z : ℂ} (hz : z ∈ escapeOpen c) :
    logDeriv (bottcherCoord c) z = z * logDeriv (bottcherCoord c) (quadratic c z) := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  have hfz : quadratic c z ∈ escapeOpen c := by
    have hgt : ‖z‖ < ‖quadratic c z‖ := quadratic_norm_lt hc hz2
    show max 2 ‖c‖ < ‖quadratic c z‖
    exact lt_trans hz hgt
  have hdiff_b : DifferentiableAt ℂ (bottcherCoord c) z :=
    (differentiableOn_bottcherCoord c).differentiableAt ((isOpen_escapeOpen c).mem_nhds hz)
  have hdiff_bfz : DifferentiableAt ℂ (bottcherCoord c) (quadratic c z) :=
    (differentiableOn_bottcherCoord c).differentiableAt ((isOpen_escapeOpen c).mem_nhds hfz)
  have hdiff_q : DifferentiableAt ℂ (quadratic c) z := by unfold quadratic; fun_prop
  have hbne : bottcherCoord c z ≠ 0 := bottcherCoord_ne_zero c z
  have hee : (fun w => bottcherCoord c (quadratic c w)) =ᶠ[nhds z]
      (fun w => bottcherCoord c w * bottcherCoord c w) := by
    filter_upwards [(isOpen_escapeOpen c).mem_nhds hz] with w hw
    obtain ⟨hcw, hw2⟩ := mem_escapeOpen_regime hw
    rw [bottcherCoord_quadratic hcw hw2, sq]
  have hL : logDeriv (fun w => bottcherCoord c (quadratic c w)) z
      = logDeriv (bottcherCoord c) (quadratic c z) * deriv (quadratic c) z :=
    logDeriv_comp hdiff_bfz hdiff_q
  have hR : logDeriv (fun w => bottcherCoord c w * bottcherCoord c w) z
      = 2 * logDeriv (bottcherCoord c) z := by
    rw [logDeriv_mul z hbne hbne hdiff_b hdiff_b]; ring
  have hld : logDeriv (fun w => bottcherCoord c (quadratic c w)) z
      = logDeriv (fun w => bottcherCoord c w * bottcherCoord c w) z := by
    rw [logDeriv_apply, logDeriv_apply, hee.deriv_eq, hee.eq_of_nhds]
  have hdq : deriv (quadratic c) z = 2 * z := by
    have hd : HasDerivAt (quadratic c) (2 * z) z := by
      unfold quadratic
      simpa using (hasDerivAt_pow 2 z).add_const c
    exact hd.deriv
  rw [hL, hdq] at hld
  rw [hR] at hld
  linear_combination (-1/2 : ℂ) * hld

/-- The escape set is forward-invariant: every iterate of an escaping point escapes. -/
theorem escapeOpen_iterate {c z : ℂ} (hz : z ∈ escapeOpen c) (n : ℕ) :
    (quadratic c)^[n] z ∈ escapeOpen c := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  show max 2 ‖c‖ < ‖(quadratic c)^[n] z‖
  exact lt_of_lt_of_le hz (norm_iterate_ge hc hz2 n)

/-- **Iterated self-similarity.** `logDeriv φ_c (z) = (∏_{k<n} f_c^[k] z) · logDeriv φ_c (f_c^[n] z)`.
The multiplicative product form of the period self-similarity: each pullback through `f_c`
contributes a factor and halves the period. As `n → ∞`, `f_c^[n] z → ∞` and `logDeriv φ_c ~ 1/w`
there, so this is the product expansion of `d log φ_c` = the Cauchy transform of the equilibrium
measure (Brolin's potential, in product rather than measure form). -/
theorem logDeriv_bottcherCoord_iterate {c z : ℂ} (hz : z ∈ escapeOpen c) (n : ℕ) :
    logDeriv (bottcherCoord c) z
      = (∏ k ∈ Finset.range n, (quadratic c)^[k] z)
        * logDeriv (bottcherCoord c) ((quadratic c)^[n] z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, logDeriv_bottcherCoord_self_similar (escapeOpen_iterate hz n),
        Finset.prod_range_succ, ← Function.iterate_succ_apply' (quadratic c) n z]
    ring

/-- **Period-doubling (contour-lift of self-similarity).** For a path `γ` lying in the escape set,
the parametrized contour integral of `ω = d log φ_c` over the image path `f_c ∘ γ` is twice that
over `γ`. This is `∮_{f_c∘γ} ω = 2 ∮_γ ω`, the integral form of `f_c*ω = 2ω`, with `γ'` the path
velocity (so the integrand over `f_c∘γ` carries the chain-rule factor `deriv f_c ∘ γ = 2·γ`). The
form `ω` is single-valued on the whole basin (branches of `φ_c` differ by constants, killed by
`d log`), so these are honest closed-loop periods: the `n`-fold pullback of the base loop (period
`2πi`) has period `2πi/2ⁿ` — the order-`2ⁿ` monodromy multiplier exponent — with no equilibrium
measure. -/
theorem pathInt_comp_quadratic {c : ℂ} {γ γ' : ℝ → ℂ}
    (hmem : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), γ θ ∈ escapeOpen c) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        logDeriv (bottcherCoord c) (quadratic c (γ θ)) * (2 * γ θ * γ' θ))
      = 2 * ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hss := logDeriv_bottcherCoord_self_similar (hmem θ hθ)
  simp only
  rw [hss]; ring

/-- **`n`-fold period scaling.** The parametrized contour integral of `ω = d log φ_c` over the
`n`-fold image path `f_c^[n] ∘ γ` is `2ⁿ` times that over `γ`. Equivalently: an `n`-fold loop
*pullback* (a `γ` with `f_c^[n] ∘ γ` = the base loop) has period `2⁻ⁿ` of the base period `2πi`,
i.e. `2πi/2ⁿ` — exactly the order-`2ⁿ` dyadic monodromy multiplier exponent
(`orderOf_dyadicRoot`), realized here for the *actual* `φ_c` with no equilibrium measure. -/
theorem pathInt_iterate_comp {c : ℂ} {γ γ' : ℝ → ℂ} (n : ℕ)
    (hmem : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), γ θ ∈ escapeOpen c) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) ((quadratic c)^[n] (γ θ))
        * (2 ^ n * (∏ k ∈ Finset.range n, (quadratic c)^[k] (γ θ)) * γ' θ))
      = 2 ^ n * ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hiter := logDeriv_bottcherCoord_iterate (hmem θ hθ) n
  simp only
  rw [hiter]; ring

end Bottcher
