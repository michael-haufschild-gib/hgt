import Mathlib

/-!
# Germs that transform by a scalar under a contracting scaling are monomials

If an analytic germ at the origin satisfies `H (μ z) = c · H z` for a scaling `μ` of modulus less
than one, then either `H` vanishes identically near the origin or `H z = a z^m` with `c = μ^m`.
Factoring out the zero of `H` reduces the equation to `G (μ z) = G z` for a germ nonvanishing at
the origin, and iterating the scaling drives the argument to the origin, so `G` is constant.

This is the rigidity behind the cocycle form of Ritt's dichotomy: a quotient of Poincaré jets that
transforms by a power of the multiplier can only be a monomial.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- A germ invariant under a contracting scaling is constant near the origin. -/
theorem eventuallyEq_const_of_scaling_invariant {G : ℂ → ℂ} {mu : ℂ} (hmu : ‖mu‖ < 1)
    (hG : ContinuousAt G 0) (heq : ∀ᶠ z in 𝓝 (0 : ℂ), G (mu * z) = G z) :
    ∀ᶠ z in 𝓝 (0 : ℂ), G z = G 0 := by
  obtain ⟨ρ, hρ0, hρ⟩ := Metric.eventually_nhds_iff.mp heq
  refine Metric.eventually_nhds_iff.mpr ⟨ρ, hρ0, fun z hz => ?_⟩
  -- the scaled orbit stays in the ball and converges to the origin
  have hstep : ∀ n : ℕ, dist (mu ^ n * z) 0 < ρ ∧ G (mu ^ n * z) = G z := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
        have hdist : dist (mu ^ (n + 1) * z) 0 < ρ := by
          rw [dist_zero_right] at ih ⊢
          have h1 : ‖mu ^ (n + 1) * z‖ = ‖mu‖ * ‖mu ^ n * z‖ := by
            rw [norm_mul, norm_mul, pow_succ]
            rw [norm_mul]
            ring
          rw [h1]
          rcases eq_or_lt_of_le (norm_nonneg (mu ^ n * z)) with h0 | h0
          · rw [← h0, mul_zero]
            exact hρ0
          · calc ‖mu‖ * ‖mu ^ n * z‖ < 1 * ‖mu ^ n * z‖ := by
                  exact mul_lt_mul_of_pos_right hmu h0
              _ = ‖mu ^ n * z‖ := one_mul _
              _ < ρ := ih.1
        refine ⟨hdist, ?_⟩
        have hval := hρ ih.1
        have hmul : mu * (mu ^ n * z) = mu ^ (n + 1) * z := by ring
        rw [hmul] at hval
        rw [hval]
        exact ih.2
  -- the orbit tends to the origin
  have hlim : Filter.Tendsto (fun n : ℕ => mu ^ n * z) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hmu
    simpa using h.mul_const z
  have hGlim : Filter.Tendsto (fun n : ℕ => G (mu ^ n * z)) atTop (𝓝 (G 0)) := hG.tendsto.comp hlim
  have hconst : (fun n : ℕ => G (mu ^ n * z)) = fun _ : ℕ => G z := by
    funext n
    exact (hstep n).2
  rw [hconst] at hGlim
  exact tendsto_nhds_unique tendsto_const_nhds hGlim

/-- **Scaling rigidity.**  An analytic germ at the origin transforming by a scalar under a
contracting scaling either vanishes near the origin or is a monomial, and then the scalar is the
corresponding power of the scaling. -/
theorem eq_monomial_of_scaling {H : ℂ → ℂ} {mu c : ℂ} (hmu0 : mu ≠ 0) (hmu : ‖mu‖ < 1)
    (hH : AnalyticAt ℂ H 0) (heq : ∀ᶠ z in 𝓝 (0 : ℂ), H (mu * z) = c * H z) :
    (∀ᶠ z in 𝓝 (0 : ℂ), H z = 0) ∨
      ∃ (m : ℕ) (a : ℂ), a ≠ 0 ∧ c = mu ^ m ∧ ∀ᶠ z in 𝓝 (0 : ℂ), H z = a * z ^ m := by
  by_cases htop : analyticOrderAt H 0 = ⊤
  · exact Or.inl (analyticOrderAt_eq_top.mp htop)
  refine Or.inr ?_
  obtain ⟨G, hG, hG0, hfac⟩ := hH.analyticOrderAt_ne_top.mp htop
  set m : ℕ := analyticOrderNatAt H 0 with hmdef
  -- transport the factorisation along the scaling
  have hscale : Filter.Tendsto (fun z : ℂ => mu * z) (𝓝 0) (𝓝 0) := by
    have h : Filter.Tendsto (fun z : ℂ => mu * z) (𝓝 0) (𝓝 (mu * 0)) :=
      ((continuous_const.mul continuous_id).tendsto 0)
    simpa using h
  have hfac' : ∀ᶠ z in 𝓝 (0 : ℂ), H (mu * z) = (mu * z) ^ m * G (mu * z) := by
    filter_upwards [hscale.eventually hfac] with z hz
    simpa using hz
  have hfac0 : ∀ᶠ z in 𝓝 (0 : ℂ), H z = z ^ m * G z := by
    filter_upwards [hfac] with z hz
    simpa using hz
  have hcore : ∀ᶠ z in 𝓝 (0 : ℂ), mu ^ m * (z ^ m * G (mu * z)) = c * (z ^ m * G z) := by
    filter_upwards [heq, hfac', hfac0] with z h1 h2 h3
    have : (mu * z) ^ m * G (mu * z) = c * (z ^ m * G z) := by rw [← h2, h1, h3]
    rw [← this, mul_pow]
    ring
  -- cancel the vanishing factor off the origin
  have hpunct : ∀ᶠ z in 𝓝[≠] (0 : ℂ), mu ^ m * G (mu * z) = c * G z := by
    filter_upwards [nhdsWithin_le_nhds hcore, self_mem_nhdsWithin] with z hz hz0
    have hzm : (z : ℂ) ^ m ≠ 0 := pow_ne_zero m hz0
    refine mul_left_cancel₀ hzm ?_
    rw [show z ^ m * (mu ^ m * G (mu * z)) = mu ^ m * (z ^ m * G (mu * z)) from by ring,
      show z ^ m * (c * G z) = c * (z ^ m * G z) from by ring]
    exact hz
  -- the scalar is the corresponding power of the scaling
  have hcont1 : Filter.Tendsto (fun z : ℂ => mu ^ m * G (mu * z)) (𝓝[≠] (0 : ℂ))
      (𝓝 (mu ^ m * G 0)) := by
    have h : Filter.Tendsto (fun z : ℂ => mu ^ m * G (mu * z)) (𝓝 (0 : ℂ))
        (𝓝 (mu ^ m * G 0)) := by
      have hcomp : Filter.Tendsto (fun z : ℂ => G (mu * z)) (𝓝 (0 : ℂ)) (𝓝 (G 0)) := by
        exact hG.continuousAt.tendsto.comp hscale
      exact (tendsto_const_nhds.mul hcomp)
    exact h.mono_left nhdsWithin_le_nhds
  have hcont2 : Filter.Tendsto (fun z : ℂ => c * G z) (𝓝[≠] (0 : ℂ)) (𝓝 (c * G 0)) :=
    (tendsto_const_nhds.mul hG.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hcm : c = mu ^ m := by
    have heqv : mu ^ m * G 0 = c * G 0 :=
      tendsto_nhds_unique (hcont1.congr' hpunct) hcont2
    exact (mul_right_cancel₀ hG0 heqv).symm
  -- the reduced germ is scaling invariant, hence constant
  have hGinv : ∀ᶠ z in 𝓝 (0 : ℂ), G (mu * z) = G z := by
    have hw : ∀ᶠ z in 𝓝[≠] (0 : ℂ), G (mu * z) = G z := by
      filter_upwards [hpunct] with z hz
      rw [hcm] at hz
      exact mul_left_cancel₀ (pow_ne_zero m hmu0) hz
    have hpt : G (mu * 0) = G 0 := by rw [mul_zero]
    rw [← nhdsNE_sup_pure (0 : ℂ)]
    exact Filter.eventually_sup.mpr ⟨hw, by simpa using hpt⟩
  have hGconst := eventuallyEq_const_of_scaling_invariant hmu hG.continuousAt hGinv
  refine ⟨m, G 0, hG0, hcm, ?_⟩
  filter_upwards [hfac0, hGconst] with z h1 h2
  rw [h1, h2]
  ring

end

end GaloisForLFunctions.HTGeometry
