import Mathlib

/-!
# Rigidity of the pure-power autonomous equation

The substitution `H = (F − a)^{d-1}` turns `F' = γ (F − a)^d` into the Riccati equation
`H' = (d−1)γ H²`, and an entire solution of that vanishes identically.

The Riccati step is elementary and needs no value distribution.  A zero of `H` forces `H` to vanish
on a whole disc: on a disc of radius `ρ` with `ρ‖c‖ ≤ 1/2` and `‖H‖ ≤ 1`, the mean value inequality
gives `M ≤ ‖c‖M²ρ ≤ M/2` for the maximum `M`, so `M = 0`; the identity theorem then propagates the
vanishing to the plane.  If instead `H` never vanishes, `1/H` is entire with derivative the constant
`−c`, hence affine — and an affine function with nonzero slope has a zero, which `1/H` cannot.

Consequently `F' = γ(F − a)^d` with `d ≥ 2` has no entire solution but the constant `a`.  This is the
single-root case of the Briot–Bouquet no-go; the general polynomial case reduces to it once one knows
that a solution omits every root of the coefficient polynomial, which for two or more distinct roots
needs Picard.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The Riccati rigidity.**  An entire solution of `H' = c H²` with `c ≠ 0` vanishes identically:
a zero forces `H` to vanish on a whole disc, hence everywhere, and a nowhere-vanishing `H` would make
`1/H` an affine function with a zero. -/
theorem eq_zero_of_deriv_eq_const_mul_sq {c : ℂ} (hc : c ≠ 0) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (heq : ∀ z, deriv H z = c * (H z) ^ (2 : ℕ)) : H = 0 := by
  classical
  by_contra hne
  obtain ⟨z₁, hz₁⟩ : ∃ z, H z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (funext hcon)
  -- a zero of `H` forces `H` to vanish on a disc
  have hlocal : ∀ z₀ : ℂ, H z₀ = 0 → H = 0 := by
    intro z₀ hz₀
    have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    -- choose a radius on which `H` is small and the contraction bites
    have hcont : ContinuousAt H z₀ := (hH z₀).continuousAt
    have hsmall : ∀ᶠ z in nhds z₀, ‖H z‖ ≤ 1 := by
      have h1 : ∀ᶠ z in nhds z₀, ‖H z - H z₀‖ < 1 := by
        have := Metric.tendsto_nhds.mp hcont.tendsto 1 (by norm_num)
        simpa [dist_eq_norm] using this
      filter_upwards [h1] with z hz
      rw [hz₀] at hz
      simpa using hz.le
    obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff.mp hsmall
    set ρ : ℝ := min (ε / 2) (1 / (2 * ‖c‖)) with hρ
    have hρ0 : 0 < ρ := by
      rw [hρ]
      exact lt_min (by linarith) (by positivity)
    have hρε : ρ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hρc : ρ * ‖c‖ ≤ 1 / 2 := by
      have h := min_le_right (ε / 2) (1 / (2 * ‖c‖))
      rw [← hρ] at h
      calc ρ * ‖c‖ ≤ (1 / (2 * ‖c‖)) * ‖c‖ := by nlinarith [hcpos]
        _ = 1 / 2 := by field_simp
    set K : Set ℂ := Metric.closedBall z₀ ρ with hK
    have hKcompact : IsCompact K := isCompact_closedBall _ _
    have hKne : K.Nonempty := ⟨z₀, Metric.mem_closedBall_self hρ0.le⟩
    have hKsmall : ∀ z ∈ K, ‖H z‖ ≤ 1 := by
      intro z hz
      refine hε ?_
      have : dist z z₀ ≤ ρ := Metric.mem_closedBall.mp hz
      calc dist z z₀ ≤ ρ := this
        _ < ε := hρε
    obtain ⟨w, hwK, hwmax⟩ :=
      hKcompact.exists_isMaxOn hKne (hH.continuous.norm.continuousOn)
    set M : ℝ := ‖H w‖ with hM
    have hMmax : ∀ z ∈ K, ‖H z‖ ≤ M := fun z hz => hwmax hz
    have hM0 : 0 ≤ M := norm_nonneg _
    have hM1 : M ≤ 1 := hKsmall w hwK
    have hderivle : ∀ z ∈ K, ‖deriv H z‖ ≤ ‖c‖ * M ^ (2 : ℕ) := by
      intro z hz
      rw [heq z, norm_mul, norm_pow]
      have hzM : ‖H z‖ ≤ M := hMmax z hz
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
      exact pow_le_pow_left₀ (norm_nonneg _) hzM 2
    have hmvt : ‖H w - H z₀‖ ≤ (‖c‖ * M ^ (2 : ℕ)) * ‖w - z₀‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hH x) hderivle
        (convex_closedBall z₀ ρ) (Metric.mem_closedBall_self hρ0.le) hwK
    have hdist : ‖w - z₀‖ ≤ ρ := by
      have := Metric.mem_closedBall.mp hwK
      rwa [dist_eq_norm] at this
    have hMle : M ≤ ‖c‖ * M ^ (2 : ℕ) * ρ := by
      rw [hz₀, sub_zero] at hmvt
      calc M = ‖H w‖ := rfl
        _ ≤ (‖c‖ * M ^ (2 : ℕ)) * ‖w - z₀‖ := hmvt
        _ ≤ (‖c‖ * M ^ (2 : ℕ)) * ρ := by
            refine mul_le_mul_of_nonneg_left hdist (by positivity)
    have hMzero : M = 0 := by
      nlinarith [hMle, hM0, hM1, hρc, hcpos, hρ0]
    -- `H` vanishes on the disc, hence everywhere
    have hdisc : ∀ z ∈ K, H z = 0 := by
      intro z hz
      have := hMmax z hz
      rw [hMzero] at this
      exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
    have hev : H =ᶠ[nhds z₀] 0 := by
      refine Metric.eventually_nhds_iff.mpr ⟨ρ, hρ0, fun z hz => ?_⟩
      exact hdisc z (Metric.mem_closedBall.mpr hz.le)
    have hAn : AnalyticOnNhd ℂ H Set.univ := fun z _ => hH.analyticAt z
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z₀) hev
    funext z
    exact this (Set.mem_univ z)
  -- so `H` never vanishes
  have hnz : ∀ z, H z ≠ 0 := by
    intro z hz
    exact hz₁ (by rw [hlocal z hz]; rfl)
  -- then `1/H` is affine with a zero
  have hinv : Differentiable ℂ (fun z => (H z)⁻¹) := fun z =>
    ((hH z).inv (hnz z))
  have hinvderiv : ∀ z, deriv (fun z => (H z)⁻¹) z = -c := by
    intro z
    have h1 : HasDerivAt H (c * (H z) ^ (2 : ℕ)) z := by
      have := (hH z).hasDerivAt
      rwa [heq z] at this
    have h2 := h1.inv (hnz z)
    have h3 : -(c * (H z) ^ (2 : ℕ)) / (H z) ^ (2 : ℕ) = -c := by
      field_simp
      rw [div_self (hnz z)]
    rw [h3] at h2
    exact h2.deriv
  have haff : ∀ z, (H z)⁻¹ = (H 0)⁻¹ + -c * z := by
    intro z
    have hd : ∀ w : ℂ, HasDerivAt (fun u => (H u)⁻¹ - (-c * u)) 0 w := by
      intro w
      have h1 : HasDerivAt (fun u => (H u)⁻¹) (-c) w := by
        have := (hinv w).hasDerivAt
        rwa [hinvderiv w] at this
      have h2 : HasDerivAt (fun u : ℂ => -c * u) (-c) w := by
        simpa using (hasDerivAt_id w).const_mul (-c)
      have h3 : HasDerivAt (fun u => (H u)⁻¹ - (-c * u)) (-c - -c) w := h1.sub h2
      rwa [sub_self] at h3
    have hconst := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
      (fun w => (hd w).deriv) z 0
    simp only [mul_zero, sub_zero, neg_mul, sub_neg_eq_add] at hconst
    linear_combination hconst
  have hzero := haff (-(H 0)⁻¹ / (-c))
  have hcne : (-c) ≠ 0 := neg_ne_zero.mpr hc
  have hrw : (H 0)⁻¹ + -c * (-(H 0)⁻¹ / (-c)) = 0 := by
    field_simp
    norm_num
  rw [hrw] at hzero
  exact (inv_ne_zero (hnz _)) hzero

/-- **No entire solution of a pure-power autonomous equation of degree at least two.**  If
`F' = γ (F − a)^d` with `γ ≠ 0` and `d ≥ 2`, then `F` is the constant `a`.  Substituting
`H = (F − a)^{d-1}` turns the equation into the Riccati equation `H' = (d−1)γ H²`. -/
theorem eq_const_of_deriv_eq_const_mul_pow {gam a : ℂ} (hgam : gam ≠ 0) {d : ℕ} (hd : 2 ≤ d)
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (heq : ∀ z, deriv F z = gam * (F z - a) ^ d) :
    F = fun _ => a := by
  set G : ℂ → ℂ := fun z => F z - a with hG
  have hGdiff : Differentiable ℂ G := hF.sub_const a
  have hGderiv : ∀ z, HasDerivAt G (gam * (G z) ^ d) z := by
    intro z
    have h1 : HasDerivAt F (gam * (F z - a) ^ d) z := by
      have := (hF z).hasDerivAt
      rwa [heq z] at this
    simpa [hG] using h1.sub_const a
  set H : ℂ → ℂ := fun z => (G z) ^ (d - 1) with hH
  have hHdiff : Differentiable ℂ H := (hGdiff.pow (d - 1))
  have hHderiv : ∀ z, deriv H z = ((d : ℂ) - 1) * gam * (H z) ^ (2 : ℕ) := by
    intro z
    have hpow := (hGderiv z).pow (d - 1)
    have hval : ((d - 1 : ℕ) : ℂ) * G z ^ (d - 1 - 1) * (gam * G z ^ d)
        = ((d : ℂ) - 1) * gam * ((G z) ^ (d - 1)) ^ (2 : ℕ) := by
      have hcast : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by
        have : (1 : ℕ) ≤ d := by omega
        push_cast [Nat.cast_sub this]
        ring
      have hexp : d - 1 - 1 + d = (d - 1) * 2 := by omega
      rw [hcast, ← pow_mul, ← hexp, pow_add]
      ring
    have hpow2 : HasDerivAt (fun w => G w ^ (d - 1))
        (((d - 1 : ℕ) : ℂ) * G z ^ (d - 1 - 1) * (gam * G z ^ d)) z := hpow
    rw [hH]
    show deriv (fun w => G w ^ (d - 1)) z = ((d : ℂ) - 1) * gam * (G z ^ (d - 1)) ^ (2 : ℕ)
    rw [hpow2.deriv]
    exact hval
  have hc : ((d : ℂ) - 1) * gam ≠ 0 := by
    refine mul_ne_zero ?_ hgam
    intro hcon
    have hdc : (d : ℂ) = 1 := by linear_combination hcon
    have : (d : ℕ) = 1 := by exact_mod_cast hdc
    omega
  have hzero := eq_zero_of_deriv_eq_const_mul_sq hc hHdiff hHderiv
  funext z
  have hz : (G z) ^ (d - 1) = 0 := congrFun hzero z
  have hGz : G z = 0 := by
    have hne : d - 1 ≠ 0 := by omega
    exact pow_eq_zero_iff hne |>.mp hz
  rw [hG] at hGz
  simp only at hGz
  linear_combination hGz

end GaloisForLFunctions.HTGeometry
