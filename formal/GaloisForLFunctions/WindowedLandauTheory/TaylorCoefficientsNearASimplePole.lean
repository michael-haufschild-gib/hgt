import Mathlib

/-!
# Taylor coefficients near a simple pole

Let `Φ` be holomorphic on a disc `|s - z| < r` except for one simple pole `ρ` with principal
part `c/(s - ρ)`. Subtracting the pole leaves a function holomorphic on the whole disc, whose
Taylor coefficients at `z` are `O(R^{-k})` for each `R < r` by Cauchy's estimate; the pole
itself contributes `c/(z - ρ)^{k+1}`. Hence

```text
|(-1)^k Φ^(k)(z)/k!  -  c/(z - ρ)^{k+1}|  ≤  M / R^k        (`exists_taylorCoeff_sub_pole_le`).
```
-/

open Complex Filter Topology Set Metric

namespace WindowedLandauTheory

noncomputable section

/-- **Cauchy's estimate** for all Taylor coefficients at once. -/
theorem exists_taylorCoeff_le {Φ : ℂ → ℂ} {z : ℂ} {r r' : ℝ}
    (hd : DifferentiableOn ℂ Φ (ball z r)) (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k Φ z / (k.factorial : ℂ)‖ ≤ M / r' ^ k := by
  have hcl : closedBall z r' ⊆ ball z r := closedBall_subset_ball h1
  have hdc : DiffContOnCl ℂ Φ (ball z r') := hd.diffContOnCl_ball hcl
  have hcont : ContinuousOn Φ (sphere z r') :=
    hd.continuousOn.mono (sphere_subset_closedBall.trans hcl)
  obtain ⟨M, hM⟩ := (isCompact_sphere z r').exists_bound_of_continuousOn hcont
  refine ⟨M, fun k => ?_⟩
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k h0 hdc hM
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hk]
  calc ‖iteratedDeriv k Φ z‖ ≤ k.factorial * M / r' ^ k := h
    _ = M / r' ^ k * k.factorial := by ring

/-- Derivatives of a simple pole: `(c/(s-ρ))^(k) = c (-1)^k k! / (z-ρ)^{k+1}`. -/
theorem iteratedDeriv_const_div_sub (c : ℂ) {ρ z : ℂ} (hz : z ≠ ρ) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => c / (s - ρ)) z =
      c * ((-1) ^ k * (k.factorial : ℂ) * ((z - ρ) ^ (k + 1))⁻¹) := by
  have hne : z - ρ ≠ 0 := sub_ne_zero.mpr hz
  have hcd : ContDiffAt ℂ k (fun s : ℂ => (s - ρ)⁻¹) z :=
    (contDiffAt_id.sub contDiffAt_const).inv hne
  have h1 : (fun s : ℂ => c / (s - ρ)) = fun s => c * (s - ρ)⁻¹ := by
    funext s
    rw [div_eq_mul_inv]
  have h2 : iteratedDeriv k (fun s : ℂ => (s - ρ)⁻¹) z = iteratedDeriv k Inv.inv (z - ρ) :=
    congrFun (iteratedDeriv_comp_sub_const k Inv.inv ρ) z
  rw [h1, iteratedDeriv_const_mul c hcd, h2, iteratedDeriv_eq_iterate, iter_deriv_inv,
    show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

/-- A function with a genuine simple pole at `ρ` is not continuous there. -/
theorem not_continuousAt_of_simple_pole {Φ h : ℂ → ℂ} {ρ c : ℂ} (hc : c ≠ 0)
    (hh : ContinuousAt h ρ) (hp : ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s) :
    ¬ContinuousAt Φ ρ := by
  intro hΦ
  have hsub : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℂ => s - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)) :=
      (continuous_id.sub continuous_const).tendsto ρ
    rw [sub_self] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun s : ℂ => (s - ρ) * Φ s) (𝓝[≠] ρ) (𝓝 (0 * Φ ρ)) :=
    hsub.mul (hΦ.tendsto.mono_left nhdsWithin_le_nhds)
  have h2 : Tendsto (fun s : ℂ => c + (s - ρ) * h s) (𝓝[≠] ρ) (𝓝 (c + 0 * h ρ)) :=
    tendsto_const_nhds.add (hsub.mul (hh.tendsto.mono_left nhdsWithin_le_nhds))
  have heq : (fun s : ℂ => (s - ρ) * Φ s) =ᶠ[𝓝[≠] ρ] fun s => c + (s - ρ) * h s := by
    filter_upwards [hp, self_mem_nhdsWithin] with s hs hsne
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hsne
    rw [hs]
    field_simp
  have hlim := tendsto_nhds_unique (h1.congr' heq) h2
  rw [zero_mul, zero_mul, add_zero] at hlim
  exact hc hlim.symm

/-- **Taylor coefficients near a simple pole.** The pole contributes `c/(z-ρ)^{k+1}`; the rest is
bounded by Cauchy's estimate on the full disc. -/
theorem exists_taylorCoeff_sub_pole_le {Φ : ℂ → ℂ} {z ρ c : ℂ} {r r' : ℝ} (hne : ρ ≠ z)
    (hd : DifferentiableOn ℂ Φ (ball z r \ {ρ}))
    (hp : ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s)
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ,
      ‖(-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ) - c / (z - ρ) ^ (k + 1)‖ ≤
        M / r' ^ k := by
  obtain ⟨h, hh, hp⟩ := hp
  classical
  -- remove the pole
  set Ψ : ℂ → ℂ := Function.update (fun s => Φ s - c / (s - ρ)) ρ (h ρ) with hΨ
  have hΨne : ∀ s, s ≠ ρ → Ψ s = Φ s - c / (s - ρ) := fun s hs => Function.update_of_ne hs _ _
  have hΨρ : Ψ =ᶠ[𝓝 ρ] h := by
    have hp' : ∀ᶠ s in 𝓝[≠] ρ, Ψ s = h s := by
      filter_upwards [hp, self_mem_nhdsWithin] with s hs hsne
      rw [hΨne s hsne, hs]
      ring
    rw [eventually_nhdsWithin_iff] at hp'
    filter_upwards [hp'] with s hs
    by_cases hsρ : s = ρ
    · rw [hsρ, hΨ, Function.update_self]
    · exact hs hsρ
  have hΨd : DifferentiableOn ℂ Ψ (ball z r) := by
    intro s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]
      exact (hh.differentiableAt.congr_of_eventuallyEq hΨρ).differentiableWithinAt
    · have hopen : IsOpen (ball z r \ {ρ}) := isOpen_ball.sdiff isClosed_singleton
      have hΦs : DifferentiableAt ℂ Φ s :=
        (hd s ⟨hs, hsρ⟩).differentiableAt (hopen.mem_nhds ⟨hs, hsρ⟩)
      have hps : DifferentiableAt ℂ (fun s : ℂ => c / (s - ρ)) s :=
        (differentiableAt_const c).div (differentiableAt_id.sub (differentiableAt_const ρ))
          (sub_ne_zero.mpr hsρ)
      have heq : Ψ =ᶠ[𝓝 s] fun s => Φ s - c / (s - ρ) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hsρ] with w hw
        exact hΨne w hw
      exact ((hΦs.sub hps).congr_of_eventuallyEq heq).differentiableWithinAt
  obtain ⟨M, hM⟩ := exists_taylorCoeff_le hΨd h0 h1
  refine ⟨M, fun k => ?_⟩
  have hzρ : z ≠ ρ := hne.symm
  have hΨan : AnalyticAt ℂ Ψ z :=
    hΨd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (h0.trans h1)))
  have hpole : ContDiffAt ℂ k (fun s : ℂ => c / (s - ρ)) z :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hzρ)
  have heqz : Φ =ᶠ[𝓝 z] fun s => Ψ s + c / (s - ρ) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hzρ] with w hw
    rw [hΨne w hw]
    ring
  have hsum : iteratedDeriv k Φ z =
      iteratedDeriv k Ψ z + iteratedDeriv k (fun s : ℂ => c / (s - ρ)) z := by
    rw [heqz.iteratedDeriv_eq]
    exact iteratedDeriv_fun_add hΨan.contDiffAt hpole
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpow : (z - ρ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzρ)
  have hsq : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  have hsplit : (-1 : ℂ) ^ k * (iteratedDeriv k Ψ z +
        c * ((-1) ^ k * (k.factorial : ℂ) * ((z - ρ) ^ (k + 1))⁻¹)) / (k.factorial : ℂ) =
      (-1) ^ k * (iteratedDeriv k Ψ z / (k.factorial : ℂ)) +
        (-1 : ℂ) ^ k * (-1 : ℂ) ^ k * (c / (z - ρ) ^ (k + 1)) := by
    field_simp
  rw [hsum, iteratedDeriv_const_div_sub c hzρ k, hsplit, hsq, one_mul, add_sub_cancel_right,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hM k

end

end WindowedLandauTheory
