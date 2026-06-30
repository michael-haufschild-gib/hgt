/-
# Böttcher tower — the order-`n` resonance (the full local natural-boundary obstruction)

At a repelling periodic point `z₀` of `f_c` (`F = f_c^[p]`, `F z₀ = z₀`, multiplier `λ`), a
hypothetical analytic continuation `g` of `φ_c` satisfies the functional equation `g ∘ F = g^d` near
`z₀` (`d = 2^p`), with `g z₀ = ζ` a `(d-1)`-th root of unity (`ζ^d = ζ`, `ζ ≠ 0`, since
`|g| = exp G_c ≥ 1`). Expanding `g - ζ = (z - z₀)^n • u` to its leading order `n` and matching the two
sides of `g ∘ F = g^d` forces the **resonance** `λ^n = d`.

The decisive consequence (`const_of_no_resonance`): when the multiplier is *non-resonant*
(`λ^m ≠ d` for every `m ≥ 1` — the nonexceptional case), `g` must be locally **constant**, which
contradicts `|g| = exp G_c` being non-constant on the basin. This is the complete local obstruction:
no continuation of `φ_c` across a non-resonant repelling periodic point. The only remaining global
input to the `J_c` natural boundary is then the **density** of such points in `J_c`.

This upgrades the first-order `Resonance.deriv_eq_zero_of_resonance` to all orders, via the analytic
order API (`AnalyticAt.analyticOrderAt_eq_natCast`) and the slope limit `(Fz-z₀)/(z-z₀) → λ`.

New file (hRigid connected lane, D2 — the local obstruction). General lemma; Mathlib only.
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

open Filter Topology

namespace Bottcher

/-- **Order-`n` resonance.** If `g ∘ F = g^d` near a fixed point `z₀` of `F` with multiplier `λ`,
`g z₀ = ζ` with `ζ^d = ζ` and `ζ ≠ 0`, and `g - ζ` has a zero of order `n` at `z₀` (i.e. `g` is
non-constant there), then `λ^n = d`. -/
theorem resonance_order {F g : ℂ → ℂ} {z₀ ζ lam : ℂ} {d n : ℕ}
    (hd : 1 ≤ d) (hF : AnalyticAt ℂ F z₀) (hg : AnalyticAt ℂ g z₀)
    (hFz : F z₀ = z₀) (hlam : HasDerivAt F lam z₀)
    (hgz : g z₀ = ζ) (hζ0 : ζ ≠ 0) (hζ : ζ ^ d = ζ)
    (heq : (fun z => g (F z)) =ᶠ[𝓝 z₀] (fun z => g z ^ d))
    (hn : analyticOrderAt (fun z => g z - ζ) z₀ = (n : ℕ∞)) :
    lam ^ n = (d : ℂ) := by
  have hh : AnalyticAt ℂ (fun z => g z - ζ) z₀ := hg.sub analyticAt_const
  obtain ⟨u, hu_an, hu_ne, hfac⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hh).mp hn
  have hζpow : ζ ^ (d - 1) = 1 := by
    have hd1 : d - 1 + 1 = d := Nat.sub_add_cancel hd
    have he : ζ ^ (d - 1) * ζ = 1 * ζ := by rw [one_mul, ← pow_succ, hd1, hζ]
    exact mul_right_cancel₀ hζ0 he
  have hS_an : AnalyticAt ℂ (fun z => ∑ k ∈ Finset.range d, g z ^ k * ζ ^ (d - 1 - k)) z₀ := by
    apply Finset.analyticAt_fun_sum; intro k hk; exact (hg.pow k).mul analyticAt_const
  have hSz : (∑ k ∈ Finset.range d, g z₀ ^ k * ζ ^ (d - 1 - k)) = (d : ℂ) := by
    have hterm : ∀ k ∈ Finset.range d, g z₀ ^ k * ζ ^ (d - 1 - k) = 1 := by
      intro k hk
      rw [hgz, ← pow_add]
      have hkk : k + (d - 1 - k) = d - 1 := by
        have : k ≤ d - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hk); omega
      rw [hkk, hζpow]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hstar : ∀ᶠ z in 𝓝 z₀,
      g (F z) - ζ = (∑ k ∈ Finset.range d, g z ^ k * ζ ^ (d - 1 - k)) * (g z - ζ) := by
    filter_upwards [heq] with z hz
    have : g (F z) = g z ^ d := hz
    rw [this, geom_sum₂_mul (g z) ζ d, hζ]
  have hFt : Tendsto F (𝓝 z₀) (𝓝 z₀) := by
    have := hF.continuousAt; rw [ContinuousAt, hFz] at this; exact this
  have hfacF : ∀ᶠ z in 𝓝 z₀, g (F z) - ζ = (F z - z₀) ^ n • u (F z) := hFt.eventually hfac
  have hkey : (fun z => slope F z₀ z ^ n * u (F z)) =ᶠ[𝓝[≠] z₀]
      (fun z => (∑ k ∈ Finset.range d, g z ^ k * ζ ^ (d - 1 - k)) * u z) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hfac, nhdsWithin_le_nhds hfacF,
      nhdsWithin_le_nhds hstar] with z hz hfz hfFz hsz
    have hzne : z ≠ z₀ := hz
    have hsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hzne
    have hslopeid : F z - z₀ = (z - z₀) * slope F z₀ z := by
      rw [slope_def_field, mul_div_cancel₀ _ hsub, hFz]
    have hcomb : (F z - z₀) ^ n * u (F z)
        = (∑ k ∈ Finset.range d, g z ^ k * ζ ^ (d - 1 - k)) * ((z - z₀) ^ n * u z) := by
      have e1 : (F z - z₀) ^ n * u (F z) = g (F z) - ζ := by rw [hfFz]; rw [smul_eq_mul]
      have e2 : (z - z₀) ^ n * u z = g z - ζ := by rw [← smul_eq_mul, ← hfz]
      rw [e1, e2, hsz]
    rw [hslopeid, mul_pow] at hcomb
    have hpow : (z - z₀) ^ n ≠ 0 := pow_ne_zero n hsub
    have hcomb2 : (z - z₀) ^ n * (slope F z₀ z ^ n * u (F z))
        = (z - z₀) ^ n * ((∑ k ∈ Finset.range d, g z ^ k * ζ ^ (d - 1 - k)) * u z) := by
      ring_nf; ring_nf at hcomb; linear_combination hcomb
    exact mul_left_cancel₀ hpow hcomb2
  have hslope : Tendsto (slope F z₀) (𝓝[≠] z₀) (𝓝 lam) := hasDerivAt_iff_tendsto_slope.mp hlam
  have huF : Tendsto (fun z => u (F z)) (𝓝[≠] z₀) (𝓝 (u z₀)) :=
    ((hu_an.continuousAt.tendsto).comp hFt).mono_left nhdsWithin_le_nhds
  have hLHS : Tendsto (fun z => slope F z₀ z ^ n * u (F z)) (𝓝[≠] z₀) (𝓝 (lam ^ n * u z₀)) :=
    (hslope.pow n).mul huF
  have hS_tend : Tendsto (fun z => ∑ k ∈ Finset.range d, g z ^ k * ζ ^ (d - 1 - k))
      (𝓝[≠] z₀) (𝓝 (∑ k ∈ Finset.range d, g z₀ ^ k * ζ ^ (d - 1 - k))) :=
    (hS_an.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hu_tend : Tendsto u (𝓝[≠] z₀) (𝓝 (u z₀)) :=
    (hu_an.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hRHS : Tendsto (fun z => (∑ k ∈ Finset.range d, g z ^ k * ζ ^ (d - 1 - k)) * u z)
      (𝓝[≠] z₀) (𝓝 ((∑ k ∈ Finset.range d, g z₀ ^ k * ζ ^ (d - 1 - k)) * u z₀)) :=
    hS_tend.mul hu_tend
  have heqlim : lam ^ n * u z₀ = (∑ k ∈ Finset.range d, g z₀ ^ k * ζ ^ (d - 1 - k)) * u z₀ :=
    tendsto_nhds_unique hLHS (hRHS.congr' hkey.symm)
  rw [hSz] at heqlim
  exact mul_right_cancel₀ hu_ne heqlim

/-- **No-resonance ⟹ locally constant continuation.** If `g ∘ F = g^d` near a fixed point `z₀` with
multiplier `λ`, `g z₀ = ζ` a `(d-1)`-th root of unity (`ζ^d = ζ`, `ζ ≠ 0`), and the multiplier is
*non-resonant* (`λ^m ≠ d` for all `m ≥ 1`), then `g` is constant `= ζ` near `z₀`. Contrapositive: a
non-constant continuation forces the resonance `λ^m = d`. This is the local natural-boundary
obstruction at a non-resonant repelling periodic point of `φ_c`. -/
theorem const_of_no_resonance {F g : ℂ → ℂ} {z₀ ζ lam : ℂ} {d : ℕ}
    (hd : 1 ≤ d) (hF : AnalyticAt ℂ F z₀) (hg : AnalyticAt ℂ g z₀)
    (hFz : F z₀ = z₀) (hlam : HasDerivAt F lam z₀)
    (hgz : g z₀ = ζ) (hζ0 : ζ ≠ 0) (hζ : ζ ^ d = ζ)
    (heq : (fun z => g (F z)) =ᶠ[𝓝 z₀] (fun z => g z ^ d))
    (hres : ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ (d : ℂ)) :
    ∀ᶠ z in 𝓝 z₀, g z = ζ := by
  by_contra hnc
  have hh : AnalyticAt ℂ (fun z => g z - ζ) z₀ := hg.sub analyticAt_const
  have hev : ¬ (∀ᶠ z in 𝓝 z₀, (fun z => g z - ζ) z = 0) := by
    intro hcon; apply hnc; filter_upwards [hcon] with z hz; simpa [sub_eq_zero] using hz
  have hord_ne_top : analyticOrderAt (fun z => g z - ζ) z₀ ≠ ⊤ :=
    fun hcon => hev (analyticOrderAt_eq_top.mp hcon)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hord_ne_top
  have hn' : analyticOrderAt (fun z => g z - ζ) z₀ = (n : ℕ∞) := hn.symm
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, analyticOrderAt_eq_zero] at hn'
      rcases hn' with hna | hne
      · exact hna hh
      · exact hne (by simp [hgz])
    · exact hpos
  exact hres n hn1 (resonance_order hd hF hg hFz hlam hgz hζ0 hζ heq hn')

end Bottcher
