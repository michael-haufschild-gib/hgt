import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The reciprocal of zeta vanishes at the pole

`ζ` has a simple pole at `1` with residue `1`, so `(s-1) ζ(s) → 1` there.  Writing
`ζ(s)⁻¹ = (s-1) · ((s-1) ζ(s))⁻¹` exhibits the reciprocal as a vanishing factor times a factor
tending to one, so the reciprocal tends to zero.

Along the real ray `s = 1 + σ` with `σ ↓ 0` this is the analytic input that pins the value of the
Möbius harmonic series: the Dirichlet series `∑ μ(n) n^{-1-σ}` is `ζ(1+σ)⁻¹`, and its Abel limit
is `∑ μ(n)/n`.

* `deningerInvZeta_tendsto_zero` : **`ζ(s)⁻¹ → 0` as `s → 1`.**
* `deningerInvZetaRay_tendsto_zero` : the same along the real ray `1 + σ`, `σ ↓ 0`.
-/

namespace RHTower

open Filter Topology

noncomputable section

/-- **The reciprocal of zeta vanishes at the pole.** -/
theorem deningerInvZeta_tendsto_zero :
    Tendsto (fun s : ℂ => (riemannZeta s)⁻¹) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
  have hres := riemannZeta_residue_one
  have hinv : Tendsto (fun s : ℂ => ((s - 1) * riemannZeta s)⁻¹) (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
    have := hres.inv₀ (one_ne_zero)
    rwa [inv_one] at this
  have hsub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hc : Continuous fun s : ℂ => s - 1 := by fun_prop
    have hcont : Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 0) := by
      have hh := hc.tendsto (1 : ℂ)
      rwa [sub_self] at hh
    exact hcont.mono_left nhdsWithin_le_nhds
  have hprod := hsub.mul hinv
  rw [zero_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs1, one_mul]

/-- The same along the real ray `s = 1 + σ` with `σ ↓ 0`. -/
theorem deningerInvZetaRay_tendsto_zero :
    Tendsto (fun σ : ℝ => (riemannZeta (1 + (σ : ℂ)))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine deningerInvZeta_tendsto_zero.comp ?_
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : Tendsto (fun σ : ℝ => (1 : ℂ) + (σ : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (1 : ℂ)) := by
      have hc2 : Continuous fun σ : ℝ => (1 : ℂ) + (σ : ℂ) := by fun_prop
      have hh := hc2.tendsto (0 : ℝ)
      rwa [Complex.ofReal_zero, add_zero] at hh
    exact hcont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ0 : (0 : ℝ) < σ := hσ
    intro hcon
    rw [Set.mem_singleton_iff] at hcon
    have : (σ : ℂ) = 0 := by
      have h := hcon
      have : (1 : ℂ) + (σ : ℂ) - 1 = 0 := by rw [h]; ring
      linear_combination this
    have : σ = 0 := by exact_mod_cast this
    linarith

end

end RHTower
