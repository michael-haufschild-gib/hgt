import GaloisForLFunctions.Bottcher.FarFieldUnivalence
import GaloisForLFunctions.Bottcher.BottcherCoord

open Complex Metric Set Filter Topology

namespace Bottcher

/-- **Functional equation of the far-field inverse Böttcher `ψ`.** If `ψ` is any left inverse of the
Böttcher coordinate on the far field `{‖z‖ > R}` (as produced by `exists_analytic_inverse_far`), then
`ψ` satisfies the inverse Böttcher functional equation `ψ(w²) = ψ(w)² + c` at every `w = φ_c z` with
`‖z‖ > R`. Proof: `φ_c(z²+c) = φ_c(z)²` (`bottcherCoord_quadratic`); `z²+c` is again in the far field
(a norm bound from `hR1`,`hR2`), so `ψ(φ_c(z²+c)) = z²+c`; combine with `ψ(φ_c z) = z`. -/
theorem psi_functional_eq_of_inverts {c : ℂ} {R : ℝ} {ψ : ℂ → ℂ}
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2)
    (hψ : ∀ z, R < ‖z‖ → ψ (bottcherCoord c z) = z) (z : ℂ) (hz : R < ‖z‖) :
    ψ ((bottcherCoord c z) ^ 2) = (ψ (bottcherCoord c z)) ^ 2 + c := by
  have hmax : max 2 ‖c‖ < R := by
    have : (0:ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left 2 ‖c‖)
    linarith
  have hc_le : ‖c‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right 2 ‖c‖) (lt_trans hmax hz))
  have hz2 : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) (lt_trans hmax hz)
  have hR4 : (4:ℝ) < R := by
    have h2 : (2:ℝ) ≤ max 2 ‖c‖ := le_max_left 2 ‖c‖
    linarith
  have hc_half : 2 * ‖c‖ < R := by
    have : ‖c‖ ≤ max 2 ‖c‖ := le_max_right 2 ‖c‖
    linarith
  -- z^2 + c is again in the far field
  have hRpos : (0:ℝ) < R := by linarith
  have hzsq : R ^ 2 < ‖z‖ ^ 2 := by nlinarith [hz, hRpos, norm_nonneg z]
  have hfz_far : R < ‖quadratic c z‖ := by
    have hge : ‖z‖ ^ 2 - ‖c‖ ≤ ‖z ^ 2 + c‖ := by
      have h := norm_sub_norm_le (z ^ 2) (-c)
      rw [sub_neg_eq_add, norm_neg, norm_pow] at h
      exact h
    have : R < ‖z‖ ^ 2 - ‖c‖ := by nlinarith [hzsq, hc_half, hR4]
    have hq : quadratic c z = z ^ 2 + c := rfl
    rw [hq]; linarith [hge, this]
  have hquad : bottcherCoord c (quadratic c z) = (bottcherCoord c z) ^ 2 :=
    bottcherCoord_quadratic hc_le hz2
  rw [← hquad, hψ (quadratic c z) hfz_far, hψ z hz]
  rfl

/-- **Change-of-variables core for the disk model `h(t) = t·ψ(1/t)`.** If `ψ` is odd and satisfies the
inverse Böttcher functional equation `ψ(w²)=ψ(w)²+c` on the far field `{‖w‖>R}`, then `h` is even and
satisfies the model functional equation `h(t²)=h(t)²+c·t²` on the punctured disk `{0<‖t‖<R⁻¹}`
(where `‖1/t‖>R`). Pure algebra; the analytic inputs (`ψ` odd, `ψ` FE) are supplied separately
(`psi_functional_eq_of_inverts` and the `φ_c`-oddness lemma). -/
theorem model_even_and_fe {c : ℂ} {R : ℝ} (hR : 0 < R) {ψ : ℂ → ℂ}
    (hodd : ∀ w, R < ‖w‖ → ψ (-w) = -ψ w)
    (hfe  : ∀ w, R < ‖w‖ → ψ (w ^ 2) = (ψ w) ^ 2 + c)
    (t : ℂ) (ht0 : t ≠ 0) (htR : ‖t‖ < R⁻¹) :
    (-t) * ψ (1 / -t) = t * ψ (1 / t) ∧
    (t ^ 2) * ψ (1 / t ^ 2) = (t * ψ (1 / t)) ^ 2 + c * t ^ 2 := by
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have hinv : R < ‖(1 : ℂ) / t‖ := by
    rw [one_div, norm_inv]
    exact (lt_inv_comm₀ hR htn).mpr htR
  refine ⟨?_, ?_⟩
  · have h1 : (1 : ℂ) / -t = -(1 / t) := by rw [one_div, one_div, inv_neg]
    rw [h1, hodd (1 / t) hinv]; ring
  · have h2 : (1 : ℂ) / t ^ 2 = (1 / t) ^ 2 := by rw [div_pow, one_pow]
    rw [h2, hfe (1 / t) hinv]; ring

/-- Each Böttcher log-term is even in `z`: `termₖ(-z) = termₖ(z)`. The term depends on `z` only
through `((quadratic c)^[k] z)²`, and `quadratic c` is even (`f(-z)=f(z)`), so for `k=0` it is `(-z)²`
and for `k≥1` the iterate values already coincide. -/
theorem bottcherLogTerm_neg (c z : ℂ) (k : ℕ) :
    bottcherLogTerm c (-z) k = bottcherLogTerm c z k := by
  have hsq : ((quadratic c)^[k] (-z)) ^ 2 = ((quadratic c)^[k] z) ^ 2 := by
    cases k with
    | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply, neg_sq]
    | succ n =>
      have hval : (quadratic c)^[n + 1] (-z) = (quadratic c)^[n + 1] z := by
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        congr 1
        show (-z) ^ 2 + c = z ^ 2 + c
        rw [neg_sq]
      rw [hval]
  unfold bottcherLogTerm
  rw [hsq]

/-- **The Böttcher coordinate is odd**: `φ_c(-z) = -φ_c(z)` for all `z ≠ 0`. Since `f(z)=z²+c` is even,
every log-term is even (`bottcherLogTerm_neg`), so the `z·exp(∑ₖ termₖ)` factorization gives
`φ_c(-z) = (-z)·exp(∑ termₖ(z)) = -φ_c(z)`. This is the `z↦-z` symmetry underlying the even disk
model `h(t)=t·ψ(1/t)`. -/
theorem bottcherCoord_neg {c z : ℂ} (hz : z ≠ 0) :
    bottcherCoord c (-z) = - bottcherCoord c z := by
  rw [bottcherCoord_eq_mul_exp (neg_ne_zero.mpr hz), bottcherCoord_eq_mul_exp hz,
      tsum_congr (bottcherLogTerm_neg c z)]
  ring

/-- **Oddness of the far-field inverse `ψ` at image points.** For `z` in the far field,
`-φ_c z = φ_c(-z)` (oddness of `φ_c`), and `ψ` inverts `φ_c` there, so
`ψ(-φ_c z) = -z = -ψ(φ_c z)`. This is the `hodd` input of `model_even_and_fe`, restricted to the
image `φ_c({‖z‖>R})` where `ψ` is a genuine inverse. -/
theorem psi_odd_of_inverts {c : ℂ} {R : ℝ} (hR0 : 0 ≤ R) {ψ : ℂ → ℂ}
    (hψ : ∀ z, R < ‖z‖ → ψ (bottcherCoord c z) = z) (z : ℂ) (hz : R < ‖z‖) :
    ψ (-(bottcherCoord c z)) = -(ψ (bottcherCoord c z)) := by
  have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz; linarith
  have hnegfar : R < ‖(-z : ℂ)‖ := by rwa [norm_neg]
  rw [← bottcherCoord_neg hz0, hψ (-z) hnegfar, hψ z hz]

/-- **`h(0) = 1` normalization of the disk model.** If `ψ(w) - w → 0` at infinity (the far-field
inverse is asymptotic to the identity, from `φ_c(z) - z → 0`), then `h(t) = t·ψ(1/t) → 1` as `t → 0`:
write `t·ψ(1/t) = t·(ψ(1/t) - 1/t) + 1`, where `t·(ψ(1/t)-1/t) → 0` since both factors vanish. Together
with `model_even_and_fe` and a removable-singularity extension this gives the `h 0 = 1` hypothesis of
`natural_boundary_of_even_fe`. -/
theorem model_tendsto_one {ψ : ℂ → ℂ}
    (hψ : Tendsto (fun w => ψ w - w) (Bornology.cobounded ℂ) (𝓝 0)) :
    Tendsto (fun t : ℂ => t * ψ (1 / t)) (𝓝[≠] 0) (𝓝 1) := by
  have hinv : Tendsto (fun t : ℂ => 1 / t) (𝓝[≠] (0:ℂ)) (Bornology.cobounded ℂ) := by
    simpa [one_div] using
      (tendsto_inv₀_nhdsNE_zero : Tendsto (fun t : ℂ => t⁻¹) _ _)
  have hg : Tendsto (fun t : ℂ => ψ (1 / t) - 1 / t) (𝓝[≠] (0:ℂ)) (𝓝 0) := hψ.comp hinv
  have ht0 : Tendsto (fun t : ℂ => t) (𝓝[≠] (0:ℂ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hprod : Tendsto (fun t : ℂ => t * (ψ (1 / t) - 1 / t)) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    simpa using ht0.mul hg
  have hmain : Tendsto (fun t : ℂ => t * (ψ (1 / t) - 1 / t) + 1) (𝓝[≠] (0:ℂ)) (𝓝 (0 + 1)) :=
    hprod.add tendsto_const_nhds
  rw [zero_add] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  field_simp
  ring

end Bottcher
