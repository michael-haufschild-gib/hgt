import GaloisForLFunctions.RHTower.KreinRepresentationMassLaw
import GaloisForLFunctions.RHTower.ClusterInterpolationContour

/-!
# The tilted kernel divided at an off-line pair

For a nontrivial zero `ρ₀ = β₀ + it₀` with `β₀ > 1/2`, put `γ₀ = gammaOf ρ₀ = t₀ - iδ₀`
(`δ₀ = β₀ - 1/2`) and `γ₁ = conj γ₀ = gammaOf (1 - conj ρ₀)`. The kernel
`h = D_{γ₀}^{m₀} D_{γ₁}^{m₁} Φ_θ` (iterated resolvent division of the tilted Riemann kernel)
decays super-exponentially and `(z - γ₀)^{m₀}(z - γ₁)^{m₁} ĥ(z) = e^{zθ} Ξ(z)`
(`pairKernel_spec`).

If every other zero has ordinate at distance `≥ δ` from `t₀` and `δ₀ ≤ δ/2`, then `ĥ` has no zero in
the disc `|z - t₀| ≤ 3δ/4`, and on its boundary `|ĥ| ≥ |e^{zθ}Ξ(z)| ≥ m_V(θ, t₀, δ/2)`: the lower
half is joined to `Re s = 2` by horizontal paths avoiding every zero by `δ/4`, the upper half is its
mirror image under `|Ξ(z̄)| = |Ξ(z)|`. By the minimum modulus principle,
`|ĥ(γ₀)|, |ĥ(γ₁)| ≥ m_V(θ, t₀, δ/2)` (`norm_pairKernel_ge`).
-/

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## The local factor at any nontrivial zero -/

/-- **Local factor of the tilted kernel at a nontrivial zero.** For `ρ₀` of multiplicity `m₀`:
`Φ̂_θ(z) = (z - γ₀)^{m₀} v(z)` near `γ₀ = gammaOf ρ₀`, with `v` analytic and `v(γ₀) ≠ 0`. -/
theorem exists_tiltedPhi_local_factor_gammaOf {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v (gammaOf ρ₀) ∧ v (gammaOf ρ₀) ≠ 0 ∧
      paperFT (tiltedPhi θ) =ᶠ[𝓝 (gammaOf ρ₀)]
        fun z => (z - gammaOf ρ₀) ^ (zetaZeroConfig.mult ρ₀) * v z := by
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  obtain ⟨u, hu, hu0, hloc⟩ := exists_zeta_local_factor hρ₀
  set m := zetaZeroConfig.mult ρ₀
  set γ : ℂ := gammaOf ρ₀ with hγ
  have hsγ : 1 / 2 + I * γ = ρ₀ := one_half_add_I_mul_gammaOf ρ₀
  have hρ0 : ρ₀ ≠ 0 := fun h => by have := hnt.2.1; rw [h] at this; simp at this
  have hρ1 : ρ₀ ≠ 1 := fun h => by have := hnt.2.2; rw [h] at this; simp at this
  have hmap : Tendsto (fun z : ℂ => 1 / 2 + I * z) (𝓝 γ) (𝓝 ρ₀) := by
    have : Continuous fun z : ℂ => 1 / 2 + I * z := by fun_prop
    have h := this.tendsto γ
    rwa [hsγ] at h
  have hre : ∀ᶠ s in 𝓝 ρ₀, 0 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hnt.2.1
  have hn0 : ∀ᶠ s in 𝓝 ρ₀, s ≠ 0 := eventually_ne_nhds hρ0
  have hn1 : ∀ᶠ s in 𝓝 ρ₀, s ≠ 1 := eventually_ne_nhds hρ1
  have hall := hmap.eventually (hloc.and (hre.and (hn0.and hn1)))
  have him : ∀ᶠ z in 𝓝 γ, |z.im| ≤ 1 / 2 := by
    have hc : Continuous fun z : ℂ => |z.im| := by fun_prop
    have : |γ.im| < 1 / 2 := WeilEF.abs_gammaOf_im_lt ⟨hnt.2.1, hnt.2.2⟩
    exact (hc.tendsto γ).eventually (Iio_mem_nhds this) |>.mono fun z hz => le_of_lt hz
  set v : ℂ → ℂ := fun z => cexp (z * θ) * (I ^ m * (xiUnit (1 / 2 + I * z) * u (1 / 2 + I * z)))
    with hv
  have hxiU : AnalyticAt ℂ xiUnit ρ₀ := analyticAt_xiUnit hnt.2.1
  refine ⟨v, ?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun z : ℂ => xiUnit (1 / 2 + I * z)) γ :=
      hxiU.comp_of_eq (by fun_prop) hsγ
    have h2 : AnalyticAt ℂ (fun z : ℂ => u (1 / 2 + I * z)) γ :=
      hu.comp_of_eq (by fun_prop) hsγ
    have h3 : AnalyticAt ℂ (fun z : ℂ => cexp (z * θ)) γ := by fun_prop
    exact h3.mul (analyticAt_const.mul (h1.mul h2))
  · simp only [hv, hsγ]
    exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
      (mul_ne_zero (xiUnit_ne_zero hρ0 hρ1 hnt.2.1) hu0))
  · filter_upwards [hall, him] with z hz hzim
    obtain ⟨hζ, hre', hz0, hz1⟩ := hz
    rw [paperFT_tiltedPhi hθ0 hθ hzim, ← riemannXiHat_eq,
      riemannXiHat_eq_xiUnit_mul_zeta hre' hz0 hz1, hζ]
    have e : 1 / 2 + I * z - ρ₀ = I * (z - γ) := by rw [← hsγ]; ring
    rw [e, mul_pow]; simp only [hv]; ring

/-! ## The pair kernel -/

/-- `D_{γ₀}^{m₀} D_{γ̄₀}^{m₁} Φ_θ`. -/
def pairKernel (θ : ℝ) (γ₀ : ℂ) (m₀ m₁ : ℕ) : ℝ → ℂ :=
  iterResolvent γ₀ m₀ (iterResolvent ((starRingEnd ℂ) γ₀) m₁ (tiltedPhi θ))

/-- **The pair kernel.** Given the local factors of `Φ̂_θ` at `γ₀` and `γ̄₀` (`Im γ₀ ≠ 0`), the pair
kernel decays super-exponentially, `(z - γ₀)^{m₀}(z - γ̄₀)^{m₁} ĥ = Φ̂_θ`, `ĥ` does not vanish at the
pair, and its weighted tails are those of `Φ_θ` up to `2^{m₀+m₁}` and a weight shift. -/
theorem pairKernel_spec {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {γ₀ : ℂ} (him : γ₀.im ≠ 0)
    (him2 : |γ₀.im| ≤ 1 / 2) {m₀ m₁ : ℕ} {v₀ v₁ : ℂ → ℂ}
    (hv₀ : AnalyticAt ℂ v₀ γ₀) (hv₀0 : v₀ γ₀ ≠ 0)
    (hloc₀ : paperFT (tiltedPhi θ) =ᶠ[𝓝 γ₀] fun z => (z - γ₀) ^ m₀ * v₀ z)
    (hv₁ : AnalyticAt ℂ v₁ ((starRingEnd ℂ) γ₀)) (hv₁0 : v₁ ((starRingEnd ℂ) γ₀) ≠ 0)
    (hloc₁ : paperFT (tiltedPhi θ) =ᶠ[𝓝 ((starRingEnd ℂ) γ₀)]
      fun z => (z - (starRingEnd ℂ) γ₀) ^ m₁ * v₁ z) :
    SuperExpDecay (pairKernel θ γ₀ m₀ m₁) ∧
    (∀ z, (z - γ₀) ^ m₀ * (z - (starRingEnd ℂ) γ₀) ^ m₁ * paperFT (pairKernel θ γ₀ m₀ m₁) z =
      paperFT (tiltedPhi θ) z) ∧
    paperFT (pairKernel θ γ₀ m₀ m₁) γ₀ ≠ 0 ∧
    paperFT (pairKernel θ γ₀ m₀ m₁) ((starRingEnd ℂ) γ₀) ≠ 0 ∧
    ∀ c X : ℝ, 0 ≤ c → expTail (pairKernel θ γ₀ m₀ m₁) c X ≤
      2 ^ (m₀ + m₁) * expTail (tiltedPhi θ) (c + 3 / 2 * ((m₀ + m₁ : ℕ) : ℝ)) X := by
  set γ₁ := (starRingEnd ℂ) γ₀ with hγ₁
  have hne : γ₀ ≠ γ₁ := by
    intro h; have := congrArg Complex.im h; simp only [hγ₁, Complex.conj_im] at this
    exact him (by linarith)
  have him₁ : |γ₁.im| ≤ 1 / 2 := by simp only [hγ₁, Complex.conj_im, abs_neg]; exact him2
  have hΦ := superExpDecay_tiltedRiemannKernel hθ0 hθ
  set g₁ := iterResolvent γ₁ m₁ (tiltedPhi θ) with hg₁def
  obtain ⟨hg₁, hlocg₁, hprod₁⟩ := iterResolvent_spec hΦ him₁ hv₁.continuousAt hloc₁ m₁ le_rfl
  rw [Nat.sub_self] at hlocg₁
  have loc₀ : paperFT g₁ =ᶠ[𝓝 γ₀] fun z => (z - γ₀) ^ m₀ * (v₀ z / (z - γ₁) ^ m₁) :=
    iterResolvent_eventually_ne hΦ him₁ hv₁.continuousAt hloc₁ hne hloc₀ m₁ le_rfl
  have hcont : ContinuousAt (fun z => v₀ z / (z - γ₁) ^ m₁) γ₀ :=
    hv₀.continuousAt.div ((continuousAt_id.sub continuousAt_const).pow _)
      (pow_ne_zero _ (sub_ne_zero.mpr hne))
  obtain ⟨hK, hlocK, hprod₀⟩ := iterResolvent_spec hg₁ him2 hcont loc₀ m₀ le_rfl
  rw [Nat.sub_self] at hlocK
  have hK1 : paperFT (iterResolvent γ₀ m₀ g₁) =ᶠ[𝓝 γ₁]
      fun z => (z - γ₁) ^ 0 * (v₁ z / (z - γ₀) ^ m₀) :=
    iterResolvent_eventually_ne hg₁ him2 hcont loc₀ hne.symm hlocg₁ m₀ le_rfl
  refine ⟨hK, fun z => ?_, ?_, ?_, fun c X hc => ?_⟩
  · show (z - γ₀) ^ m₀ * (z - γ₁) ^ m₁ * paperFT (iterResolvent γ₀ m₀ g₁) z = _
    rw [mul_comm ((z - γ₀) ^ m₀), mul_assoc, hprod₀ z, hprod₁ z]
  · show paperFT (iterResolvent γ₀ m₀ g₁) γ₀ ≠ 0
    rw [hlocK.eq_of_nhds, pow_zero, one_mul]
    exact div_ne_zero hv₀0 (pow_ne_zero _ (sub_ne_zero.mpr hne))
  · show paperFT (iterResolvent γ₀ m₀ g₁) γ₁ ≠ 0
    rw [hK1.eq_of_nhds, pow_zero, one_mul]
    exact div_ne_zero hv₁0 (pow_ne_zero _ (sub_ne_zero.mpr hne.symm))
  · have h1 := expTail_iterResolvent_le hg₁ him2 hcont loc₀ m₀ le_rfl c X hc
    have h2 := expTail_iterResolvent_le hΦ him₁ hv₁.continuousAt hloc₁ m₁ le_rfl
      (c + 3 / 2 * m₀) X (by positivity)
    show expTail (iterResolvent γ₀ m₀ g₁) c X ≤ _
    refine h1.trans ?_
    calc (2 : ℝ) ^ m₀ * expTail g₁ (c + 3 / 2 * m₀) X
        ≤ 2 ^ m₀ * (2 ^ m₁ * expTail (tiltedPhi θ) (c + 3 / 2 * m₀ + 3 / 2 * m₁) X) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ (m₀ + m₁) * expTail (tiltedPhi θ) (c + 3 / 2 * ((m₀ + m₁ : ℕ) : ℝ)) X := by
          rw [pow_add]; push_cast; ring_nf

/-! ## `Ξ` near an off-line pair -/

theorem gammaOf_one_half_add_I_mul (z : ℂ) : gammaOf (1 / 2 + I * z) = z := by
  unfold gammaOf; field_simp; ring

/-- If every zero other than `ρ₀` and its mirror has ordinate at distance `≥ δ` from `t₀`, then
`Ξ(z) ≠ 0` for `|Re z - t₀| < δ`, `|Im z| < 1/2`, `z ∉ {γ₀, γ̄₀}`. -/
theorem riemannPhiTransform_ne_zero_near_pair {ρ₀ : ℂ} {δ : ℝ}
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ →
      δ ≤ |ρ.im - ρ₀.im|) {z : ℂ} (hz : |z.re - ρ₀.im| < δ) (him : |z.im| < 1 / 2)
    (h0 : z ≠ gammaOf ρ₀) (h1 : z ≠ gammaOf (Zeta23.reflect ρ₀)) :
    riemannPhiTransform (1 / 2 + I * z) ≠ 0 := by
  intro hΞ
  set s : ℂ := 1 / 2 + I * z with hs
  have hsre : s.re = 1 / 2 - z.im := by simp [hs]; ring
  have hsim : s.im = z.re := by simp [hs]
  have hsre0 : 0 < s.re := by rw [hsre]; linarith [(abs_lt.mp him).2]
  have hsre1 : s.re < 1 := by rw [hsre]; linarith [(abs_lt.mp him).1]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre0; simp at hsre0
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsre1; simp at hsre1
  rw [riemannPhiTransform_eq_xi, xi_eq_xiUnit_mul_zeta hs0 hs1 hsre0] at hΞ
  have hζ : riemannZeta s = 0 := by
    rcases mul_eq_zero.mp hΞ with h | h
    · exact absurd h (xiUnit_ne_zero hs0 hs1 hsre0)
    · exact h
  have hmem : s ∈ zetaZeroConfig.carrier := ⟨hζ, hsre0, hsre1⟩
  have hγs : gammaOf s = z := gammaOf_one_half_add_I_mul z
  have hs0' : s ≠ ρ₀ := fun h => h0 (by rw [← hγs, h])
  have hs1' : s ≠ Zeta23.reflect ρ₀ := fun h => h1 (by rw [← hγs, h])
  have := hsep s hmem hs0' hs1'
  rw [hsim] at this
  linarith

/-- On the lower half of the circle `|w - t₀| = 3δ/4`, the horizontal path from `1/2 + iw` to
`Re s = 2` avoids every zero by `δ/4`, when `|β₀ - 1/2| ≤ δ/2`. -/
theorem path_far_of_lower_pair_circle {ρ₀ : ℂ} {δ : ℝ}
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ →
      δ ≤ |ρ.im - ρ₀.im|) (hdep : |ρ₀.re - 1 / 2| ≤ δ / 2) {w : ℂ}
    (hw : ‖w - (ρ₀.im : ℂ)‖ = 3 * δ / 4) (hneg : w.im ≤ 0) :
    ∀ x ∈ Icc (1 / 2 - w.im) 2, ∀ ρ ∈ zetaZeroConfig.carrier,
      δ / 4 ≤ ‖(x : ℂ) + (w.re : ℂ) * I - ρ‖ := by
  intro x hx ρ hρ
  have hwre : |w.re - ρ₀.im| ≤ 3 * δ / 4 := by
    have := Complex.abs_re_le_norm (w - (ρ₀.im : ℂ)); rw [hw] at this; simpa using this
  by_cases hpair : ρ = ρ₀ ∨ ρ = Zeta23.reflect ρ₀
  · have hρim : ρ.im = ρ₀.im := by
      rcases hpair with h | h
      · rw [h]
      · rw [h]; simp [Zeta23.reflect]
    have hρre : |ρ.re - 1 / 2| ≤ δ / 2 := by
      rcases hpair with h | h
      · rw [h]; exact hdep
      · rw [h]; simp only [Zeta23.reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
        rw [show 1 - ρ₀.re - 1 / 2 = -(ρ₀.re - 1 / 2) by ring, abs_neg]; exact hdep
    set c : ℂ := (1 / 2 : ℂ) + (ρ₀.im : ℂ) * I with hc
    have hsq : (3 * δ / 4) ^ 2 ≤ ‖(x : ℂ) + (w.re : ℂ) * I - c‖ ^ 2 := by
      rw [← hw, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [hc, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
      have h1 : -w.im ≤ x - 1 / 2 := by linarith [hx.1]
      have h2 : 0 ≤ -w.im := by linarith
      norm_num
      nlinarith
    have hpc : 3 * δ / 4 ≤ ‖(x : ℂ) + (w.re : ℂ) * I - c‖ := by
      have h0 : 0 ≤ 3 * δ / 4 := by rw [← hw]; exact norm_nonneg _
      exact (pow_le_pow_iff_left₀ h0 (norm_nonneg _) two_ne_zero).mp hsq
    have hρc : ‖ρ - c‖ ≤ δ / 2 := by
      have e : ρ - c = ((ρ.re - 1 / 2 : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [hc]
        · simp [hc, hρim]
      rw [e, Complex.norm_real, Real.norm_eq_abs]; exact hρre
    have htri := norm_sub_norm_le ((x : ℂ) + (w.re : ℂ) * I - c) (ρ - c)
    rw [show (x : ℂ) + (w.re : ℂ) * I - c - (ρ - c) = (x : ℂ) + (w.re : ℂ) * I - ρ by ring]
      at htri
    linarith
  · push Not at hpair
    have h1 := hsep ρ hρ hpair.1 hpair.2
    have h3 : |w.re - ρ.im| ≤ ‖(x : ℂ) + (w.re : ℂ) * I - ρ‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + (w.re : ℂ) * I - ρ); simpa using this
    have h4 : |ρ.im - ρ₀.im| ≤ |w.re - ρ.im| + |w.re - ρ₀.im| := by
      calc |ρ.im - ρ₀.im| = |(w.re - ρ₀.im) - (w.re - ρ.im)| := by ring_nf
        _ ≤ |w.re - ρ₀.im| + |w.re - ρ.im| := abs_sub _ _
        _ = |w.re - ρ.im| + |w.re - ρ₀.im| := by ring
    linarith

/-- **The floor on the pair circle.** On `|z - t₀| = 3δ/4`:
`m_V(θ, t₀, δ/2) ≤ e^{θ Re z} |Ξ(z)|`. -/
theorem pair_circle_floor {θ : ℝ} (hθ0 : 0 ≤ θ) {ρ₀ : ℂ} (hγ : 8 ≤ ρ₀.im) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ →
      δ ≤ |ρ.im - ρ₀.im|) (hdep : |ρ₀.re - 1 / 2| ≤ δ / 2) {z : ℂ}
    (hz : ‖z - (ρ₀.im : ℂ)‖ = 3 * δ / 4) :
    dividedKernelFloor θ ρ₀.im (δ / 2) ≤
      Real.exp (θ * z.re) * ‖riemannPhiTransform (1 / 2 + I * z)‖ := by
  set γ₀ := ρ₀.im with hγ₀
  set w : ℂ := if z.im ≤ 0 then z else (starRingEnd ℂ) z with hw
  have hwre : w.re = z.re := by rw [hw]; split_ifs <;> simp
  have hwim : w.im ≤ 0 := by
    rw [hw]; split_ifs with h
    · exact h
    · simp; linarith
  have hwn : ‖w - (γ₀ : ℂ)‖ = 3 * δ / 4 := by
    rw [hw]; split_ifs
    · exact hz
    · rw [← hz]
      have : (starRingEnd ℂ) z - (γ₀ : ℂ) = (starRingEnd ℂ) (z - (γ₀ : ℂ)) := by simp
      rw [this, Complex.norm_conj]
  have hΞw : ‖riemannPhiTransform (1 / 2 + I * w)‖ = ‖riemannPhiTransform (1 / 2 + I * z)‖ := by
    rw [hw]; split_ifs
    · rfl
    · exact norm_riemannPhiTransform_conj z
  have hwim2 : -(1 / 2) ≤ w.im := by
    have := Complex.abs_im_le_norm (w - (γ₀ : ℂ)); rw [hwn] at this; simp at this
    linarith [(abs_le.mp this).1]
  have hwre2 : |w.re - γ₀| ≤ 3 * δ / 4 := by
    have := Complex.abs_re_le_norm (w - (γ₀ : ℂ)); rw [hwn] at this; simpa using this
  have hlow := norm_riemannPhiTransform_ge_near_line hwim2 hwim
    (by linarith [(abs_le.mp hwre2).1]) (by positivity : (0 : ℝ) < δ / 4) (by linarith)
    (path_far_of_lower_pair_circle hsep hdep hwn hwim)
  rw [hΞw, hwre] at hlow
  rw [hwre] at hwre2
  have hre1 := (abs_le.mp hwre2).1
  have hre2 := (abs_le.mp hwre2).2
  have hC := logDerivZetaConstant_nonneg
  have hc := xiNearLineLowerConst_pos
  have hfrac : (γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2) ≤ z.re ^ 2 / (1 + z.re) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hsq : (γ₀ - 1 / 2) ^ 2 ≤ z.re ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact mul_le_mul hsq (by linarith) (by linarith) (by positivity)
  have he1 : Real.exp (-(π * (γ₀ + 1 / 2) / 4)) ≤ Real.exp (-(π * z.re / 4)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hlog : Real.log z.re ≤ Real.log (γ₀ + 1) := Real.log_le_log (by linarith) (by linarith)
  have he2 : Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / (δ / 2))) ≤
      Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log z.re / (δ / 4))) := by
    apply Real.exp_le_exp.mpr
    rw [show 3 / 2 * logDerivZetaConstant * Real.log z.re / (δ / 4) =
      3 * logDerivZetaConstant * Real.log z.re / (δ / 2) by field_simp; ring]
    have : 3 * logDerivZetaConstant * Real.log z.re / (δ / 2) ≤
        3 * logDerivZetaConstant * Real.log (γ₀ + 1) / (δ / 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
  have heθ : Real.exp (θ * (γ₀ - 1 / 2)) ≤ Real.exp (θ * z.re) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hθ0)
  have hXi : xiNearLineLowerConst * ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) *
      Real.exp (-(π * (γ₀ + 1 / 2) / 4)) *
      Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / (δ / 2))) ≤
      ‖riemannPhiTransform (1 / 2 + I * z)‖ := by
    refine le_trans ?_ hlow
    have hB2 : 0 ≤ xiNearLineLowerConst * (z.re ^ 2 / (1 + z.re)) :=
      mul_nonneg hc.le (div_nonneg (sq_nonneg _) (by linarith))
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hfrac hc.le) he1
      (Real.exp_pos _).le hB2) he2 (Real.exp_pos _).le
      (mul_nonneg hB2 (Real.exp_pos _).le)
  unfold dividedKernelFloor
  calc Real.exp (θ * (γ₀ - 1 / 2)) * xiNearLineLowerConst * ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) *
        Real.exp (-(π * (γ₀ + 1 / 2) / 4)) *
        Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / (δ / 2)))
      = Real.exp (θ * (γ₀ - 1 / 2)) * (xiNearLineLowerConst *
          ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) * Real.exp (-(π * (γ₀ + 1 / 2) / 4)) *
          Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / (δ / 2)))) := by ring
    _ ≤ Real.exp (θ * z.re) * ‖riemannPhiTransform (1 / 2 + I * z)‖ :=
        mul_le_mul heθ hXi (by positivity) (Real.exp_pos _).le

/-- **Minimum modulus for a kernel divided at an off-line pair.** Let `h` decay
super-exponentially with `(z - γ₀)^{m₀}(z - γ̄₀)^{m₁} ĥ = Φ̂_θ`, `γ₀ = gammaOf ρ₀`, and
`ĥ(γ₀), ĥ(γ̄₀) ≠ 0`. If every other zero has ordinate at distance `≥ δ` from `t₀ ≥ 8` and
`|β₀ - 1/2| ≤ δ/2 ≤ 1/4`, then `|ĥ| ≥ m_V(θ, t₀, δ/2)` on the disc `|z - t₀| ≤ 3δ/4`. -/
theorem norm_divided_pair_ge {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ}
    (hγ : 8 ≤ ρ₀.im) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ →
      δ ≤ |ρ.im - ρ₀.im|) (hdep : |ρ₀.re - 1 / 2| ≤ δ / 2) {h : ℝ → ℂ} {m₀ m₁ : ℕ}
    (hh : SuperExpDecay h)
    (hprod : ∀ z, (z - gammaOf ρ₀) ^ m₀ * (z - (starRingEnd ℂ) (gammaOf ρ₀)) ^ m₁ *
      paperFT h z = paperFT (tiltedPhi θ) z)
    (hne₀ : paperFT h (gammaOf ρ₀) ≠ 0) (hne₁ : paperFT h ((starRingEnd ℂ) (gammaOf ρ₀)) ≠ 0) :
    ∀ z ∈ closedBall (ρ₀.im : ℂ) (3 * δ / 4), dividedKernelFloor θ ρ₀.im (δ / 2) ≤ ‖paperFT h z‖ := by
  set γ₀ := gammaOf ρ₀ with hγ₀def
  set γ₁ := (starRingEnd ℂ) γ₀ with hγ₁def
  set t₀ := ρ₀.im with ht₀
  have hγ₀re : γ₀.re = t₀ := WeilEF.gammaOf_re ρ₀
  have hγ₀im : γ₀.im = 1 / 2 - ρ₀.re := WeilEF.gammaOf_im ρ₀
  have hγ₁refl : γ₁ = gammaOf (Zeta23.reflect ρ₀) := by rw [hγ₁def, hγ₀def, gammaOf_reflect']
  have hdist : ∀ z : ℂ, ‖z - (t₀ : ℂ)‖ ≤ 3 * δ / 4 → ‖z - γ₀‖ ≤ 1 ∧ ‖z - γ₁‖ ≤ 1 := by
    intro z hz
    have hγt : ‖(t₀ : ℂ) - γ₀‖ ≤ δ / 2 := by
      have e : (t₀ : ℂ) - γ₀ = -(((γ₀.im : ℝ) : ℂ) * I) := by
        apply Complex.ext <;> simp [hγ₀re]
      rw [e, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        hγ₀im, abs_sub_comm]; exact hdep
    have hγt₁ : ‖(t₀ : ℂ) - γ₁‖ ≤ δ / 2 := by
      have e : (t₀ : ℂ) - γ₁ = (starRingEnd ℂ) ((t₀ : ℂ) - γ₀) := by simp [hγ₁def]
      rw [e, Complex.norm_conj]; exact hγt
    constructor
    · calc ‖z - γ₀‖ = ‖(z - t₀) + ((t₀ : ℂ) - γ₀)‖ := by ring_nf
        _ ≤ ‖z - t₀‖ + ‖(t₀ : ℂ) - γ₀‖ := norm_add_le _ _
        _ ≤ 1 := by linarith
    · calc ‖z - γ₁‖ = ‖(z - t₀) + ((t₀ : ℂ) - γ₁)‖ := by ring_nf
        _ ≤ ‖z - t₀‖ + ‖(t₀ : ℂ) - γ₁‖ := norm_add_le _ _
        _ ≤ 1 := by linarith
  have hball_im : ∀ z : ℂ, ‖z - (t₀ : ℂ)‖ ≤ 3 * δ / 4 → |z.im| < 1 / 2 := by
    intro z hz
    have := Complex.abs_im_le_norm (z - (t₀ : ℂ))
    simp at this; linarith
  have hball_re : ∀ z : ℂ, ‖z - (t₀ : ℂ)‖ ≤ 3 * δ / 4 → |z.re - t₀| < δ := by
    intro z hz
    have := Complex.abs_re_le_norm (z - (t₀ : ℂ))
    simp at this; linarith
  have hne : ∀ z : ℂ, ‖z - (t₀ : ℂ)‖ ≤ 3 * δ / 4 → paperFT h z ≠ 0 := by
    intro z hz
    by_cases h0 : z = γ₀
    · rw [h0]; exact hne₀
    by_cases h1 : z = γ₁
    · rw [h1]; exact hne₁
    intro hz0
    have hp := hprod z
    rw [hz0, mul_zero, paperFT_tiltedPhi hθ0 hθ (hball_im z hz).le] at hp
    have hΞ := riemannPhiTransform_ne_zero_near_pair hsep (hball_re z hz) (hball_im z hz) h0
      (by rw [← hγ₁refl]; exact h1)
    exact (mul_ne_zero (Complex.exp_ne_zero _) hΞ) hp.symm
  set mV := dividedKernelFloor θ t₀ (δ / 2) with hmVdef
  have hmV0 : 0 < mV := dividedKernelFloor_pos (by linarith)
  have hdiff := hh.differentiable_paperFT
  have hcircle : ∀ z ∈ frontier (ball (t₀ : ℂ) (3 * δ / 4)), ‖(paperFT h z)⁻¹‖ ≤ mV⁻¹ := by
    intro z hz
    rw [frontier_ball _ (by positivity : 3 * δ / 4 ≠ 0)] at hz
    have hzn : ‖z - (t₀ : ℂ)‖ = 3 * δ / 4 := by simpa [dist_eq_norm] using hz
    have hfl := pair_circle_floor hθ0 hγ hδ hδ2 hsep hdep hzn
    obtain ⟨hd0, hd1⟩ := hdist z hzn.le
    have hp := hprod z
    rw [paperFT_tiltedPhi hθ0 hθ (hball_im z hzn.le).le] at hp
    have hnorm : Real.exp (θ * z.re) * ‖riemannPhiTransform (1 / 2 + I * z)‖ =
        ‖z - γ₀‖ ^ m₀ * ‖z - γ₁‖ ^ m₁ * ‖paperFT h z‖ := by
      have := congrArg norm hp
      rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_mul, Complex.norm_exp] at this
      have e : (z * (θ : ℂ)).re = θ * z.re := by simp [Complex.mul_re]; ring
      rw [e] at this
      exact this.symm
    have hle : ‖z - γ₀‖ ^ m₀ * ‖z - γ₁‖ ^ m₁ * ‖paperFT h z‖ ≤ ‖paperFT h z‖ := by
      have h1 : ‖z - γ₀‖ ^ m₀ ≤ 1 := pow_le_one₀ (norm_nonneg _) hd0
      have h2 : ‖z - γ₁‖ ^ m₁ ≤ 1 := pow_le_one₀ (norm_nonneg _) hd1
      have h3 : ‖z - γ₀‖ ^ m₀ * ‖z - γ₁‖ ^ m₁ ≤ 1 := by
        calc ‖z - γ₀‖ ^ m₀ * ‖z - γ₁‖ ^ m₁ ≤ 1 * 1 :=
              mul_le_mul h1 h2 (by positivity) zero_le_one
          _ = 1 := one_mul 1
      calc ‖z - γ₀‖ ^ m₀ * ‖z - γ₁‖ ^ m₁ * ‖paperFT h z‖ ≤ 1 * ‖paperFT h z‖ :=
            mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = ‖paperFT h z‖ := one_mul _
    have hlow : mV ≤ ‖paperFT h z‖ := by
      calc mV ≤ Real.exp (θ * z.re) * ‖riemannPhiTransform (1 / 2 + I * z)‖ := hfl
        _ = _ := hnorm
        _ ≤ ‖paperFT h z‖ := hle
    rw [norm_inv]
    exact inv_anti₀ hmV0 hlow
  have hdcc : DiffContOnCl ℂ (fun z => (paperFT h z)⁻¹) (ball (t₀ : ℂ) (3 * δ / 4)) := by
    have hdo : DifferentiableOn ℂ (fun z => (paperFT h z)⁻¹) (closedBall (t₀ : ℂ) (3 * δ / 4)) := by
      intro z hz
      have hz' : ‖z - (t₀ : ℂ)‖ ≤ 3 * δ / 4 := by simpa [dist_eq_norm] using hz
      exact ((hdiff z).inv (hne z hz')).differentiableWithinAt
    exact ⟨hdo.mono ball_subset_closedBall, hdo.continuousOn.mono closure_ball_subset_closedBall⟩
  intro z hz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdcc hcircle
    (by rwa [closure_ball _ (by positivity : 3 * δ / 4 ≠ 0)])
  rw [norm_inv] at hmax
  have hz' : ‖z - (t₀ : ℂ)‖ ≤ 3 * δ / 4 := by simpa [dist_eq_norm] using hz
  have hpos : 0 < ‖paperFT h z‖ := norm_pos_iff.mpr (hne z hz')
  rwa [inv_le_inv₀ hpos hmV0] at hmax

/-- **The divided kernel of an off-line zero.** For a nontrivial zero `ρ₀` off the critical line,
of multiplicity `m`, with `t₀ ≥ 8`, ordinate separation `δ ≤ 1/2` from all zeros other than `ρ₀` and
its mirror, and `|β₀ - 1/2| ≤ δ/2`, there is a super-exponentially decaying `h` with
`(z - γ₀)^m (z - γ̄₀)^m ĥ = Φ̂_θ`, `|ĥ(γ₀)|, |ĥ(γ̄₀)| ≥ m_V(θ, t₀, δ/2)`, and weighted tails
`≤ 2^{2m}` times those of `Φ_θ` with weight shifted by `3m`. -/
theorem offLine_pairKernel_package {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hoff : ρ₀.re ≠ 1 / 2) (hγ : 8 ≤ ρ₀.im) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ →
      δ ≤ |ρ.im - ρ₀.im|) (hdep : |ρ₀.re - 1 / 2| ≤ δ / 2) :
    ∃ h : ℝ → ℂ, SuperExpDecay h ∧
      (∀ z, (z - gammaOf ρ₀) ^ zetaZeroConfig.mult ρ₀ *
        (z - (starRingEnd ℂ) (gammaOf ρ₀)) ^ zetaZeroConfig.mult ρ₀ * paperFT h z =
          paperFT (tiltedPhi θ) z) ∧
      dividedKernelFloor θ ρ₀.im (δ / 2) ≤ ‖paperFT h (gammaOf ρ₀)‖ ∧
      dividedKernelFloor θ ρ₀.im (δ / 2) ≤ ‖paperFT h ((starRingEnd ℂ) (gammaOf ρ₀))‖ ∧
      ∀ c X : ℝ, 0 ≤ c → expTail h c X ≤ 2 ^ (2 * zetaZeroConfig.mult ρ₀) *
        expTail (tiltedPhi θ) (c + 3 / 2 * ((2 * zetaZeroConfig.mult ρ₀ : ℕ) : ℝ)) X := by
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  set m := zetaZeroConfig.mult ρ₀ with hm
  set γ₀ := gammaOf ρ₀ with hγ₀def
  have hγ₀im : γ₀.im = 1 / 2 - ρ₀.re := WeilEF.gammaOf_im ρ₀
  have hγ₀re : γ₀.re = ρ₀.im := WeilEF.gammaOf_re ρ₀
  have him : γ₀.im ≠ 0 := by rw [hγ₀im]; intro h; exact hoff (by linarith)
  have him2 : |γ₀.im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt ⟨hnt.2.1, hnt.2.2⟩).le
  obtain ⟨v₀, hv₀, hv₀0, hloc₀⟩ := exists_tiltedPhi_local_factor_gammaOf hθ0 hθ hρ₀
  have hmem₁ := zetaZeroConfig.reflect_mem ρ₀ hρ₀
  obtain ⟨v₁, hv₁, hv₁0, hloc₁⟩ := exists_tiltedPhi_local_factor_gammaOf hθ0 hθ hmem₁
  have hrefl : gammaOf (Zeta23.reflect ρ₀) = (starRingEnd ℂ) γ₀ := gammaOf_reflect' ρ₀
  have hmr : zetaZeroConfig.mult (Zeta23.reflect ρ₀) = m := zetaZeroConfig.mult_reflect ρ₀ hρ₀
  rw [hrefl, hmr] at hloc₁
  rw [hrefl] at hv₁ hv₁0
  obtain ⟨hK, hprod, hne₀, hne₁, htail⟩ :=
    pairKernel_spec hθ0 hθ him him2 hv₀ hv₀0 hloc₀ hv₁ hv₁0 hloc₁
  have hlow := norm_divided_pair_ge hθ0 hθ hγ hδ hδ2 hsep hdep hK hprod hne₀ hne₁
  have hin₀ : γ₀ ∈ closedBall (ρ₀.im : ℂ) (3 * δ / 4) := by
    rw [mem_closedBall, dist_eq_norm]
    have e : γ₀ - (ρ₀.im : ℂ) = ((γ₀.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hγ₀re]
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, hγ₀im,
      abs_sub_comm]
    linarith
  have hin₁ : (starRingEnd ℂ) γ₀ ∈ closedBall (ρ₀.im : ℂ) (3 * δ / 4) := by
    rw [mem_closedBall, dist_eq_norm] at hin₀ ⊢
    have e : (starRingEnd ℂ) γ₀ - (ρ₀.im : ℂ) = (starRingEnd ℂ) (γ₀ - (ρ₀.im : ℂ)) := by simp
    rw [e, Complex.norm_conj]; exact hin₀
  refine ⟨pairKernel θ γ₀ m m, hK, hprod, hlow _ hin₀, hlow _ hin₁, fun c X hc => ?_⟩
  have := htail c X hc
  rw [show m + m = 2 * m by ring] at this
  exact this

end

end RHTower
