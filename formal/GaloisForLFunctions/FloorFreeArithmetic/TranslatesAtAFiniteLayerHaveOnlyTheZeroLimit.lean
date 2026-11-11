import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMissingInputOfTransport

/-!
# Translates at a finite layer have only the zero limit

Suppose `ζ` has finitely many zeros right of `Re s = σ`, and let `ρ` be one of them. Along a
phase return `τ_j → ∞` (`n^{-iτ_j} → 1` for every `n`) the translates `ζ(· + iτ_j)` converge to
`ζ` on `Re s > 1`. On a connected open set `U` of the upper half-plane joining `ρ` to
`Re s > 1` they are not locally bounded: a bounded return would replicate the zero.

This file decides which normalizations `c_j ζ(· + iτ_j)` are locally bounded on `U`: only those
with `c_j → 0`.

* `forall_eventually_exists_lt_norm_translate`: the supremum of `|ζ(· + iτ_j)|` over `U` tends
  to infinity along every phase return. It is a limit: every subsequence of a phase return is a
  phase return.
* `tendsto_normalization_zero`: a locally bounded normalization has `c_j → 0`.
* `eqOn_zero_of_tendstoLocallyUniformlyOn_normalized`: every locally uniform limit of
  normalized translates on `U` vanishes identically.
* `asymptoticAbscissaLaw_of_boundedNormalizedReturns`: a bounded normalization that does not
  tend to zero, at every zero right of the critical line, gives the asymptotic abscissa law.

Hurwitz's argument therefore has no nonzero limit to act on: replication of a zero of a finite
layer cannot come from a normal family of translates.
-/

open Complex Filter Metric Set Topology

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open ArithmeticAuxiliaryDynamics

/-- A subsequence of a phase return is a phase return. -/
theorem isPhaseReturn_comp {τ : ℕ → ℝ} (h : IsPhaseReturn τ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsPhaseReturn (τ ∘ φ) :=
  ⟨fun j => h.nonneg (φ j), h.tendsto.comp hφ.tendsto_atTop,
    fun n => (h.phase n).comp hφ.tendsto_atTop⟩

/-- Translates bounded near each point for all late indices are locally bounded for all
indices: a single translate is continuous on a closed ball of the upper half-plane. -/
theorem translatesBoundedOn_of_eventually {τ : ℕ → ℝ} (hτ : ∀ j, 0 ≤ τ j) {U : Set ℂ}
    (hUim : ∀ z ∈ U, 0 < z.im)
    (h : ∀ z ∈ U, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ U ∧ ∃ C : ℝ, ∀ᶠ j in atTop,
      ∀ w ∈ ball z R, ‖riemannZeta (w + (τ j : ℂ) * I)‖ ≤ C) :
    TranslatesBoundedOn τ U := by
  intro z hz
  obtain ⟨R, hR, hsub, C, hC⟩ := h z hz
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  have hcl : closedBall z (R / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hR)).trans hsub
  have hone : ∀ j, ∃ B : ℝ, ∀ w ∈ closedBall z (R / 2),
      ‖riemannZeta (w + (τ j : ℂ) * I)‖ ≤ B := by
    intro j
    refine (isCompact_closedBall z (R / 2)).exists_bound_of_continuousOn ?_
    intro w hw
    have hne : w + (τ j : ℂ) * I ≠ 1 := by
      intro h1
      have him : (w + (τ j : ℂ) * I).im = w.im + τ j := by simp
      rw [h1, one_im] at him
      linarith only [him, hUim w (hcl hw), hτ j]
    exact ((differentiableAt_riemannZeta hne).comp w
      (differentiableAt_id.add_const _)).continuousAt.continuousWithinAt
  choose B hB using hone
  refine ⟨R / 2, half_pos hR, ball_subset_closedBall.trans hcl,
    |C| + ∑ j ∈ Finset.range N, |B j|, fun j w hw => ?_⟩
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, |B i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hj : N ≤ j
  · have h1 := hN j hj w (ball_subset_ball (half_le_self hR.le) hw)
    linarith only [h1, le_abs_self C, hsum]
  · have h1 := hB j w (ball_subset_closedBall hw)
    have h2 : |B j| ≤ ∑ i ∈ Finset.range N, |B i| :=
      Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (not_le.mp hj))
    linarith only [h1, h2, le_abs_self (B j), abs_nonneg C]

/-- Local boundedness, for late indices, of the normalized translates `c_j ζ(· + iτ_j)`. -/
def NormalizedTranslatesBoundedOn (c : ℕ → ℂ) (τ : ℕ → ℝ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ U ∧ ∃ C : ℝ, ∀ᶠ j in atTop,
    ∀ w ∈ ball z R, ‖c j * riemannZeta (w + (τ j : ℂ) * I)‖ ≤ C

section FiniteLayer

variable {σ : ℝ} {ρ s₀ : ℂ} {τ : ℕ → ℝ} {U : Set ℂ}

/-- **The translates blow up along every phase return.** With finitely many zeros right of
`Re s = σ`, on a connected open set `U` of the upper half-plane joining one of them to
`Re s > 1`, the supremum of `|ζ(· + iτ_j)|` over `U` tends to infinity. -/
theorem forall_eventually_exists_lt_norm_translate
    (hfin : {w : ℂ | riemannZeta w = 0 ∧ σ < w.re}.Finite) (hρ : riemannZeta ρ = 0)
    (hσ : σ < ρ.re) (hρ1 : ρ.re < 1) (h : IsPhaseReturn τ) (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hρU : ρ ∈ U) (C : ℝ) :
    ∀ᶠ j in atTop, ∃ w ∈ U, C < ‖riemannZeta (w + (τ j : ℂ) * I)‖ := by
  by_contra hnot
  rw [not_eventually] at hnot
  obtain ⟨φ, hφ, hφC⟩ := extraction_of_frequently_atTop hnot
  refine not_translatesBoundedOn_of_finite hfin hρ hσ hρ1 (isPhaseReturn_comp h hφ) hUo hUc
    hUim hs₀ hs₀1 hρU fun z hz => ?_
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hUo z hz
  refine ⟨R, hR, hsub, C, fun j w hw => ?_⟩
  have hj := hφC j
  push Not at hj
  exact hj w (hsub hw)

/-- **Only vanishing normalizations are bounded.** If the normalized translates
`c_j ζ(· + iτ_j)` are locally bounded on `U`, then `c_j → 0`. -/
theorem tendsto_normalization_zero
    (hfin : {w : ℂ | riemannZeta w = 0 ∧ σ < w.re}.Finite) (hρ : riemannZeta ρ = 0)
    (hσ : σ < ρ.re) (hρ1 : ρ.re < 1) (h : IsPhaseReturn τ) (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hρU : ρ ∈ U) {c : ℕ → ℂ} (hbd : NormalizedTranslatesBoundedOn c τ U) :
    Tendsto c atTop (𝓝 0) := by
  by_contra hnot
  -- a subsequence of the normalization stays away from zero
  rw [Metric.tendsto_nhds] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfreq⟩ := hnot
  obtain ⟨φ, hφ, hφε⟩ := extraction_of_frequently_atTop hfreq
  -- along it the translates themselves are bounded
  refine not_translatesBoundedOn_of_finite hfin hρ hσ hρ1 (isPhaseReturn_comp h hφ) hUo hUc
    hUim hs₀ hs₀1 hρU
    (translatesBoundedOn_of_eventually (fun j => h.nonneg (φ j)) hUim fun z hz => ?_)
  obtain ⟨R, hR, hsub, C, hC⟩ := hbd z hz
  refine ⟨R, hR, hsub, C / ε, (hφ.tendsto_atTop.eventually hC).mono fun j hj w hw => ?_⟩
  have h1 := hj w hw
  rw [norm_mul] at h1
  have h2 : ε ≤ ‖c (φ j)‖ := by
    have := hφε j
    rwa [dist_zero_right] at this
  have h3 : ε * ‖riemannZeta (w + (τ (φ j) : ℂ) * I)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h1
  exact (le_div_iff₀' hε).mpr h3

/-- **Every limit of normalized translates vanishes.** If `c_j ζ(· + iτ_j)` converges locally
uniformly on `U`, its limit is identically zero there. -/
theorem eqOn_zero_of_tendstoLocallyUniformlyOn_normalized
    (hfin : {w : ℂ | riemannZeta w = 0 ∧ σ < w.re}.Finite) (hρ : riemannZeta ρ = 0)
    (hσ : σ < ρ.re) (hρ1 : ρ.re < 1) (h : IsPhaseReturn τ) (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hρU : ρ ∈ U) {c : ℕ → ℂ} {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun j s => c j * riemannZeta (s + (τ j : ℂ) * I)) g
      atTop U) :
    EqOn g 0 U := by
  have hne : ∀ j, ∀ z ∈ U, z + (τ j : ℂ) * I ≠ 1 := by
    intro j z hz h1
    have him : (z + (τ j : ℂ) * I).im = z.im + τ j := by simp
    rw [h1, one_im] at him
    linarith only [him, hUim z hz, h.nonneg j]
  have hdiff : ∀ j, DifferentiableOn ℂ (fun s => c j * riemannZeta (s + (τ j : ℂ) * I)) U := by
    intro j z hz
    exact (((differentiableAt_riemannZeta (hne j z hz)).comp z
      (differentiableAt_id.add_const _)).const_mul (c j)).differentiableWithinAt
  have hgd : DifferentiableOn ℂ g U := hconv.differentiableOn (Eventually.of_forall hdiff) hUo
  -- a convergent sequence is locally bounded
  have hbd : NormalizedTranslatesBoundedOn c τ U := by
    intro z hz
    have hcont : Tendsto (fun w => ‖g w‖) (𝓝 z) (𝓝 ‖g z‖) :=
      (hgd.continuousOn.continuousAt (hUo.mem_nhds hz)).norm
    have hgz : ∀ᶠ w in 𝓝 z, ‖g w‖ < ‖g z‖ + 1 := hcont.eventually (gt_mem_nhds (lt_add_one _))
    obtain ⟨t, ht, hev⟩ := hconv {p | dist p.1 p.2 < 1} (dist_mem_uniformity one_pos) z hz
    rw [hUo.nhdsWithin_eq hz] at ht
    obtain ⟨R, hR, hball⟩ :=
      Metric.mem_nhds_iff.mp (inter_mem (inter_mem ht hgz) (hUo.mem_nhds hz))
    refine ⟨R, hR, fun w hw => (hball hw).2, ‖g z‖ + 2, hev.mono fun j hj w hw => ?_⟩
    have h1 : dist (g w) (c j * riemannZeta (w + (τ j : ℂ) * I)) < 1 := hj w (hball hw).1.1
    have h2 : ‖g w‖ < ‖g z‖ + 1 := (hball hw).1.2
    have h3 : ‖c j * riemannZeta (w + (τ j : ℂ) * I)‖ ≤
        ‖g w‖ + dist (g w) (c j * riemannZeta (w + (τ j : ℂ) * I)) := by
      rw [dist_eq_norm]
      have h4 := norm_sub_le (g w) (g w - c j * riemannZeta (w + (τ j : ℂ) * I))
      rwa [sub_sub_cancel] at h4
    linarith only [h1, h2, h3]
  have hc0 := tendsto_normalization_zero hfin hρ hσ hρ1 h hUo hUc hUim hs₀ hs₀1 hρU hbd
  -- the limit vanishes right of `Re s = 1`, where the translates converge to `ζ`
  have hYo : IsOpen {z | z ∈ U ∧ 1 < z.re} := hUo.inter (isOpen_lt continuous_const continuous_re)
  have hg0 : ∀ z ∈ {z | z ∈ U ∧ 1 < z.re}, g z = 0 := by
    intro z hz
    have hlim := hc0.mul (h.tendsto_of_one_lt_re hz.2)
    rw [zero_mul] at hlim
    exact tendsto_nhds_unique (hconv.tendsto_at hz.1) hlim
  have hev : g =ᶠ[𝓝 s₀] 0 := Filter.eventually_of_mem (hYo.mem_nhds ⟨hs₀, hs₀1⟩) hg0
  exact (hgd.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hs₀ hev

end FiniteLayer

/-- **A nonvanishing bounded normalization gives the asymptotic abscissa law.** Suppose every
zero right of the critical line in the upper half-plane has a phase return, a connected domain
joining it to `Re s > 1` and a normalization, not tending to zero, whose normalized translates
are locally bounded on the domain. Then finitely many zeros right of `½ + h` forces none. -/
theorem asymptoticAbscissaLaw_of_boundedNormalizedReturns
    (hB : ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → 0 < ρ.im →
      ∃ (τ : ℕ → ℝ) (c : ℕ → ℂ) (U : Set ℂ) (s₀ : ℂ), IsPhaseReturn τ ∧ IsOpen U ∧
        IsPreconnected U ∧ (∀ z ∈ U, 0 < z.im) ∧ ρ ∈ U ∧ s₀ ∈ U ∧ 1 < s₀.re ∧
        NormalizedTranslatesBoundedOn c τ U ∧ ¬ Tendsto c atTop (𝓝 0)) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_infinite_zeros fun ρ hρ hρ12 hρ1 hρim r hr hfin => ?_
  obtain ⟨τ, c, U, s₀, hτ, hUo, hUc, hUim, hρU, hs₀, hs₀1, hbd, hc⟩ := hB ρ hρ hρ12 hρ1 hρim
  exact hc (tendsto_normalization_zero hfin hρ (by linarith only [hr]) hρ1 hτ hUo hUc hUim hs₀
    hs₀1 hρU hbd)

end GaloisForLFunctions.FloorFreeArithmetic
