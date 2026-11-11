import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheChiWeightJetsHaveTheirConductorLimits

/-!
# Uniform conductor jets on moving height intervals

If both endpoint conductor logarithms have the same normalized limit,
every height between them has that limit. Selecting a hypothetical bad
height then contradicts the already proved moving-height jet limit.
This supplies the uniform estimate required before integrating a taper.
-/

open Complex Filter Metric Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem eventually_uniform_of_selections
    {ι α β : Type*} [PseudoMetricSpace β] {l : Filter ι}
    {S : ι → Set α} {a : ι → α} (ha : ∀ᶠ i in l, a i ∈ S i)
    {f : ι → α → β} {b : β}
    (h : ∀ x : ι → α, (∀ᶠ i in l, x i ∈ S i) →
      Tendsto (fun i => f i (x i)) l (𝓝 b)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x ∈ S i, dist (f i x) b < ε := by
  classical
  let bad (i : ι) : Prop := ∃ x ∈ S i, ε ≤ dist (f i x) b
  let pick (i : ι) : α := if hi : bad i then Classical.choose hi else a i
  have hpick : ∀ᶠ i in l, pick i ∈ S i := by
    filter_upwards [ha] with i hai
    by_cases hi : bad i
    · simpa only [pick, dif_pos hi] using (Classical.choose_spec hi).1
    · simpa only [pick, dif_neg hi] using hai
  have hclose := (h pick hpick).eventually (Metric.ball_mem_nhds b hε)
  filter_upwards [hclose] with i hi
  intro x hx
  by_contra hn
  have hb : bad i := ⟨x, hx, not_lt.mp hn⟩
  have hfar : ε ≤ dist (f i (pick i)) b := by
    simpa only [pick, dif_pos hb] using (Classical.choose_spec hb).2
  exact (not_lt_of_ge hfar) hi

/-- Every chi displacement jet converges uniformly between convergent conductor endpoints. -/
theorem eventually_uniform_scaled_holomorphicChiPair_jet
    {ι : Type*} {l : Filter ι} {L a b : ι → ℝ}
    (hL : Tendsto L l atTop) (ha : Tendsto a l atTop)
    (hab : ∀ᶠ i in l, a i ≤ b i) {τ : ℝ}
    (hτa : Tendsto (fun i => Real.log (a i / (2 * Real.pi)) / L i) l (𝓝 τ))
    (hτb : Tendsto (fun i => Real.log (b i / (2 * Real.pi)) / L i) l (𝓝 τ))
    {C : ι → ℂ} {C₀ : ℂ} (hC : Tendsto C l (𝓝 C₀))
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ t ∈ Icc (a i) (b i),
      ‖iteratedDeriv j (fun z => holomorphicChiPair (z / (L i : ℂ)) t) (C i) -
        (2 * (τ : ℂ)) ^ j * Complex.exp (2 * (τ : ℂ) * C₀)‖ < ε := by
  have hdefault : ∀ᶠ i in l, a i ∈ Icc (a i) (b i) := hab.mono (fun _ hi => ⟨le_rfl, hi⟩)
  have hselection (t : ι → ℝ) (ht : ∀ᶠ i in l, t i ∈ Icc (a i) (b i)) :
      Tendsto (fun i => iteratedDeriv j (fun z => holomorphicChiPair (z / (L i : ℂ)) (t i)) (C i)) l
        (𝓝 ((2 * (τ : ℂ)) ^ j * Complex.exp (2 * (τ : ℂ) * C₀))) := by
    have ht_top : Tendsto t l atTop := by
      apply Filter.tendsto_atTop.2
      intro M
      filter_upwards [ha.eventually_ge_atTop M, ht] with i hai hti
      exact hai.trans hti.1
    have hratio : Tendsto (fun i => Real.log (t i / (2 * Real.pi)) / L i) l (𝓝 τ) := by
      apply Metric.tendsto_nhds.2
      intro δ hδ
      filter_upwards [hτa.eventually (Metric.ball_mem_nhds τ hδ),
        hτb.eventually (Metric.ball_mem_nhds τ hδ), hL.eventually_gt_atTop 0,
        ha.eventually_gt_atTop 0, ht] with i hai hbi hLi ha0 hti
      have hleft : Real.log (a i / (2 * Real.pi)) / L i ≤
          Real.log (t i / (2 * Real.pi)) / L i :=
        div_le_div_of_nonneg_right
          (Real.log_le_log (by positivity)
            (div_le_div_of_nonneg_right hti.1 (by positivity))) hLi.le
      have ht0 : 0 < t i := ha0.trans_le hti.1
      have hright : Real.log (t i / (2 * Real.pi)) / L i ≤
          Real.log (b i / (2 * Real.pi)) / L i :=
        div_le_div_of_nonneg_right
          (Real.log_le_log (by positivity)
            (div_le_div_of_nonneg_right hti.2 (by positivity))) hLi.le
      change dist (Real.log (a i / (2 * Real.pi)) / L i) τ < δ at hai
      change dist (Real.log (b i / (2 * Real.pi)) / L i) τ < δ at hbi
      rw [Real.dist_eq] at hai hbi ⊢
      obtain ⟨hal, _⟩ := abs_lt.mp hai
      obtain ⟨_, hbu⟩ := abs_lt.mp hbi
      exact abs_lt.mpr ⟨by linarith only [hal, hleft], by linarith only [hbu, hright]⟩
    exact tendsto_scaled_holomorphicChiPair_jet hL ht_top hratio hC j
  simpa only [dist_eq_norm] using eventually_uniform_of_selections (β := ℂ)
    (f := fun i t => iteratedDeriv j (fun z => holomorphicChiPair (z / (L i : ℂ)) t) (C i))
    hdefault hselection hε

end GaloisForLFunctions.MultiscaleMollifiedZetaField
