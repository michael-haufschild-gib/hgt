import GaloisForLFunctions.RHTower.PaperZetaReturnFiniteWindows

/-! # An exact spectral reformulation of the native recurrence receiver

Choosing the Fourier frequency after the physical window cannot bypass the
return-density problem: the zero mode already dominates every frequency.
-/

namespace RHTower
noncomputable section
open Set MeasureTheory Filter Topology

theorem paperZetaReturnDensity_ge_iff (D : PaperZetaReturnDisc) (ε κ : ℝ)
    (T : {t : ℝ // 0 < t}) :
    κ ≤ paperZetaReturnDensity D ε T ↔
      ENNReal.ofReal (κ * T.val) ≤ volume (paperZetaReturnTimes D ε ∩ Icc 0 T.val) := by
  rw [ENNReal.ofReal_le_iff_le_toReal (paperZetaReturnTimes_window_ne_top D ε T),
    paperZetaReturnDensity, le_div_iff₀ T.property]
  rfl

/-- Frequencies may depend arbitrarily on the window length. -/
def PaperZetaReturnSpectralRecurrence : Prop :=
  ∀ (D : PaperZetaReturnDisc) (ε : ℝ), 0 < ε →
    ∃ κ > 0, ∃ᶠ T : ℝ in atTop, 0 < T ∧ ∃ k : ℤ, κ ≤ ‖paperZetaReturnCoeff D ε T k‖

theorem paperZetaReturnSpectralRecurrence_iff :
    PaperZetaReturnSpectralRecurrence ↔ ZetaDiscRecurrent := by
  constructor
  · intro h c r hr hstrip ε hε
    let D : PaperZetaReturnDisc := ⟨c, r, hr, hstrip⟩
    obtain ⟨κ, hκ, hf⟩ := h D ε hε
    refine ⟨κ, hκ, hf.mono ?_⟩
    rintro T ⟨hT, k, hk⟩
    exact (paperZetaReturnDensity_ge_iff D ε κ ⟨T, hT⟩).mp
      (hk.trans (paperZetaReturnCoeff_norm_le_density D ε ⟨T, hT⟩ k))
  · intro h D ε hε
    obtain ⟨κ, hκ, hf⟩ := h D.center D.radius D.radius_pos D.strip ε hε
    refine ⟨κ, hκ, (hf.and_eventually (eventually_gt_atTop 0)).mono ?_⟩
    rintro T ⟨hm, hT⟩
    refine ⟨hT, 0, ?_⟩
    rw [paperZetaReturnCoeff_zero_norm D ε ⟨T, hT⟩]
    exact (paperZetaReturnDensity_ge_iff D ε κ ⟨T, hT⟩).mpr hm

/-- The proven native receiver accepts the spectral criterion without new assumptions. -/
theorem paperZetaReturnSpectralRecurrence_implies_RH :
    PaperZetaReturnSpectralRecurrence → RiemannHypothesis :=
  fun h => riemannHypothesis_of_zetaDiscRecurrent (paperZetaReturnSpectralRecurrence_iff.mp h)

/-- An off-line zero supplies a single return profile whose entire frequency array decays. -/
theorem paperZetaReturn_RH_or_uniform_frequency_decay :
    RiemannHypothesis ∨
      ∃ (D : PaperZetaReturnDisc) (ε : ℝ), 0 < ε ∧
        ∀ δ > 0, ∀ᶠ T : ℝ in atTop, ∀ k : ℤ, ‖paperZetaReturnCoeff D ε T k‖ ≤ δ := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip] at hRH
    push Not at hRH
    obtain ⟨ρ, hρ1, hρ2, hρ0⟩ := hRH
    obtain ⟨r, hr, hstrip, ε, hε, hd⟩ := exists_zetaSelfReturn_density_zero hρ0 hρ1 hρ2
    let D : PaperZetaReturnDisc := ⟨ρ, r, hr, hstrip⟩
    refine ⟨D, ε, hε, fun δ hδ => ?_⟩
    filter_upwards [hd δ hδ, eventually_gt_atTop (0 : ℝ)] with T hvol hT
    intro k
    apply (paperZetaReturnCoeff_norm_le_density D ε ⟨T, hT⟩ k).trans
    apply (div_le_iff₀ hT).mpr
    exact (ENNReal.le_ofReal_iff_toReal_le
      (paperZetaReturnTimes_window_ne_top D ε T) (mul_nonneg hδ.le hT.le)).mp hvol

/-- The same profile defeats every moving frequency selection simultaneously. -/
theorem paperZetaReturn_RH_or_moving_frequency_decay :
    RiemannHypothesis ∨
      ∃ (D : PaperZetaReturnDisc) (ε : ℝ), 0 < ε ∧
        ∀ k : ℝ → ℤ, Tendsto (fun T => paperZetaReturnCoeff D ε T (k T)) atTop (𝓝 0) := by
  rcases paperZetaReturn_RH_or_uniform_frequency_decay with h | ⟨D, ε, hε, hd⟩
  · exact Or.inl h
  · right
    refine ⟨D, ε, hε, fun k => ?_⟩
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hd (δ / 2) (by positivity))
    exact ⟨T₀, fun T hT => by
      simpa only [dist_zero_right] using (hT₀ T hT (k T)).trans_lt (by linarith)⟩

/-- Strict positivity at every finite window coexists with a vanishing entire spectrum
in the alternative to RH. Local positivity alone cannot pay the recurrence estimate. -/
theorem paperZetaReturn_RH_or_positive_vanishing_zero_mode :
    RiemannHypothesis ∨
      ∃ (D : PaperZetaReturnDisc) (ε : {e : ℝ // 0 < e}),
        (∀ T : {t : ℝ // 0 < t}, 0 < ‖paperZetaReturnCoeff D ε T 0‖) ∧
        (∀ k : ℝ → ℤ, Tendsto (fun T => paperZetaReturnCoeff D ε T (k T)) atTop (𝓝 0)) := by
  rcases paperZetaReturn_RH_or_moving_frequency_decay with h | ⟨D, ε, hε, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨D, ⟨ε, hε⟩, paperZetaReturnCoeff_zero_norm_pos D ⟨ε, hε⟩, hd⟩

end
end RHTower
