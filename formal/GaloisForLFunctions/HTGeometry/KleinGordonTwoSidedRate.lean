import GaloisForLFunctions.HTGeometry.KleinGordonEnergyExponent

/-!
# The estimate in both directions of time

The card's opening estimate is stated with `|t|`; the spectral sharpening of statement 414 runs
forwards only. The reflection of statement 355 supplies the other direction — the state at `−t` for `W`
is the state at `+t` for the reflected background, up to the velocity flip, which is an isometry — so
the backward rate is the reflected background's forward rate.

When the background is even in time the two coincide, and the bound closes up:

`‖v(t)‖ ≤ e^{μ|t|}·‖v(0)‖·e^{bT}`   for all `|t|` large,   `μ = log(r+ε)/T`,

which is the shape the card began with, at the rate the clock actually has.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Flipping the velocity of a datum does not change its energy norm. -/
theorem norm_kgPair_neg_snd (g h : Lp ℂ 2 (volume : Measure E)) :
    ‖kgPair E (g, -h)‖ = ‖kgPair E (g, h)‖ := by
  have h1 : ‖kgPair E (g, -h)‖ ^ 2 = ‖g‖ ^ 2 + ‖h‖ ^ 2 := by
    rw [norm_kgPair_sq, norm_neg]
  have h2 : ‖kgPair E (g, h)‖ ^ 2 = ‖g‖ ^ 2 + ‖h‖ ^ 2 := norm_kgPair_sq g h
  have hn1 : (0 : ℝ) ≤ ‖kgPair E (g, -h)‖ := norm_nonneg _
  have hn2 : (0 : ℝ) ≤ ‖kgPair E (g, h)‖ := norm_nonneg _
  nlinarith [h1, h2, hn1, hn2]

section TwoSided

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The backward rate is the reflected background's forward rate.** -/
theorem eventually_norm_kgFieldStateT_neg_le_exp_rate (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, (fun ρ : ℝ => W (-ρ)) (r + T) = (fun ρ : ℝ => W (-ρ)) r) (hT : 0 < T)
    {ε : ℝ} (hε : 0 < ε)
    (hq : 1 ≤ (spectralRadius ℂ (kgMonodromy (fun r : ℝ => W (-r)) b hb0
      (norm_neg_background_le hWb) (continuous_neg_background_apply hWs) T)).toReal + ε)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∀ᶠ t : ℝ in atTop, ‖kgFieldStateT W g h (-t)‖
      ≤ Real.exp (Real.log ((spectralRadius ℂ (kgMonodromy (fun r : ℝ => W (-r)) b hb0
            (norm_neg_background_le hWb) (continuous_neg_background_apply hWs) T)).toReal + ε)
          / T * t) * ‖kgPair E (g, h)‖ * Real.exp (b * T) := by
  have hfwd := eventually_norm_kgFieldStateT_le_exp_rate hb0 (norm_neg_background_le hWb)
    (continuous_neg_background_apply hWs) hper hT hε hq g (-h)
  filter_upwards [hfwd] with t ht
  rw [norm_kgFieldStateT_neg hb0 hWb hWs g h t]
  rw [norm_kgPair_neg_snd] at ht
  exact ht

set_option maxHeartbeats 1000000 in
/-- **The two-sided estimate at the true rate**, for a background even in time. -/
theorem exists_bound_norm_kgFieldStateT_abs (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hsym : ∀ r : ℝ, W (-r) = W r) (hT : 0 < T)
    {ε : ℝ} (hε : 0 < ε)
    (hq : 1 ≤ (spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| →
      ‖kgFieldStateT W g h t‖
        ≤ Real.exp (Real.log ((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε)
            / T * |t|) * ‖kgPair E (g, h)‖ * Real.exp (b * T) := by
  have hfun : (fun r : ℝ => W (-r)) = W := funext hsym
  have hmono : kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
      (continuous_neg_background_apply hWs) T = kgMonodromy W b hb0 hWb hWs T :=
    kgMonodromy_congr hfun hb0 (norm_neg_background_le hWb)
      (continuous_neg_background_apply hWs) hWb hWs T
  have hperV : ∀ r : ℝ, (fun ρ : ℝ => W (-ρ)) (r + T) = (fun ρ : ℝ => W (-ρ)) r := by
    intro r
    show W (-(r + T)) = W (-r)
    rw [hsym, hsym, hper]
  have hqV : 1 ≤ (spectralRadius ℂ (kgMonodromy (fun r : ℝ => W (-r)) b hb0
      (norm_neg_background_le hWb) (continuous_neg_background_apply hWs) T)).toReal + ε := by
    rw [hmono]
    exact hq
  have hfwd := eventually_norm_kgFieldStateT_le_exp_rate hb0 hWb hWs hper hT hε hq g h
  have hbwd := eventually_norm_kgFieldStateT_neg_le_exp_rate hb0 hWb hWs hperV hT hε hqV g h
  rw [hmono] at hbwd
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.mp hfwd
  obtain ⟨t₂, ht₂⟩ := eventually_atTop.mp hbwd
  refine ⟨max t₁ t₂, fun t ht => ?_⟩
  rcases le_total (0 : ℝ) t with hpos | hneg
  · have habs : |t| = t := abs_of_nonneg hpos
    rw [habs] at ht ⊢
    exact ht₁ t (le_trans (le_max_left _ _) ht)
  · have habs : |t| = -t := abs_of_nonpos hneg
    rw [habs] at ht ⊢
    have hmem := ht₂ (-t) (le_trans (le_max_right _ _) ht)
    rwa [neg_neg] at hmem

end TwoSided

end GaloisForLFunctions.HTGeometry
