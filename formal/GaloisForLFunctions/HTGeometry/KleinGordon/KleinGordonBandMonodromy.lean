import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFloquetInhabited

/-!
# Deciding stability on a band

The Floquet criterion is about the powers of the monodromy of the original equation, which is not an
object one can compute with. The band models are: there the Cauchy problem is a genuine strong problem
(statement 281), the frequency is bounded, and everything is a bounded operator with a cut-off.

This file connects the two. The band compression of a periodic background is periodic, so it has a
monodromy of its own, and the state estimate of statement 269 — applied with the *same* datum for both
backgrounds — bounds the difference of the two monodromies by the accumulated discrepancy over one
period, which vanishes. So `M_R → M` strongly, and since the `M_R` are bounded uniformly by `e^{b|T|}`,
so does every power: `M_Rⁿ → Mⁿ` strongly, for each fixed `n`.

The consequence is a transfer principle: **a bound on the powers of the band monodromies, uniform in
the cut-off, is a bound on the powers of the true monodromy** — so the stability of a periodically
driven clock can be decided on the band models.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandMonodromy

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- The band compression of a periodic background is periodic. -/
theorem periodic_kgBandOpT (hper : ∀ r : ℝ, W (r + T) = W r) (R : ℝ) (r : ℝ) :
    kgBandOpT W R (r + T) = kgBandOpT W R r := by
  rw [kgBandOpT, kgBandOpT, hper]

/-- **The monodromy of the band model.** -/
def kgBandMonodromy (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (b : ℝ) (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (R T : ℝ) :
    KGEnergy E →L[ℂ] KGEnergy E :=
  kgMonodromy (kgBandOpT W R) b hb0 (norm_kgBandOpT_le hb0 hWb R)
    (continuous_kgBandOpT_apply hWs R) T

theorem kgBandMonodromy_apply (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (R : ℝ)
    (v : KGEnergy E) :
    kgBandMonodromy W b hb0 hWb hWs R T v = kgFieldStateT (kgBandOpT W R) v.fst v.snd T := rfl

theorem norm_kgBandMonodromy_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (R : ℝ) :
    ‖kgBandMonodromy W b hb0 hWb hWs R T‖ ≤ Real.exp (b * |T|) :=
  norm_kgMonodromy_le _ _ _

/-- **The band state differs from the true one by the accumulated discrepancy**, at the same
datum. -/
theorem norm_kgFieldStateT_band_sub_le_same (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (R : ℝ)
    (g h : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldStateT (kgBandOpT W R) g h t - kgFieldStateT W g h t‖
      ≤ (∫ s in (0 : ℝ)..t,
          ‖(kgBandOpT W R s - W s) (kgFieldMildT W (kgFreqInvOp g) h s)‖) * Real.exp (b * t) := by
  have hkey := norm_kgFieldStateT_sub_general_le hb0 (norm_kgBandOpT_le hb0 hWb R)
    (continuous_kgBandOpT_apply hWs R) hWb hWs g h g h ht
  have hzero : kgPair E ((g : Lp ℂ 2 (volume : Measure E)) - g, h - h) = 0 := by
    rw [sub_self, sub_self]
    exact map_zero (kgPair E)
  rw [hzero, norm_zero, zero_add] at hkey
  exact hkey

/-- **The band monodromies converge strongly to the monodromy.** -/
theorem tendsto_kgBandMonodromy (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (hT : 0 ≤ T)
    (v : KGEnergy E) :
    Tendsto (fun R : ℝ => kgBandMonodromy W b hb0 hWb hWs R T v) atTop
      (𝓝 (kgMonodromy W b hb0 hWb hWs T v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hcu : Continuous (kgFieldMildT W (kgFreqInvOp v.fst) v.snd) :=
    continuous_kgFieldMildT hb0 hWb hWs _ _
  have hle : ∀ R : ℝ,
      ‖kgBandMonodromy W b hb0 hWb hWs R T v - kgMonodromy W b hb0 hWb hWs T v‖
        ≤ (∫ s in (0 : ℝ)..T, ‖(kgBandOpT W R s - W s)
            (kgFieldMildT W (kgFreqInvOp v.fst) v.snd s)‖) * Real.exp (b * T) := fun R =>
    norm_kgFieldStateT_band_sub_le_same hb0 hWb hWs R v.fst v.snd hT
  have hdisc := tendsto_integral_kgBandOpT_sub hb0 hWb hWs
    (kgFieldMildT W (kgFreqInvOp v.fst) v.snd) hcu T
  have hsum : Tendsto (fun R : ℝ => (∫ s in (0 : ℝ)..T, ‖(kgBandOpT W R s - W s)
      (kgFieldMildT W (kgFreqInvOp v.fst) v.snd s)‖) * Real.exp (b * T)) atTop (𝓝 0) := by
    simpa using hdisc.mul_const (Real.exp (b * T))
  exact squeeze_zero (fun _ => norm_nonneg _) hle hsum

/-- **Every power of the band monodromy converges strongly to the corresponding power.** -/
theorem tendsto_kgBandMonodromy_pow (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (hT : 0 ≤ T)
    (n : ℕ) (v : KGEnergy E) :
    Tendsto (fun R : ℝ => (kgBandMonodromy W b hb0 hWb hWs R T ^ n) v) atTop
      (𝓝 ((kgMonodromy W b hb0 hWb hWs T ^ n) v)) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      have hstepB : ∀ R : ℝ, (kgBandMonodromy W b hb0 hWb hWs R T ^ (n + 1)) v
          = kgBandMonodromy W b hb0 hWb hWs R T
              ((kgBandMonodromy W b hb0 hWb hWs R T ^ n) v) := by
        intro R
        rw [pow_succ']
        rfl
      have hstepM : (kgMonodromy W b hb0 hWb hWs T ^ (n + 1)) v
          = kgMonodromy W b hb0 hWb hWs T ((kgMonodromy W b hb0 hWb hWs T ^ n) v) := by
        rw [pow_succ']
        rfl
      rw [hstepM]
      simp only [hstepB]
      rw [tendsto_iff_norm_sub_tendsto_zero]
      set z : ℝ → KGEnergy E := fun R => (kgBandMonodromy W b hb0 hWb hWs R T ^ n) v with hz
      set z₀ : KGEnergy E := (kgMonodromy W b hb0 hWb hWs T ^ n) v with hz₀
      have hzlim : Tendsto z atTop (𝓝 z₀) := ih v
      have hzn := (tendsto_iff_norm_sub_tendsto_zero).mp hzlim
      have hop := (tendsto_iff_norm_sub_tendsto_zero).mp
        (tendsto_kgBandMonodromy hb0 hWb hWs hT z₀)
      have hle : ∀ R : ℝ, ‖kgBandMonodromy W b hb0 hWb hWs R T (z R)
            - kgMonodromy W b hb0 hWb hWs T z₀‖
          ≤ Real.exp (b * |T|) * ‖z R - z₀‖
            + ‖kgBandMonodromy W b hb0 hWb hWs R T z₀ - kgMonodromy W b hb0 hWb hWs T z₀‖ := by
        intro R
        have hsplit : kgBandMonodromy W b hb0 hWb hWs R T (z R)
              - kgMonodromy W b hb0 hWb hWs T z₀
            = kgBandMonodromy W b hb0 hWb hWs R T (z R - z₀)
              + (kgBandMonodromy W b hb0 hWb hWs R T z₀ - kgMonodromy W b hb0 hWb hWs T z₀) := by
          rw [map_sub]
          abel
        rw [hsplit]
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact (kgBandMonodromy W b hb0 hWb hWs R T).le_of_opNorm_le
          (norm_kgBandMonodromy_le hb0 hWb hWs R) _
      have hsum : Tendsto (fun R : ℝ => Real.exp (b * |T|) * ‖z R - z₀‖
          + ‖kgBandMonodromy W b hb0 hWb hWs R T z₀
            - kgMonodromy W b hb0 hWb hWs T z₀‖) atTop (𝓝 0) := by
        simpa using (hzn.const_mul (Real.exp (b * |T|))).add hop
      exact squeeze_zero (fun _ => norm_nonneg _) hle hsum

/-- **Stability transfers from the band models.** A bound on the powers of the band monodromies,
uniform in the cut-off, is a bound on the powers of the true monodromy — so the stability of a
periodically driven clock may be decided on the band models, where the Cauchy problem is a genuine
strong problem. -/
theorem norm_kgMonodromy_pow_le_of_band_bound (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (hT : 0 ≤ T)
    {C : ℝ} (hC : ∀ R : ℝ, ∀ n : ℕ, ‖kgBandMonodromy W b hb0 hWb hWs R T ^ n‖ ≤ C) (n : ℕ) :
    ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0 n)
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun v => ?_
  have hlim := (tendsto_kgBandMonodromy_pow hb0 hWb hWs hT n v).norm
  refine le_of_tendsto hlim ?_
  filter_upwards with R
  exact (kgBandMonodromy W b hb0 hWb hWs R T ^ n).le_of_opNorm_le (hC R n) _

end BandMonodromy

end GaloisForLFunctions.HTGeometry
