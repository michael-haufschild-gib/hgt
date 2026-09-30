import GaloisForLFunctions.RHTower.LiEvenCrossEulerSmallMassProfile

/-!
# Source-dependent crossover limits of actual LI Euler jets

Any convergent binary mass scale `4^k v` lies eventually in one logarithmic
window. The uniform complete-tail estimate therefore gives the exact two-term
limit along arbitrary filters, without sign assumptions on higher moments.
-/

namespace RHTower

noncomputable section

private theorem eulerJetOrder_le_log_window_of_scale_le
    {v W : ℝ} (hv : 0 < v) (hW : 0 < W) (k : ℕ)
    (hscale : (4 : ℝ) ^ k * v ≤ W) :
    (k : ℝ) ≤ -Real.log v / Real.log 4 + Real.log W / Real.log 4 := by
  have hlog := (Real.log_le_log_iff (by positivity : 0 < (4 : ℝ) ^ k * v) hW).2 hscale
  rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 4) k).ne' hv.ne',
    Real.log_pow] at hlog
  have hk : (k : ℝ) ≤ (Real.log W - Real.log v) / Real.log 4 :=
    (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 4))).2 (by linarith)
  convert hk using 1
  ring

/-- A bounded binary mass scale forces the complete higher-moment tail to vanish. -/
theorem liEvenCrossEulerNormalizedMassTail_tendsto_zero
    {α : Type*} {l : Filter α} {v : α → ℝ} {k : α → ℕ} {w : ℝ}
    (hv : Filter.Tendsto v l (nhdsWithin 0 (Set.Ioi 0)))
    (hw : Filter.Tendsto (fun a => (4 : ℝ) ^ k a * v a) l (nhds w)) :
    Filter.Tendsto (fun a => liEvenCrossEulerNormalizedMassTail (v a) (k a)) l (nhds 0) := by
  let W : ℝ := |w| + 1
  have hW : 0 < W := by dsimp [W]; positivity
  have hwW : w < W := by dsimp [W]; linarith [le_abs_self w]
  have hwindow : ∀ᶠ a in l,
      (k a : ℝ) ≤ -Real.log (v a) / Real.log 4 + Real.log W / Real.log 4 := by
    filter_upwards [hv.eventually self_mem_nhdsWithin,
      hw.eventually (Iio_mem_nhds hwW)] with a hva hwa
    exact eulerJetOrder_le_log_window_of_scale_le hva hW (k a) hwa.le
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hwindow,
    hv.eventually (liEvenCrossEulerNormalizedMassTail_uniform_log_window
      (Real.log W / Real.log 4) hε)] with a hka htail
  simpa [Real.dist_eq] using htail (k a) hka

/-- **Actual source crossover profile:** the limiting binary mass scale retains `M₀,M₁`. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_two_term_profile_tendsto
    {α : Type*} {l : Filter α} {v : α → ℝ} {k : α → ℕ} {w : ℝ}
    (hv : Filter.Tendsto v l (nhdsWithin 0 (Set.Ioi 0)))
    (hw : Filter.Tendsto (fun a => (4 : ℝ) ^ k a * v a) l (nhds w)) :
    Filter.Tendsto
      (fun a => liEvenCrossFirstCurrentEvenEulerJet (v a) (k a) / (2 * v a))
      l (nhds (normalizedPrimeArchMoment 0 - 4 * w * normalizedPrimeArchMoment 1)) := by
  have htail := liEvenCrossEulerNormalizedMassTail_tendsto_zero hv hw
  have hleading := (hw.const_mul (4 * normalizedPrimeArchMoment 1)).const_sub
    (normalizedPrimeArchMoment 0)
  have hsum := hleading.add htail
  have hquarter : ∀ᶠ y : ℝ in nhdsWithin 0 (Set.Ioi 0), y < 1 / 4 :=
    (show ∀ᶠ y : ℝ in nhds 0, y < 1 / 4 from
      Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  have heq : (fun a => normalizedPrimeArchMoment 0 -
      (4 * normalizedPrimeArchMoment 1) * ((4 : ℝ) ^ k a * v a) +
        liEvenCrossEulerNormalizedMassTail (v a) (k a)) =ᶠ[l]
      (fun a => liEvenCrossFirstCurrentEvenEulerJet (v a) (k a) / (2 * v a)) := by
    filter_upwards [hv.eventually self_mem_nhdsWithin, hv.eventually hquarter] with a hva hqa
    rw [liEvenCrossFirstCurrentEvenEulerJet_div_two_mul_mass_eq hva hqa.le, pow_succ]
    ring
  have htarget : normalizedPrimeArchMoment 0 - (4 * normalizedPrimeArchMoment 1) * w + 0 =
      normalizedPrimeArchMoment 0 - 4 * w * normalizedPrimeArchMoment 1 := by ring
  rw [htarget] at hsum
  exact hsum.congr' heq

end

end RHTower
