import GaloisForLFunctions.HTGeometry.KleinGordonContinuousRate

/-!
# The growth rate transfers from the band models

Statement 324 transfers a *uniform* bound on the powers of the band monodromies to the true one, and
359 does the same for two-sided bounds. The rate itself transfers by the same argument: a geometric
bound `‖M_Rⁿ‖ ≤ Cqⁿ`, uniform in the cut-off, passes to the limit because the powers converge
strongly (statement 323).

A geometric bound on the powers caps the spectrum, because `|k|ⁿ ≤ ‖Mⁿ‖` (statement 410) and a
sequence `|k|ⁿ` below `Cqⁿ` forces `|k| ≤ q`. Hence

**the spectral radius of the true clock is bounded by the rate of its band models** — the growth rate,
like stability and oscillation, is decidable on the models where the Cauchy problem is a genuine strong
problem.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

/-! ## A geometric bound caps the base -/

/-- **A sequence dominated by a geometric one has base at most the geometric base.** -/
theorem norm_le_of_pow_geometric {x C q : ℝ} (hq : 0 < q) (h : ∀ n : ℕ, x ^ n ≤ C * q ^ n) :
    x ≤ q := by
  by_contra hlt
  push Not at hlt
  have hratio : 1 < x / q := (one_lt_div hq).mpr hlt
  have hdiv : Tendsto (fun n : ℕ => (x / q) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hratio
  obtain ⟨n, hn⟩ := (hdiv.eventually_gt_atTop C).exists
  have hq0 : 0 < q ^ n := pow_pos hq n
  rw [div_pow, lt_div_iff₀ hq0] at hn
  exact absurd (h n) (not_le.mpr hn)

/-! ## The transfer -/

section BandRate

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

set_option maxHeartbeats 1000000 in
/-- **A geometric bound on the band powers passes to the true monodromy.** -/
theorem norm_pow_le_of_band_rate (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (hT : 0 ≤ T)
    {C q : ℝ} (hC : ∀ R : ℝ, ∀ n : ℕ, ‖kgBandMonodromy W b hb0 hWb hWs R T ^ n‖ ≤ C * q ^ n)
    (n : ℕ) : ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C * q ^ n := by
  have hC0 : (0 : ℝ) ≤ C * q ^ n := le_trans (norm_nonneg _) (hC 0 n)
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun v => ?_
  have hlim := (tendsto_kgBandMonodromy_pow hb0 hWb hWs hT n v).norm
  refine le_of_tendsto hlim ?_
  filter_upwards with R
  exact (kgBandMonodromy W b hb0 hWb hWs R T ^ n).le_of_opNorm_le (hC R n) _

set_option maxHeartbeats 1000000 in
/-- **The spectral radius of the true clock is bounded by the rate of its band models.** -/
theorem spectralRadius_le_of_band_rate (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (hT : 0 ≤ T)
    {C q : ℝ} (hq : 0 < q)
    (hC : ∀ R : ℝ, ∀ n : ℕ, ‖kgBandMonodromy W b hb0 hWb hWs R T ^ n‖ ≤ C * q ^ n) :
    spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) ≤ ENNReal.ofReal q := by
  refine spectralRadius_le_ofReal_of_forall fun k hk => ?_
  have hpow : ∀ n : ℕ, ‖k‖ ^ n ≤ C * q ^ n := fun n =>
    (norm_pow_le_norm_pow_of_mem_spectrum (le_of_eq norm_one_kgEnergy) hk n).trans
      (norm_pow_le_of_band_rate hb0 hWb hWs hT hC n)
  exact norm_le_of_pow_geometric hq hpow

end BandRate

end GaloisForLFunctions.HTGeometry
