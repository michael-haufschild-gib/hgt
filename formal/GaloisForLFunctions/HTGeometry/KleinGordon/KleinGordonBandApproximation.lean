import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonStrongDifference

/-!
# The band approximation is faithful

The band theory of the previous files is a complete theory — strong solutions, well-posedness, exact
conservation, a well-posed inverse problem — but it is a theory of the *compressed* equation
`∂ₜ²u = −⟨D⟩²u + P_R W P_R u` with band-limited data. This file shows it approximates the true one:
as the cut-off grows the band solutions converge to the solution of the original equation.

The operator-norm estimate of statement 136 cannot see this, because `P_R W P_R` does not converge to
`W` in norm. The sharper estimate of statement 234 can: it measures the perturbations by their action
along the true solution, and there the convergence is the strong convergence of statement 215,
dominated by `2‖W‖‖u(s)‖` on the interval.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Approximation

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The accumulated discrepancy of the band compressions vanishes.** -/
theorem tendsto_integral_kgBandOp_sub (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (u : ℝ → Lp ℂ 2 (volume : Measure E)) (hu : Continuous u) (t : ℝ) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..t, ‖(kgBandOp W₀ R - W₀) (u s)‖) atTop (𝓝 0) := by
  have hbound : IntervalIntegrable (fun s : ℝ => 2 * b * ‖u s‖) volume 0 t :=
    (continuous_const.mul hu.norm).intervalIntegrable 0 t
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable
      (fun s : ℝ => ‖(kgBandOp W₀ R - W₀) (u s)‖) (volume.restrict (Set.uIoc 0 t)) := by
    intro R
    exact (((kgBandOp W₀ R - W₀).continuous.comp hu).norm).aestronglyMeasurable
  have hdom : ∀ R : ℝ, ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      ‖‖(kgBandOp W₀ R - W₀) (u s)‖‖ ≤ 2 * b * ‖u s‖ := by
    intro R
    filter_upwards with s _
    have h1 : ‖(kgBandOp W₀ R - W₀) (u s)‖ ≤ ‖kgBandOp W₀ R (u s)‖ + ‖W₀ (u s)‖ := by
      rw [sub_apply]
      exact norm_sub_le _ _
    have h2 : ‖kgBandOp W₀ R (u s)‖ ≤ b * ‖u s‖ :=
      (kgBandOp W₀ R).le_of_opNorm_le (norm_kgBandOp_le hb0 hW R) _
    have h3 : ‖W₀ (u s)‖ ≤ b * ‖u s‖ := W₀.le_of_opNorm_le hW _
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    linarith
  have hlim : ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      Tendsto (fun R : ℝ => ‖(kgBandOp W₀ R - W₀) (u s)‖) atTop (𝓝 0) := by
    filter_upwards with s _
    have h := tendsto_kgBandOp_apply (W₀ := W₀) (u s)
    have h0 := (tendsto_iff_norm_sub_tendsto_zero).mp h
    refine h0.congr fun R => ?_
    rw [sub_apply]
  have hres := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun s : ℝ => 2 * b * ‖u s‖) (l := (atTop : Filter ℝ))
    (F := fun R : ℝ => fun s : ℝ => ‖(kgBandOp W₀ R - W₀) (u s)‖) (f := fun _ : ℝ => (0 : ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hdom) hbound hlim
  simpa using hres

/-- **The band solutions converge to the true solution**, forwards in time. -/
theorem tendsto_kgFieldMild_band_of_nonneg (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (x y : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ => kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldMild W₀ x y t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hcu : Continuous (kgFieldMild W₀ x y) := continuous_kgFieldMild hb0 hW x y
  have hle : ∀ R : ℝ,
      ‖kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) t
          - kgFieldMild W₀ x y t‖
        ≤ (‖kgLowPassOp R x - x‖ + ‖kgLowPassOp R y - y‖
            + ∫ s in (0 : ℝ)..t, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ x y s)‖)
          * Real.exp (b * t) := fun R =>
    norm_kgFieldMild_sub_general_le hb0 (norm_kgBandOp_le hb0 hW R) hW _ _ _ _ ht
  have h1 : Tendsto (fun R : ℝ => ‖kgLowPassOp R x - x‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply x)
  have h2 : Tendsto (fun R : ℝ => ‖kgLowPassOp R y - y‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply y)
  have h3 := tendsto_integral_kgBandOp_sub hb0 hW (kgFieldMild W₀ x y) hcu t
  have hsum : Tendsto (fun R : ℝ => (‖kgLowPassOp R x - x‖ + ‖kgLowPassOp R y - y‖
      + ∫ s in (0 : ℝ)..t, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ x y s)‖)
        * Real.exp (b * t)) atTop (𝓝 0) := by
    have hadd := (h1.add h2).add h3
    have hmul := hadd.mul_const (Real.exp (b * t))
    simpa using hmul
  exact squeeze_zero (fun _ => norm_nonneg _) hle hsum

/-- **The band solutions converge to the true solution.** The band theory is a faithful
approximation: what it proves about the compressed equation is the limit of what holds for the
original one. -/
theorem tendsto_kgFieldMild_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldMild W₀ x y t)) := by
  rcases le_total (0 : ℝ) t with ht | ht
  · exact tendsto_kgFieldMild_band_of_nonneg hb0 hW x y ht
  · have hneg : (0 : ℝ) ≤ -t := by linarith
    have hkey := tendsto_kgFieldMild_band_of_nonneg hb0 hW x (-y) hneg
    have hrefl : ∀ R : ℝ,
        kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (-(kgLowPassOp R y)) (-t)
          = kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) t := by
      intro R
      have h := kgFieldMild_neg hb0 (norm_kgBandOp_le hb0 hW R) (kgLowPassOp R x)
        (kgLowPassOp R y) (-t)
      rw [neg_neg] at h
      exact h.symm
    have hrefl0 : kgFieldMild W₀ x (-y) (-t) = kgFieldMild W₀ x y t := by
      have h := kgFieldMild_neg hb0 hW x y (-t)
      rw [neg_neg] at h
      exact h.symm
    rw [← hrefl0]
    refine hkey.congr fun R => ?_
    rw [← hrefl R, map_neg]
end Approximation

end GaloisForLFunctions.HTGeometry
