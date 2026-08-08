import GaloisForLFunctions.RHTower.Sieve.CesaroPerronBridge

/-!
# The Cesàro Perron error as an average of the sharp-cutoff error

Under the averaging identity the Cesàro kernel's distance from `log y` is the logarithmic average of the
sharp kernel's distance from `1`:

`‖(1/2π)∫_{|t| ≤ T}(y^s − 1)/s² dt − log y‖ ≤ ∫_1^y ‖perronVertical σ T u − 1‖ du/u`,

because `log y = ∫_1^y du/u`.  Two inputs make the right side finite where the pointwise sharp error is
not: the trivial bound `‖perronVertical σ T u‖ ≤ u^σ T/(πσ)`, which covers a neighbourhood of `u = 1` of
length `1/T` at cost `O(1/σ)`, and Perron's lemma `‖perronVertical σ T u − 1‖ ≤ u^σ/(πT log u)` away from
it.  The factor `1/log u` that forced the near-diagonal analysis in the sharp route is integrable against
`du/u`.

To keep the integrand continuous the cutoff variable is clamped by `max u 1`, exactly as in the averaging
identity; on `[1, y]` the clamped and unclamped kernels agree.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The sharp-cutoff Perron integrand with the cutoff variable clamped away from zero. -/
def perronBox (σ : ℝ) : ℝ → ℝ → ℂ := fun u t =>
  ((max u 1 : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)

theorem continuous_perronBox {σ : ℝ} (hσ : 0 < σ) :
    Continuous (Function.uncurry (perronBox σ)) := by
  have hbase : Continuous fun p : ℝ × ℝ => (((max p.1 1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_fst.max continuous_const)
  have hden : Continuous fun p : ℝ × ℝ => ((σ : ℂ) + (p.2 : ℝ) * I) :=
    continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hnum : Continuous fun p : ℝ × ℝ =>
      (((max p.1 1 : ℝ) : ℂ)) ^ ((σ : ℂ) + (p.2 : ℝ) * I) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hslit : (((max p.1 1 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
      simp only [Complex.ofReal_re]
      exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact hbase.continuousAt.cpow hden.continuousAt hslit
  exact hnum.div hden fun p => line_ne_zero hσ p.2

/-- The truncated Perron integral with the cutoff clamped: a continuous function of the cutoff. -/
def perronVerticalClamped (σ T u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T, perronBox σ u t

theorem continuous_perronVerticalClamped {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    Continuous fun u : ℝ => perronVerticalClamped σ T u := by
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_perronBox hσ) (-T) T

/-- Above the cutoff the clamp is invisible. -/
theorem perronVerticalClamped_eq {σ T u : ℝ} (hu : 1 ≤ u) :
    perronVerticalClamped σ T u = perronVertical σ T u := by
  rw [perronVerticalClamped, perronVertical]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [perronBox, max_eq_left hu]

/-- **The trivial bound for the truncated Perron integral.**  The kernel is at most `y^σ/σ` on the whole
line, so the truncated integral is at most `y^σT/(πσ)`. -/
theorem norm_perronVertical_le_trivial {y σ T : ℝ} (hy : 0 < y) (hσ : 0 < σ) (hT : 0 ≤ T) :
    ‖perronVertical σ T y‖ ≤ y ^ σ * T / (Real.pi * σ) := by
  have hTle : -T ≤ T := by linarith
  have hyσ : (0 : ℝ) ≤ y ^ σ := Real.rpow_nonneg hy.le σ
  have hcont : Continuous fun t : ℝ =>
      ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I) := by
    have hbase : Continuous fun _ : ℝ => ((y : ℝ) : ℂ) := continuous_const
    have hden : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℝ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hnum : Continuous fun t : ℝ => ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hslit : ((y : ℝ) : ℂ) ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
        simpa using hy
      exact hbase.continuousAt.cpow hden.continuousAt hslit
    exact hnum.div hden fun t => line_ne_zero hσ t
  have hpt : ∀ t : ℝ,
      ‖((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)‖ ≤ y ^ σ / σ := by
    intro t
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre]
    exact perron_kernel_norm_le_const hy hσ t
  have hmono : (∫ t in (-T)..T,
        ‖((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)‖)
      ≤ ∫ _t in (-T)..T, y ^ σ / σ :=
    intervalIntegral.integral_mono_on hTle (hcont.norm.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) fun t _ => hpt t
  have hconstint : (∫ _t in (-T)..T, y ^ σ / σ) = 2 * T * (y ^ σ / σ) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [perronVertical, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  have hstep := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t : ℝ => ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)) hTle
  rw [hconstint] at hmono
  have hfin : (1 / (2 * Real.pi)) * (2 * T * (y ^ σ / σ)) = y ^ σ * T / (Real.pi * σ) := by
    field_simp
  calc (1 / (2 * Real.pi))
        * ‖∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (2 * T * (y ^ σ / σ)) := by
        refine mul_le_mul_of_nonneg_left (le_trans hstep hmono) (by positivity)
    _ = y ^ σ * T / (Real.pi * σ) := hfin

/-- **The Cesàro error is the logarithmic average of the sharp error.**  `log y = ∫_1^y du/u`, so the two
errors differ only by the averaging. -/
theorem norm_perron_cesaro_sub_log_le_integral {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) {y : ℝ}
    (hy : 1 ≤ y) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t in (-T)..T,
          (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
        - ((Real.log y : ℝ) : ℂ)‖
      ≤ ∫ u in (1 : ℝ)..y, ‖perronVerticalClamped σ T u - 1‖ / u := by
  have hzero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) y := by
    rw [Set.uIcc_of_le hy, Set.mem_Icc]
    intro h
    linarith [h.1]
  have hupos : ∀ u ∈ Set.uIcc (1 : ℝ) y, (0 : ℝ) < u := by
    intro u hu
    rw [Set.uIcc_of_le hy, Set.mem_Icc] at hu
    linarith [hu.1]
  have hlogeq : ((Real.log y : ℝ) : ℂ) = ∫ u in (1 : ℝ)..y, 1 / (u : ℂ) := by
    have hreal : (∫ u in (1 : ℝ)..y, 1 / u) = Real.log y := by
      rw [integral_one_div hzero]
      simp
    have hcast : (∫ u in (1 : ℝ)..y, 1 / (u : ℂ))
        = ((∫ u in (1 : ℝ)..y, 1 / u : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun u _ => ?_
      push_cast
      rfl
    rw [hcast, hreal]
  have hPcont : ContinuousOn (fun u : ℝ => perronVerticalClamped σ T u / (u : ℂ))
      (Set.uIcc (1 : ℝ) y) := by
    intro u hu
    refine ContinuousAt.continuousWithinAt ?_
    refine ((continuous_perronVerticalClamped hσ T).continuousAt).div
      (Complex.continuous_ofReal.continuousAt) ?_
    exact_mod_cast (hupos u hu).ne'
  have hOnecont : ContinuousOn (fun u : ℝ => 1 / (u : ℂ)) (Set.uIcc (1 : ℝ) y) := by
    intro u hu
    refine ContinuousAt.continuousWithinAt ?_
    refine continuousAt_const.div (Complex.continuous_ofReal.continuousAt) ?_
    exact_mod_cast (hupos u hu).ne'
  have haverage : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t in (-T)..T,
        (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
      = ∫ u in (1 : ℝ)..y, perronVerticalClamped σ T u / (u : ℂ) := by
    rw [perron_cesaro_eq_average hσ hT hy]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hy, Set.mem_Icc] at hu
    rw [perronVerticalClamped_eq hu.1]
  rw [haverage, hlogeq, ← intervalIntegral.integral_sub hPcont.intervalIntegrable
    hOnecont.intervalIntegrable]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hy) (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hupos u hu
  rw [div_sub_div_same, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]

/-- Perron's lemma above the cutoff, in clamped form. -/
theorem norm_perronVerticalClamped_sub_one_le {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) {u : ℝ}
    (hu : 1 < u) :
    ‖perronVerticalClamped σ T u - 1‖ ≤ u ^ σ / (Real.pi * T * Real.log u) := by
  rw [perronVerticalClamped_eq (le_of_lt hu)]
  exact norm_perronVertical_sub_one_le hu hσ hT

/-- The trivial bound in clamped form: valid at the cutoff itself, where Perron's lemma degenerates. -/
theorem norm_perronVerticalClamped_sub_one_le_trivial {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) {u : ℝ}
    (hu : 1 ≤ u) :
    ‖perronVerticalClamped σ T u - 1‖ ≤ u ^ σ * T / (Real.pi * σ) + 1 := by
  have hu0 : (0 : ℝ) < u := by linarith
  rw [perronVerticalClamped_eq hu]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_one]
  linarith [norm_perronVertical_le_trivial hu0 hσ hT]

/-- **The Cesàro error from any pointwise bound on the sharp error.**  Every estimate for the truncated
sharp-cutoff kernel transfers to the Cesàro kernel by logarithmic averaging. -/
theorem norm_perron_cesaro_sub_log_le_of_bound {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) {y : ℝ}
    (hy : 1 ≤ y) {E : ℝ → ℝ} (hEint : IntervalIntegrable (fun u => E u / u) volume 1 y)
    (hE : ∀ u ∈ Set.Icc (1 : ℝ) y, ‖perronVerticalClamped σ T u - 1‖ ≤ E u) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t in (-T)..T,
          (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
        - ((Real.log y : ℝ) : ℂ)‖
      ≤ ∫ u in (1 : ℝ)..y, E u / u := by
  refine le_trans (norm_perron_cesaro_sub_log_le_integral hσ hT hy) ?_
  have hcont : ContinuousOn (fun u : ℝ => ‖perronVerticalClamped σ T u - 1‖ / u)
      (Set.uIcc (1 : ℝ) y) := by
    refine ContinuousOn.div (ContinuousOn.norm ?_) continuousOn_id ?_
    · exact (continuous_perronVerticalClamped hσ T).continuousOn.sub continuousOn_const
    · intro u hu
      rw [Set.uIcc_of_le hy, Set.mem_Icc] at hu
      have : (0 : ℝ) < u := by linarith [hu.1]
      exact this.ne'
  refine intervalIntegral.integral_mono_on hy hcont.intervalIntegrable hEint fun u hu => ?_
  have hu0 : (0 : ℝ) < u := by
    rw [Set.mem_Icc] at hu
    linarith [hu.1]
  exact div_le_div_of_nonneg_right (hE u hu) hu0.le

end RHTower.Sieve
end
