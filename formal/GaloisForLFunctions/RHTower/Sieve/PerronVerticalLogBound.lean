import GaloisForLFunctions.RHTower.Sieve.CesaroPerronReduction
import GaloisForLFunctions.RHTower.Sieve.PerronVerticalPairBlockBound

/-!
# The truncated Perron integral is logarithmic in the height, not linear

Bounding the Perron kernel by its size at the real axis gives `∫_{|t| ≤ T} dt/‖σ+it‖ ≤ 2T/σ`, which is
linear in the height.  Splitting the range at `|t| = σ` gives the truth:

`∫_{|t| ≤ T} dt/‖σ+it‖ ≤ 2(1 + log(T/σ))`,

because `1/‖σ+it‖ ≤ 1/σ` on `|t| ≤ σ` and `≤ 1/|t|` beyond it.  Hence

`‖perronVertical σ T y‖ ≤ y^σ(1 + log(T/σ))/π`,

logarithmic in `T` where the crude bound was linear.  This is what makes the Cesàro error's contribution
from the neighbourhood of the cutoff `O(log T/T)` instead of `O(1/σ)`: that neighbourhood has length
`1/T`, so a bound of size `log T` there costs `log T/T`, while a bound of size `T/σ` costs `1/σ`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The reciprocal modulus on the line is at most `1/σ`. -/
theorem inv_norm_line_le_inv_sigma {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ≤ 1 / σ := by
  have h := perron_kernel_norm_le_const (x := 1) zero_lt_one hσ t
  rwa [Real.one_rpow] at h

/-- Away from the real axis the reciprocal modulus is at most `1/|t|`. -/
theorem inv_norm_line_le_inv_abs {σ : ℝ} {t : ℝ} (ht : t ≠ 0) :
    1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ≤ 1 / |t| := by
  have h := perron_kernel_norm_le_abs (x := 1) (σ := σ) zero_lt_one ht
  rwa [Real.one_rpow] at h

/-- The reciprocal modulus is continuous on the line. -/
theorem continuous_inv_norm_line {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun t : ℝ => 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ := by
  refine continuous_const.div ?_ fun t => ?_
  · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).norm
  · exact norm_ne_zero_iff.2 (line_ne_zero hσ t)

/-- **The positive half of the line integral.**  Splitting at `|t| = σ`. -/
theorem integral_inv_norm_line_le {σ T : ℝ} (hσ : 0 < σ) (hσT : σ ≤ T) :
    (∫ t in (0 : ℝ)..T, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖) ≤ 1 + Real.log (T / σ) := by
  have hcont := continuous_inv_norm_line hσ
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => 1 / ‖(σ : ℂ) + (t : ℝ) * I‖) (μ := volume)
    (hcont.intervalIntegrable 0 σ) (hcont.intervalIntegrable σ T)
  have hlow : (∫ t in (0 : ℝ)..σ, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖) ≤ 1 := by
    have hmono := intervalIntegral.integral_mono_on hσ.le (hcont.intervalIntegrable 0 σ)
      ((continuous_const (y := 1 / σ)).intervalIntegrable (μ := volume) 0 σ)
      fun t _ => inv_norm_line_le_inv_sigma hσ t
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hval : (σ - 0) * (1 / σ) = 1 := by
      rw [sub_zero]
      field_simp
    rw [hval] at hmono
    exact hmono
  have hhigh : (∫ t in σ..T, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖) ≤ Real.log (T / σ) := by
    have hzero : (0 : ℝ) ∉ Set.uIcc σ T := by
      rw [Set.uIcc_of_le hσT, Set.mem_Icc]
      intro h
      linarith [h.1]
    have hcont2 : ContinuousOn (fun t : ℝ => 1 / t) (Set.uIcc σ T) := by
      intro t ht
      rw [Set.uIcc_of_le hσT, Set.mem_Icc] at ht
      refine ContinuousAt.continuousWithinAt ?_
      exact continuousAt_const.div continuousAt_id (by linarith [ht.1] : t ≠ 0)
    have hptle : ∀ t ∈ Set.Icc σ T, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ≤ 1 / t := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hσ ht.1
      have hb := inv_norm_line_le_inv_abs (σ := σ) ht0.ne'
      rwa [abs_of_pos ht0] at hb
    have hmono := intervalIntegral.integral_mono_on hσT (hcont.intervalIntegrable σ T)
      (hcont2.intervalIntegrable (μ := volume)) hptle
    rw [integral_one_div hzero] at hmono
    exact hmono
  linarith [hsplit, hlow, hhigh]

/-- **The full line integral of the reciprocal modulus.**  Logarithmic in the height. -/
theorem integral_symm_inv_norm_line_le {σ T : ℝ} (hσ : 0 < σ) (hσT : σ ≤ T) :
    (∫ t in (-T)..T, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖) ≤ 2 * (1 + Real.log (T / σ)) := by
  have hcont := continuous_inv_norm_line hσ
  have heven : ∀ t : ℝ,
      1 / ‖(σ : ℂ) + ((-t : ℝ) : ℝ) * I‖ = 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ := by
    intro t
    rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I]
    congr 2
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => 1 / ‖(σ : ℂ) + (t : ℝ) * I‖) (μ := volume)
    (hcont.intervalIntegrable (-T) 0) (hcont.intervalIntegrable 0 T)
  have hrefl : (∫ t in (-T)..(0 : ℝ), 1 / ‖(σ : ℂ) + (t : ℝ) * I‖)
      = ∫ t in (0 : ℝ)..T, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ := by
    have h := intervalIntegral.integral_comp_neg
      (a := (0 : ℝ)) (b := T) (f := fun t : ℝ => 1 / ‖(σ : ℂ) + (t : ℝ) * I‖)
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    exact heven t
  have hpos := integral_inv_norm_line_le hσ hσT
  rw [hrefl] at hsplit
  linarith [hsplit, hpos]

/-- **The truncated Perron integral, logarithmic in the height.**  The crude bound `y^σT/(πσ)` is
replaced by `y^σ(1 + log(T/σ))/π`. -/
theorem norm_perronVertical_le_log {y σ T : ℝ} (hy : 0 < y) (hσ : 0 < σ) (hσT : σ ≤ T) :
    ‖perronVertical σ T y‖ ≤ y ^ σ * (1 + Real.log (T / σ)) / Real.pi := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hσ hσT
  have hTle : -T ≤ T := by linarith
  have hyσ : (0 : ℝ) ≤ y ^ σ := Real.rpow_nonneg hy.le σ
  have hlognn : (0 : ℝ) ≤ Real.log (T / σ) := Real.log_nonneg ((one_le_div hσ).2 hσT)
  have hcont : Continuous fun t : ℝ =>
      ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I) := by
    have hden : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℝ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hnum : Continuous fun t : ℝ => ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hslit : ((y : ℝ) : ℂ) ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
        simpa using hy
      exact (continuous_const (y := ((y : ℝ) : ℂ))).continuousAt.cpow hden.continuousAt hslit
    exact hnum.div hden fun t => line_ne_zero hσ t
  have hpt : ∀ t : ℝ,
      ‖((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)‖
        = y ^ σ * (1 / ‖(σ : ℂ) + (t : ℝ) * I‖) := by
    intro t
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre, mul_one_div]
  have hstep := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t : ℝ => ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)) hTle
  have hcongr : (∫ t in (-T)..T,
        ‖((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)‖)
      = y ^ σ * ∫ t in (-T)..T, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => y ^ σ * (1 / ‖(σ : ℂ) + (t : ℝ) * I‖))
      (fun t _ => hpt t), intervalIntegral.integral_const_mul]
  have hmain : ‖∫ t in (-T)..T,
        ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)‖
      ≤ y ^ σ * (2 * (1 + Real.log (T / σ))) := by
    refine le_trans hstep ?_
    rw [hcongr]
    exact mul_le_mul_of_nonneg_left (integral_symm_inv_norm_line_le hσ hσT) hyσ
  rw [perronVertical, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  have hval : (1 / (2 * Real.pi)) * (y ^ σ * (2 * (1 + Real.log (T / σ))))
      = y ^ σ * (1 + Real.log (T / σ)) / Real.pi := by
    field_simp
  calc (1 / (2 * Real.pi))
        * ‖∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (y ^ σ * (2 * (1 + Real.log (T / σ)))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = y ^ σ * (1 + Real.log (T / σ)) / Real.pi := hval

/-- The logarithmic bound in clamped form, valid at the cutoff itself where Perron's lemma
degenerates. -/
theorem norm_perronVerticalClamped_sub_one_le_log {σ T : ℝ} (hσ : 0 < σ) (hσT : σ ≤ T) {u : ℝ}
    (hu : 1 ≤ u) :
    ‖perronVerticalClamped σ T u - 1‖ ≤ u ^ σ * (1 + Real.log (T / σ)) / Real.pi + 1 := by
  have hu0 : (0 : ℝ) < u := by linarith
  rw [perronVerticalClamped_eq hu]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_one]
  linarith [norm_perronVertical_le_log hu0 hσ hσT]

end RHTower.Sieve
end
