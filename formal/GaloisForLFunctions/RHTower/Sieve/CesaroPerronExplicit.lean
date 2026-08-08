import GaloisForLFunctions.RHTower.Sieve.CesaroPerronReduction
import GaloisForLFunctions.RHTower.Sieve.LogLogAntiderivative
import GaloisForLFunctions.RHTower.Sieve.PerronVerticalLogBound

/-!
# The truncated Cesàro Perron formula, explicitly

The logarithmic average of the sharp-cutoff error is charged in three pieces, split at `1 + 1/T` and
at `2`:

* on `[1, 1+1/T]` Perron's lemma degenerates, so the trivial bound `u^σT/(πσ) + 1` is used; the interval
  has length `1/T`, which cancels the `T`;
* on `[1+1/T, 2]` Perron's lemma gives `u^σ/(πT log u)`, and `∫du/(u log u) = log log` contributes one
  logarithm of the height;
* on `[2, y]` the logarithm is bounded below by `log 2` and `∫u^{σ−1}du ≤ y^σ/σ`.

`‖(1/2π)∫_{|t| ≤ T}(y^s − 1)/s²dt − log y‖
    ≤ (4/(πσ) + 1/T) + (4/(πT))(log log 2 − log log(1 + 1/T)) + y^σ/(πTσ log 2)`

for `1 ≤ σ ≤ 2`, `T ≥ 1`, `y ≥ 1`.  Every term is `O(1) + O(log T/T) + O(y^σ/T)`: no factor `N`, no
`1/log y`, and no near-diagonal analysis.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The averaged integrand is integrable on every interval away from the origin. -/
theorem intervalIntegrable_cesaro_integrand {σ : ℝ} (hσ : 0 < σ) (T : ℝ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ‖perronVerticalClamped σ T u - 1‖ / u) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (ContinuousOn.norm ?_) continuousOn_id ?_
  · exact (continuous_perronVerticalClamped hσ T).continuousOn.sub continuousOn_const
  · intro u hu
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hu
    have : (0 : ℝ) < u := lt_of_lt_of_le ha hu.1
    exact this.ne'

/-- `u^σ ≤ 4` on `[1,2]` for `σ ≤ 2`. -/
theorem rpow_le_four {σ u : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    u ^ σ ≤ 4 := by
  have h1 : u ^ σ ≤ (2 : ℝ) ^ σ := Real.rpow_le_rpow (by linarith) hu2 (by linarith)
  have h2 : (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ2
  have h3 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  linarith

/-- **The first piece.**  On the interval of length `1/T` at the cutoff, the trivial bound. -/
theorem cesaro_piece_one_le {σ T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) {a : ℝ}
    (ha1 : 1 ≤ a) (ha2 : a ≤ 1 + 1 / T) :
    (∫ u in (1 : ℝ)..a, ‖perronVerticalClamped σ T u - 1‖ / u)
      ≤ (4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1) / T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hTσ0 : (0 : ℝ) ≤ T / σ := by positivity
  have hlognn : (0 : ℝ) ≤ Real.log (1 + T / σ) := Real.log_nonneg (by linarith)
  have hinvT : 1 / T ≤ 1 := by
    rw [div_le_one hT0]; linarith
  have ha2' : a ≤ 2 := by linarith
  have hpt : ∀ u ∈ Set.Icc (1 : ℝ) a,
      ‖perronVerticalClamped σ T u - 1‖ / u
        ≤ 4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1 := by
    intro u hu
    rw [Set.mem_Icc] at hu
    have hu1 : (1 : ℝ) ≤ u := hu.1
    have hu0 : (0 : ℝ) < u := by linarith
    have hbase := norm_perronVerticalClamped_sub_one_le_log hσ0 hT0.le hu1
    have hfour : u ^ σ ≤ 4 := rpow_le_four hσ1 hσ2 hu1 (by linarith [hu.2])
    have hstep : ‖perronVerticalClamped σ T u - 1‖
        ≤ 4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1 := by
      refine le_trans hbase ?_
      have hd : u ^ σ * (1 + Real.log (1 + T / σ)) / Real.pi
          ≤ 4 * (1 + Real.log (1 + T / σ)) / Real.pi := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hfour (by linarith)
      linarith
    calc ‖perronVerticalClamped σ T u - 1‖ / u ≤ ‖perronVerticalClamped σ T u - 1‖ / 1 := by
          refine div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one hu1
      _ = ‖perronVerticalClamped σ T u - 1‖ := by rw [div_one]
      _ ≤ 4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1 := hstep
  have hmono := intervalIntegral.integral_mono_on ha1
    (intervalIntegrable_cesaro_integrand hσ0 T zero_lt_one ha1)
    ((continuous_const (y := 4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1)).intervalIntegrable
      (μ := volume) 1 a) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hlen : a - 1 ≤ 1 / T := by linarith
  have hCnn : (0 : ℝ) ≤ 4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1 := by positivity
  have hfin : (a - 1) * (4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1)
      ≤ (1 / T) * (4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1) :=
    mul_le_mul_of_nonneg_right hlen hCnn
  have hval : (1 / T) * (4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1)
      = (4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1) / T := by ring
  rw [hval] at hfin
  linarith

/-- **The second piece.**  Between the cutoff neighbourhood and `2`, Perron's lemma against
`∫du/(u log u)`. -/
theorem cesaro_piece_two_le {σ T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) {a b : ℝ}
    (ha : 1 + 1 / T ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    (∫ u in a..b, ‖perronVerticalClamped σ T u - 1‖ / u)
      ≤ (4 / (Real.pi * T)) * (Real.log (Real.log 2) - Real.log (Real.log (1 + 1 / T))) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hTinv : (0 : ℝ) < 1 / T := by positivity
  have ha1 : 1 < a := by linarith
  have hpt : ∀ u ∈ Set.Icc a b,
      ‖perronVerticalClamped σ T u - 1‖ / u
        ≤ (4 / (Real.pi * T)) * (1 / (u * Real.log u)) := by
    intro u hu
    rw [Set.mem_Icc] at hu
    have hu1 : 1 < u := lt_of_lt_of_le ha1 hu.1
    have hu0 : (0 : ℝ) < u := by linarith
    have hlogpos : (0 : ℝ) < Real.log u := Real.log_pos hu1
    have hbase := norm_perronVerticalClamped_sub_one_le hσ0 hT0 hu1
    have hfour : u ^ σ ≤ 4 := rpow_le_four hσ1 hσ2 hu1.le (by linarith [hu.2])
    have hstep : ‖perronVerticalClamped σ T u - 1‖ / u
        ≤ (u ^ σ / (Real.pi * T * Real.log u)) / u :=
      div_le_div_of_nonneg_right hbase hu0.le
    have hval : (u ^ σ / (Real.pi * T * Real.log u)) / u
        = (u ^ σ / (Real.pi * T)) * (1 / (u * Real.log u)) := by
      field_simp
    have hmul : (u ^ σ / (Real.pi * T)) * (1 / (u * Real.log u))
        ≤ (4 / (Real.pi * T)) * (1 / (u * Real.log u)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact div_le_div_of_nonneg_right hfour (by positivity)
    rw [hval] at hstep
    exact le_trans hstep hmul
  have hcont : ContinuousOn (fun u : ℝ => (4 / (Real.pi * T)) * (1 / (u * Real.log u)))
      (Set.uIcc a b) := continuousOn_const.mul (continuousOn_inv_mul_log ha1 hab)
  have hmono := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_cesaro_integrand hσ0 T (by linarith) hab)
    hcont.intervalIntegrable hpt
  rw [intervalIntegral.integral_const_mul, integral_inv_mul_log_eq ha1 hab] at hmono
  refine le_trans hmono ?_
  have hb1 : 1 < b := lt_of_lt_of_le ha1 hab
  have hmonoUp : Real.log (Real.log b) ≤ Real.log (Real.log 2) :=
    Real.log_le_log (Real.log_pos hb1) (Real.log_le_log (by linarith) hb)
  have h1T : (1 : ℝ) < 1 + 1 / T := by linarith
  have hmonoDown : Real.log (Real.log (1 + 1 / T)) ≤ Real.log (Real.log a) :=
    Real.log_le_log (Real.log_pos h1T) (Real.log_le_log (by linarith) ha)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **The third piece.**  Beyond `2` the logarithm is bounded below and the power integrates. -/
theorem cesaro_piece_three_le {σ T : ℝ} (hσ1 : 1 ≤ σ) (hT : 1 ≤ T) {a y : ℝ}
    (ha : 2 ≤ a) (hay : a ≤ y) :
    (∫ u in a..y, ‖perronVerticalClamped σ T u - 1‖ / u)
      ≤ y ^ σ / (Real.pi * T * σ * Real.log 2) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : (0 : ℝ) < a := by linarith
  have hpt : ∀ u ∈ Set.Icc a y,
      ‖perronVerticalClamped σ T u - 1‖ / u
        ≤ (1 / (Real.pi * T * Real.log 2)) * u ^ (σ - 1) := by
    intro u hu
    rw [Set.mem_Icc] at hu
    have hu2 : (2 : ℝ) ≤ u := le_trans ha hu.1
    have hu1 : 1 < u := by linarith
    have hu0 : (0 : ℝ) < u := by linarith
    have hlogu : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu2
    have hbase := norm_perronVerticalClamped_sub_one_le hσ0 hT0 hu1
    have hstep : ‖perronVerticalClamped σ T u - 1‖ / u
        ≤ (u ^ σ / (Real.pi * T * Real.log u)) / u :=
      div_le_div_of_nonneg_right hbase hu0.le
    refine le_trans hstep ?_
    have hden : (0 : ℝ) < Real.pi * T * Real.log 2 := by positivity
    have hmono2 : (u ^ σ / (Real.pi * T * Real.log u)) / u
        ≤ (u ^ σ / (Real.pi * T * Real.log 2)) / u := by
      refine div_le_div_of_nonneg_right ?_ hu0.le
      refine div_le_div_of_nonneg_left (Real.rpow_nonneg hu0.le σ) hden ?_
      exact mul_le_mul_of_nonneg_left hlogu (by positivity)
    refine le_trans hmono2 (le_of_eq ?_)
    rw [Real.rpow_sub hu0, Real.rpow_one]
    field_simp
  have hcont : ContinuousOn (fun u : ℝ => (1 / (Real.pi * T * Real.log 2)) * u ^ (σ - 1))
      (Set.uIcc a y) := by
    refine continuousOn_const.mul ?_
    intro u hu
    rw [Set.uIcc_of_le hay, Set.mem_Icc] at hu
    refine ContinuousAt.continuousWithinAt ?_
    exact Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hu.1] : u ≠ 0))
  have hmono := intervalIntegral.integral_mono_on hay
    (intervalIntegrable_cesaro_integrand hσ0 T ha0 hay) hcont.intervalIntegrable hpt
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : (-1 : ℝ) < σ - 1))] at hmono
  refine le_trans hmono ?_
  have hsub : σ - 1 + 1 = σ := by ring
  rw [hsub]
  have hann : (0 : ℝ) ≤ a ^ σ := Real.rpow_nonneg ha0.le σ
  have hstep : (1 / (Real.pi * T * Real.log 2)) * ((y ^ σ - a ^ σ) / σ)
      ≤ (1 / (Real.pi * T * Real.log 2)) * (y ^ σ / σ) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) hσ0.le
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-- **The truncated Cesàro Perron formula.**  For `1 ≤ σ ≤ 2` and `T ≥ 1`, uniformly in `y ≥ 1`:

`‖(1/2π)∫_{|t| ≤ T}(y^s − 1)/s²dt − log y‖
    ≤ (4/(πσ) + 1/T) + (4/(πT))(log log 2 − log log(1 + 1/T)) + y^σ/(πTσ log 2)`.

No factor `N`, no `1/log y`: the logarithmic average of the sharp-cutoff error is finite where the
pointwise error is not. -/
theorem norm_perron_cesaro_sub_log_le_explicit {σ T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t in (-T)..T,
          (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
        - ((Real.log y : ℝ) : ℂ)‖
      ≤ (4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1) / T
        + (4 / (Real.pi * T)) * (Real.log (Real.log 2) - Real.log (Real.log (1 + 1 / T)))
        + y ^ σ / (Real.pi * T * σ * Real.log 2) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hTinv : (0 : ℝ) < 1 / T := by positivity
  have hinvT1 : 1 / T ≤ 1 := by
    rw [div_le_one hT0]; linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hP2nn : (0 : ℝ) ≤ (4 / (Real.pi * T))
      * (Real.log (Real.log 2) - Real.log (Real.log (1 + 1 / T))) := by
    have h1T : (1 : ℝ) < 1 + 1 / T := by linarith
    have hmon : Real.log (Real.log (1 + 1 / T)) ≤ Real.log (Real.log 2) :=
      Real.log_le_log (Real.log_pos h1T) (Real.log_le_log (by linarith) (by linarith))
    exact mul_nonneg (by positivity) (by linarith)
  have hP3nn : (0 : ℝ) ≤ y ^ σ / (Real.pi * T * σ * Real.log 2) := by
    have hyσ : (0 : ℝ) ≤ y ^ σ := Real.rpow_nonneg (by linarith) σ
    positivity
  have hbound : (∫ u in (1 : ℝ)..y, ‖perronVerticalClamped σ T u - 1‖ / u)
      ≤ (4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1) / T
        + (4 / (Real.pi * T)) * (Real.log (Real.log 2) - Real.log (Real.log (1 + 1 / T)))
        + y ^ σ / (Real.pi * T * σ * Real.log 2) := by
    rcases le_total y (1 + 1 / T) with hcase | hcase
    · have h1 := cesaro_piece_one_le hσ1 hσ2 hT hy hcase
      linarith
    · rcases le_total y 2 with hy2 | hy2
      · have hs1 := intervalIntegral.integral_add_adjacent_intervals
          (f := fun u : ℝ => ‖perronVerticalClamped σ T u - 1‖ / u) (μ := volume)
          (intervalIntegrable_cesaro_integrand hσ0 T zero_lt_one
            (by linarith : (1 : ℝ) ≤ 1 + 1 / T))
          (intervalIntegrable_cesaro_integrand hσ0 T (by linarith : (0 : ℝ) < 1 + 1 / T) hcase)
        have h1 := cesaro_piece_one_le hσ1 hσ2 hT (by linarith : (1 : ℝ) ≤ 1 + 1 / T) (le_refl _)
        have h2 := cesaro_piece_two_le (T := T) hσ1 hσ2 (by linarith) (le_refl _) hcase hy2
        linarith [hs1]
      · have hs1 := intervalIntegral.integral_add_adjacent_intervals
          (f := fun u : ℝ => ‖perronVerticalClamped σ T u - 1‖ / u) (μ := volume)
          (intervalIntegrable_cesaro_integrand hσ0 T zero_lt_one
            (by linarith : (1 : ℝ) ≤ 1 + 1 / T))
          (intervalIntegrable_cesaro_integrand hσ0 T (by linarith : (0 : ℝ) < 1 + 1 / T)
            (by linarith : (1 : ℝ) + 1 / T ≤ 2))
        have hs2 := intervalIntegral.integral_add_adjacent_intervals
          (f := fun u : ℝ => ‖perronVerticalClamped σ T u - 1‖ / u) (μ := volume)
          (intervalIntegrable_cesaro_integrand hσ0 T zero_lt_one (by norm_num : (1 : ℝ) ≤ 2))
          (intervalIntegrable_cesaro_integrand hσ0 T (by norm_num : (0 : ℝ) < 2) hy2)
        have h1 := cesaro_piece_one_le hσ1 hσ2 hT (by linarith : (1 : ℝ) ≤ 1 + 1 / T) (le_refl _)
        have h2 := cesaro_piece_two_le (T := T) hσ1 hσ2 (by linarith) (le_refl _)
          (by linarith : (1 : ℝ) + 1 / T ≤ 2) (le_refl _)
        have h3 := cesaro_piece_three_le (T := T) hσ1 (by linarith) (le_refl (2 : ℝ)) hy2
        linarith [hs1, hs2]
  exact le_trans (norm_perron_cesaro_sub_log_le_integral hσ0 hT0.le hy) hbound

end RHTower.Sieve
end
