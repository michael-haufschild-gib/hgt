import GaloisForLFunctions.BiScaleUncertainty.FactorialPolarLossLowerBound

/-! The actual factorial polar loss has asymptotic coefficient one quarter.
Only finite arithmetic bounds and scalar limits are used; no limit is passed
through the full Weil form. -/

open Filter MeasureTheory Set
open scoped Topology CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

private theorem index_cast_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => ((n+k : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat k)

private theorem inv_index_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => 1/((n+k : ℕ) : ℝ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp (index_cast_tendsto k)

theorem harmonicCorrection_tendsto_half :
    Tendsto (fun n : ℕ => harmonicCorrection (n+1)) atTop (𝓝 (1/2 : ℝ)) := by
  have h0 : ∀ n : ℕ, 0 ≤ (1/2 : ℝ)-harmonicCorrection (n+1) := fun n =>
    sub_nonneg.mpr (harmonicCorrection_bounds_sharp (by omega : 1 ≤ n+1)).2
  have hle : ∀ n : ℕ, (1/2 : ℝ)-harmonicCorrection (n+1) ≤ 1/((n+1 : ℕ) : ℝ) := by
    intro n
    have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have hb := (harmonicCorrection_bounds_sharp (by omega : 1 ≤ n+1)).1
    calc
      _ ≤ (1/2 : ℝ)-((n+1 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ)+1) := by linarith
      _ = 1/(2*(2*((n+1 : ℕ) : ℝ)+1)) := by field_simp; ring
      _ ≤ _ := one_div_le_one_div_of_le hn (by linarith)
  have hz := squeeze_zero h0 hle (inv_index_tendsto 1)
  have hc : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 (1/2 : ℝ)) := tendsto_const_nhds
  simpa using hc.sub hz

private theorem chebyshev_log_sandwich (n : ℕ) :
    Real.log (n+2 : ℕ)/2 ≤ chebyshevBiNullProducer (n+1) ∧
      chebyshevBiNullProducer (n+1) ≤ Real.log (n+2 : ℕ)/2+Real.log (9/4 : ℝ)/2 := by
  have hlo := chebyshevBiNullProducer_log_lower (n+1)
  rw [show (((n+1 : ℕ) : ℝ)+1) = ((n+2 : ℕ) : ℝ) by push_cast; ring] at hlo
  have hhi := chebyshevBiNullProducer_log_upper n
  have hlog : Real.log (n+1 : ℕ) ≤ Real.log (n+2 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show n+1 ≤ n+2 by omega))
  exact ⟨hlo, by linarith⟩

theorem chebyshevBiNullProducer_normalized_tendsto_half :
    Tendsto (fun n : ℕ => chebyshevBiNullProducer (n+1)/Real.log (n+2 : ℕ))
      atTop (𝓝 (1/2 : ℝ)) := by
  have hi : Tendsto (fun n : ℕ => 1/Real.log (n+2 : ℕ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp (index_cast_tendsto 2))
  have hb : Tendsto (fun n : ℕ => (Real.log (9/4 : ℝ)/2)*(1/Real.log (n+2 : ℕ)))
      atTop (𝓝 0) := by simpa using hi.const_mul (Real.log (9/4 : ℝ)/2)
  have h0 : ∀ n : ℕ, 0 ≤ chebyshevBiNullProducer (n+1)/Real.log (n+2 : ℕ)-(1/2 : ℝ) := by
    intro n
    have hlog : 0 < Real.log (n+2 : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n+2 by omega))
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hlog).2
    have h := (chebyshev_log_sandwich n).1
    linarith
  have hle : ∀ n : ℕ, chebyshevBiNullProducer (n+1)/Real.log (n+2 : ℕ)-(1/2 : ℝ) ≤
      (Real.log (9/4 : ℝ)/2)*(1/Real.log (n+2 : ℕ)) := by
    intro n
    have hlog : 0 < Real.log (n+2 : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n+2 by omega))
    have h := (chebyshev_log_sandwich n).2
    calc
      _ = (chebyshevBiNullProducer (n+1)-Real.log (n+2 : ℕ)/2)/Real.log (n+2 : ℕ) := by
        field_simp
      _ ≤ (Real.log (9/4 : ℝ)/2)/Real.log (n+2 : ℕ) :=
        div_le_div_of_nonneg_right (by linarith) hlog.le
      _ = _ := by ring
  have hz := squeeze_zero h0 hle hb
  have hc : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 (1/2 : ℝ)) := tendsto_const_nhds
  simpa using hz.add hc

theorem factorialPolarCollar_tendsto :
    Tendsto (fun n : ℕ => sourceFactorialCollar (n+1)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => (sourceFactorialCollar_pos (by omega : 1 ≤ n+1)).le) ?_
    (inv_index_tendsto 1)
  intro n
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ))).2
  exact sourceFactorialCollar_small_budget (N := n+1) (K := n+1) (by omega) (by omega)

/-- The coefficient is for the literal pole of the actual compact source. -/
theorem factorialPolarLoss_normalized_tendsto_quarter :
    Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)*factorialPolarLoss n/Real.log (n+2 : ℕ))
      atTop (𝓝 (1/4 : ℝ)) := by
  have hε : Tendsto (fun n : ℕ => 1+sourceFactorialCollar (n+1)/2) atTop (𝓝 (1 : ℝ)) := by
    simpa using (factorialPolarCollar_tendsto.div_const (2 : ℝ)).const_add (1 : ℝ)
  have he : (fun n : ℕ => ((n+1 : ℕ) : ℝ)*factorialPolarLoss n/Real.log (n+2 : ℕ)) =
      fun n => (1+sourceFactorialCollar (n+1)/2)*harmonicCorrection (n+1)*
        (chebyshevBiNullProducer (n+1)/Real.log (n+2 : ℕ)) := by
    funext n
    have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have hlog : 0 < Real.log (n+2 : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n+2 by omega))
    rw [factorialPolarLoss_eq]
    field_simp
  rw [he]
  convert (hε.mul harmonicCorrection_tendsto_half).mul
    chebyshevBiNullProducer_normalized_tendsto_half using 1
  norm_num

/-- The signed pole term appearing in the actual Weil diagonal has coefficient `-1/2`. -/
theorem factorialRamp_polarContribution_normalized_tendsto :
    Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)*
      (2*(∫ x in Ici (0 : ℝ), polarDensity x*autocorr (factorialRampSource n) x))/
        Real.log (n+2 : ℕ)) atTop (𝓝 (-1/2 : ℝ)) := by
  have he : (fun n : ℕ => ((n+1 : ℕ) : ℝ)*
      (2*(∫ x in Ici (0 : ℝ), polarDensity x*autocorr (factorialRampSource n) x))/
        Real.log (n+2 : ℕ)) =
      fun n => (-2 : ℝ)*(((n+1 : ℕ) : ℝ)*factorialPolarLoss n/Real.log (n+2 : ℕ)) := by
    funext n
    rw [factorialPolarLoss, abs_of_nonpos (integral_polar_autocorr_factorialRamp_nonpos n)]
    ring
  rw [he]
  convert factorialPolarLoss_normalized_tendsto_quarter.const_mul (-2 : ℝ) using 1
  norm_num

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
