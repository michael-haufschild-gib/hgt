import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment
import GaloisForLFunctions.RHTower.BoxFubini

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower.Sieve

/-- Duhamel transport in `L²`: integrating a continuously varying coefficient
field over a cell of length `H` costs one factor `H`, before integrating its
fixed-parameter mean square. -/
theorem integral_normSq_intervalIntegral_le_duhamel
    {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F))
    (hG : Continuous (fun t : ℝ => ∫ r in a..t, F r t)) :
    (∫ t in a..b, ‖∫ r in a..t, F r t‖ ^ 2) ≤
      (b - a) * ∫ r in a..b, ∫ t in a..b, ‖F r t‖ ^ 2 := by
  let R : ℝ → ℝ := fun t => ∫ r in a..b, ‖F r t‖ ^ 2
  have hswapCont : Continuous (Function.uncurry fun t r : ℝ => ‖F r t‖ ^ 2) := by
    exact (hF.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hRcont : Continuous R := by
    have hset := continuous_parametric_integral_of_continuous
      (μ := volume) (s := Set.Icc a b) hswapCont isCompact_Icc
    dsimp only [R]
    rw [show (fun t : ℝ => ∫ r in a..b, ‖F r t‖ ^ 2) =
        (fun t : ℝ => ∫ r in Set.Icc a b, ‖F r t‖ ^ 2) by
      funext t
      rw [intervalIntegral.integral_of_le hab,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]]
    exact hset
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖∫ r in a..t, F r t‖ ^ 2 ≤ (b - a) * R t := by
    intro t ht
    have hFt : Continuous (fun r : ℝ => F r t) :=
      hF.comp (continuous_id.prodMk continuous_const)
    have hnorm := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) ht.1
      (f := fun r : ℝ => F r t)
    have hcs :=
      GaloisForLFunctions.HTGeometry.integral_norm_le_sqrt_length_mul_sqrt_meanSquare
        hFt ht.1
    have hsub0 : 0 ≤ ∫ r in a..t, ‖F r t‖ ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall ht.1 fun _ => sq_nonneg _
    have hfull0 : 0 ≤ R t := by
      dsimp only [R]
      exact intervalIntegral.integral_nonneg_of_forall hab fun _ => sq_nonneg _
    have hsub : (∫ r in a..t, ‖F r t‖ ^ 2) ≤ R t := by
      dsimp only [R]
      exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        ((hFt.norm.pow 2).intervalIntegrable a b)
    have hlen0 : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hlen : t - a ≤ b - a := sub_le_sub_right ht.2 a
    calc
      ‖∫ r in a..t, F r t‖ ^ 2
          ≤ (∫ r in a..t, ‖F r t‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ (Real.sqrt (t - a) *
          Real.sqrt (∫ r in a..t, ‖F r t‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀
              (intervalIntegral.integral_nonneg_of_forall ht.1 fun _ => norm_nonneg _)
              hcs 2
      _ = (t - a) * (∫ r in a..t, ‖F r t‖ ^ 2) := by
            rw [mul_pow, Real.sq_sqrt hlen0, Real.sq_sqrt hsub0]
      _ ≤ (b - a) * R t :=
        mul_le_mul hlen hsub hsub0 (by linarith)
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume)
    (f := fun t : ℝ => ‖∫ r in a..t, F r t‖ ^ 2)
    (g := fun t : ℝ => (b - a) * R t)
    hab
    ((hG.norm.pow 2).intervalIntegrable a b)
    ((continuous_const.mul hRcont).intervalIntegrable a b)
    hpoint
  refine hmono.trans_eq ?_
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact RHTower.interval_integral_swap_of_continuous hab hab
    hswapCont

end RHTower.Sieve
