import GaloisForLFunctions.BiScaleUncertainty.FactorialWeilGram
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Unconditional decay of the full signed factorial ramp–tent mixed coefficient. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def factorialWeilMixedBound (n : ℕ) : ℝ :=
  (36*Real.log ((n+1 : ℕ) : ℝ)+26*Real.log 5+14+2*Real.log (1000000 : ℝ))/
    Real.sqrt (n+1 : ℕ)

def factorialWeilGramError (n : ℕ) : ℝ :=
  (factorialWeilMixedBound n)^2/(2*((n+1 : ℕ) : ℝ))

private theorem mixed_raw_bound (n : ℕ) :
    |factorialWeilMixed n| ≤ factorialSourceJumpError n+
      2*((10*Real.log (4*((n+1 : ℕ) : ℝ)+1)+3+1/(4*((n+1 : ℕ) : ℝ)))/Real.sqrt (n+1 : ℕ)) := by
  unfold factorialWeilMixed
  calc
    _ ≤ |-(∫ x in Ioi (0 : ℝ), sourceFactorialCausal (n+1) x*archLevySinhWeight x)|+
        |2*fullPairing (sourceFactorialCausal (n+1))| := abs_sub _ _
    _ = |∫ x in Ioi (0 : ℝ), sourceFactorialCausal (n+1) x*archLevySinhWeight x|+
        2*|fullPairing (sourceFactorialCausal (n+1))| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ _ := add_le_add (abs_integral_sourceFactorialCausal_archWeight_le n)
      (mul_le_mul_of_nonneg_left (abs_fullPairing_sourceFactorialCausal_le (by omega : 1 ≤ n+1))
        (by norm_num))

theorem factorialWeilMixed_abs_le (n : ℕ) :
    |factorialWeilMixed n| ≤ factorialWeilMixedBound n := by
  have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have hnp : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hlog : Real.log (4*((n+1 : ℕ) : ℝ)+1) ≤ Real.log 5+Real.log ((n+1 : ℕ) : ℝ) := by
    calc
      _ ≤ Real.log (5*((n+1 : ℕ) : ℝ)) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := Real.log_mul (by norm_num) hnp.ne'
  have hQ : Real.log (factorialJumpScale (n+1)) =
      Real.log (1000000 : ℝ)+5*Real.log ((n+1 : ℕ) : ℝ) := by
    rw [factorialJumpScale, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hsmall : 1/(4*((n+1 : ℕ) : ℝ)) ≤ 1/2 :=
    (div_le_iff₀ (by positivity)).2 (by linarith)
  refine (mixed_raw_bound n).trans ?_
  calc
    _ = (26*Real.log (4*((n+1 : ℕ) : ℝ)+1)+10*Real.log ((n+1 : ℕ) : ℝ)+
        13+2*Real.log (1000000 : ℝ)+2*(1/(4*((n+1 : ℕ) : ℝ))))/Real.sqrt (n+1 : ℕ) := by
      unfold factorialSourceJumpError
      rw [hQ]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith)
      (Real.sqrt_nonneg _)

theorem factorialWeilMixedBound_tendsto :
    Tendsto factorialWeilMixedBound atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hl : Tendsto (fun n : ℕ => Real.log ((n+1 : ℕ) : ℝ)/Real.sqrt (n+1 : ℕ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero.comp hn
  have hi : Tendsto (fun n : ℕ => 1/Real.sqrt (n+1 : ℕ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow, one_div] using
      tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hn)
  have he : factorialWeilMixedBound = fun n : ℕ =>
      36*(Real.log ((n+1 : ℕ) : ℝ)/Real.sqrt (n+1 : ℕ))+
      (26*Real.log 5+14+2*Real.log (1000000 : ℝ))*(1/Real.sqrt (n+1 : ℕ)) := by
    funext n
    unfold factorialWeilMixedBound
    ring
  rw [he]
  simpa using (hl.const_mul 36).add (hi.const_mul (26*Real.log 5+14+2*Real.log (1000000 : ℝ)))

theorem factorialWeilMixed_tendsto : Tendsto factorialWeilMixed atTop (𝓝 0) :=
  squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using factorialWeilMixed_abs_le n)
    factorialWeilMixedBound_tendsto

theorem factorialWeilGramError_tendsto : Tendsto factorialWeilGramError atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun n : ℕ => (factorialWeilMixedBound n)^2) ?_
    (by simpa using factorialWeilMixedBound_tendsto.pow 2)
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold factorialWeilGramError; positivity)]
  unfold factorialWeilGramError
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*((n+1 : ℕ) : ℝ))).2
  have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  nlinarith [mul_nonneg (sq_nonneg (factorialWeilMixedBound n))
    (show 0 ≤ 2*((n+1 : ℕ) : ℝ)-1 by linarith)]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
