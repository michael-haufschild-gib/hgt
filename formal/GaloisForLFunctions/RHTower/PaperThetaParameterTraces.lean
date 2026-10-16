import GaloisForLFunctions.RHTower.PaperThetaParameterVariation

/-! # Native traces and continuity of spectral jets

The common variation budget is itself the modulus of one literal imaginary
parameter mode. Its known source-end trace pays all differentiated traces.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmQuantile ThetaFiniteTransport

theorem parameterVariationBudget_eq (z : ℂ) (x : ℝ) :
    parameterVariationBudget z x = (‖z‖+1)/(|z.im|+1) *
      ‖flatQuotient (-I*((|z.im|+1 : ℝ) : ℂ)) x+1‖ := by
  let b := |z.im|+1
  have hb : 0 < b := by dsimp [b]; positivity
  have hchar (h : ℝ) : sourceChar (-I*(b : ℂ)) h = (Real.exp (b*h) : ℂ) := by
    rw [sourceChar]
    have he : I*(-I*(b : ℂ))*(h : ℂ) = ((b*h : ℝ) : ℂ) := by
      push_cast
      calc
        _ = -(I*I)*((b : ℂ)*(h : ℂ)) := by ring
        _ = _ := by rw [I_mul_I]; ring
    rw [he, Complex.ofReal_exp]
  have hi : (∫ h in Ioi (0 : ℝ), (sourceRatio h x : ℂ)*sourceChar (-I*(b : ℂ)) h) =
      ((∫ h in Ioi (0 : ℝ), sourceRatio h x*Real.exp (b*h) : ℝ) : ℂ) := by
    calc
      _ = ∫ h in Ioi (0 : ℝ), ((sourceRatio h x*Real.exp (b*h) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with h
        rw [hchar]
        push_cast
        rfl
      _ = _ := integral_ofReal
  have hp : 0 ≤ ∫ h in Ioi (0 : ℝ), sourceRatio h x*Real.exp (b*h) :=
    integral_nonneg fun h => mul_nonneg (sourceRatio_pos h x).le (Real.exp_pos _).le
  have he : I*(-I*(b : ℂ)) = (b : ℂ) := by rw [← mul_assoc]; simp
  have hn : ‖flatQuotient (-I*(b : ℂ)) x+1‖ =
      b * ∫ h in Ioi (0 : ℝ), sourceRatio h x*Real.exp (b*h) := by
    rw [flatQuotient_eq_sourceRatio_integral, hi, he, norm_mul, norm_neg,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hb, abs_of_nonneg hp]
  change (‖z‖+1) * (∫ h in Ioi (0 : ℝ), sourceRatio h x*Real.exp (b*h)) =
    (‖z‖+1)/b * ‖flatQuotient (-I*(b : ℂ)) x+1‖
  rw [hn]
  field_simp [hb.ne']

theorem continuous_parameterVariationBudget (z : ℂ) :
    Continuous (parameterVariationBudget z) := by
  have he : parameterVariationBudget z = fun x => (‖z‖+1)/(|z.im|+1) *
      ‖flatQuotient (-I*((|z.im|+1 : ℝ) : ℂ)) x+1‖ := funext (parameterVariationBudget_eq z)
  rw [he]
  exact (((continuous_flatQuotient _).add continuous_const).norm).const_mul _

theorem tendsto_parameterVariationBudget_atTop (z : ℂ) :
    Tendsto (parameterVariationBudget z) atTop (𝓝 0) := by
  have he : parameterVariationBudget z = fun x => (‖z‖+1)/(|z.im|+1) *
      ‖flatQuotient (-I*((|z.im|+1 : ℝ) : ℂ)) x+1‖ := funext (parameterVariationBudget_eq z)
  rw [he]
  have h := (((tendsto_flatQuotient_atTop (-I*((|z.im|+1 : ℝ) : ℂ))).add
    (tendsto_const_nhds (x := (1 : ℂ)))).norm).const_mul ((‖z‖+1)/(|z.im|+1))
  simpa only [neg_add_cancel, norm_zero, mul_zero] using h

theorem flatParameterJet_increment_abs (n : ℕ) (z : ℂ) (a b : ℝ) :
    ‖flatParameterJet n z b-flatParameterJet n z a‖ ≤
      (n.factorial : ℝ)*|parameterVariationBudget z b-parameterVariationBudget z a| := by
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonpos (sub_nonpos.mpr (parameterVariationBudget_antitone z hab)),
      neg_sub] using flatParameterJet_increment n z hab
  · rw [norm_sub_rev, abs_of_nonneg (sub_nonneg.mpr (parameterVariationBudget_antitone z hba))]
    exact flatParameterJet_increment n z hba

theorem continuous_flatParameterJet (n : ℕ) (z : ℂ) :
    Continuous (flatParameterJet n z) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb0 : Tendsto (fun y => (n.factorial : ℝ)*
      |parameterVariationBudget z y-parameterVariationBudget z x|) (𝓝 x) (𝓝 0) := by
    have hb := (((continuous_parameterVariationBudget z).continuousAt (x := x)).tendsto.sub
      (tendsto_const_nhds (x := parameterVariationBudget z x))).abs.const_mul (n.factorial : ℝ)
    simpa only [sub_self, abs_zero, mul_zero] using hb
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun y => flatParameterJet_increment_abs n z x y) hb0

theorem flatQuotient_add_one_parameter_circle (z : ℂ) (x : ℝ)
    {w : ℂ} (hw : w ∈ Metric.sphere z 1) :
    ‖flatQuotient w x+1‖ ≤ parameterVariationBudget z x := by
  have hd : ‖w-z‖ = 1 := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
  have hnw : ‖w‖ ≤ ‖z‖+1 := by
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel, hd] at ht
    simpa only [add_comm] using ht
  have him : -w.im ≤ |z.im|+1 := by
    have hh := Complex.abs_im_le_norm (w-z)
    rw [Complex.sub_im, hd] at hh
    have hz := neg_abs_le z.im
    have hwz := neg_abs_le (w.im-z.im)
    linarith
  rw [flatQuotient_eq_sourceRatio_integral, norm_mul, norm_neg, norm_mul, norm_I, one_mul]
  apply mul_le_mul hnw _ (norm_nonneg _) (by positivity)
  apply norm_integral_le_of_norm_le (integrable_sourceRatio_tilt (|z.im|+1) x).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [norm_sourceRatio_character]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right him hh.le)) (sourceRatio_pos h x).le

theorem norm_flatParameterJet_sub_trace_le (n : ℕ) (z : ℂ) (x : ℝ) :
    ‖flatParameterJet n z x-(if n = 0 then -1 else 0)‖ ≤
      (n.factorial : ℝ)*parameterVariationBudget z x := by
  have hf : Differentiable ℂ (fun w => (1 : ℂ)+flatQuotient w x) :=
    (differentiable_const _).add (differentiable_flatQuotient_parameter x)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n (R := 1) one_pos hf.diffContOnCl
    (fun w hw => by simpa only [add_comm] using flatQuotient_add_one_parameter_circle z x hw)
  have he : iteratedDeriv n (fun w => (1 : ℂ)+flatQuotient w x) z =
      flatParameterJet n z x-(if n = 0 then -1 else 0) := by
    cases n with
    | zero => simp [flatParameterJet, add_comm]
    | succ n => rw [iteratedDeriv_const_add (Nat.succ_pos n)]; simp [flatParameterJet]
  rw [he] at h
  simpa only [one_pow, div_one] using h

/-- Every positive-order jet has zero at the native right end. -/
theorem tendsto_flatParameterJet_succ_atTop (n : ℕ) (z : ℂ) :
    Tendsto (flatParameterJet (n+1) z) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb (x : ℝ) : ‖flatParameterJet (n+1) z x‖ ≤
      ((n+1).factorial : ℝ)*parameterVariationBudget z x := by
    simpa only [Nat.add_one_ne_zero, if_false, sub_zero] using
      norm_flatParameterJet_sub_trace_le (n+1) z x
  have hlim := (tendsto_parameterVariationBudget_atTop z).const_mul ((n+1).factorial : ℝ)
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall hb) (by simpa only [mul_zero] using hlim)

end RHTower.PaperThetaEndpoint
