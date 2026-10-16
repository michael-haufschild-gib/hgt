import GaloisForLFunctions.RHTower.PaperThetaParameterAnalytic
import GaloisForLFunctions.RHTower.PaperThetaBoundedVariation

/-! # Native variation of every spectral parameter jet

One decreasing source budget controls an entire parameter circle. Cauchy's
formula can therefore be applied to increments before the spatial partition
is summed. This pays parameter differentiation in the original BV domain.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmQuantile ThetaFiniteTransport

def parameterVariationBudget (z : ℂ) (x : ℝ) : ℝ :=
  (‖z‖+1) * ∫ h in Ioi (0 : ℝ), sourceRatio h x * Real.exp ((|z.im|+1)*h)

def flatParameterJet (n : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  iteratedDeriv n (fun w => flatQuotient w x) z

theorem parameterVariationBudget_nonneg (z : ℂ) (x : ℝ) :
    0 ≤ parameterVariationBudget z x := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun h => mul_nonneg (sourceRatio_pos h x).le (Real.exp_pos _).le

theorem parameterVariationBudget_antitone (z : ℂ) :
    Antitone (parameterVariationBudget z) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply setIntegral_mono_on (integrable_sourceRatio_tilt (|z.im|+1) b).integrableOn
    (integrable_sourceRatio_tilt (|z.im|+1) a).integrableOn measurableSet_Ioi
  intro h hh
  exact mul_le_mul_of_nonneg_right (sourceRatio_antitone_all ⟨h, hh.le⟩ hab)
    (Real.exp_pos _).le

theorem flatQuotient_increment_parameter_circle (z : ℂ) {a b : ℝ} (hab : a ≤ b)
    {w : ℂ} (hw : w ∈ Metric.sphere z 1) :
    ‖flatQuotient w b-flatQuotient w a‖ ≤
      parameterVariationBudget z a-parameterVariationBudget z b := by
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
  have hdiff : flatQuotient w b-flatQuotient w a = (I*w) *
      ∫ h in Ioi (0 : ℝ), ((sourceRatio h a : ℂ)-sourceRatio h b)*sourceChar w h := by
    rw [show (fun h : ℝ => ((sourceRatio h a : ℂ)-sourceRatio h b)*sourceChar w h) =
      (fun h => (sourceRatio h a : ℂ)*sourceChar w h-
        (sourceRatio h b : ℂ)*sourceChar w h) by funext h; ring,
      integral_sub (integrable_sourceRatio_character w a).integrableOn
        (integrable_sourceRatio_character w b).integrableOn]
    linear_combination flatQuotient_eq_sourceRatio_integral w b -
      flatQuotient_eq_sourceRatio_integral w a
  let B := |z.im|+1
  have hi : IntegrableOn (fun h : ℝ =>
      (sourceRatio h a-sourceRatio h b)*Real.exp (B*h)) (Ioi 0) := by
    exact ((integrable_sourceRatio_tilt B a).sub
      (integrable_sourceRatio_tilt B b)).integrableOn.congr (Eventually.of_forall fun h => by
        change sourceRatio h a*Real.exp (B*h)-sourceRatio h b*Real.exp (B*h) = _
        ring)
  have hb : ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)),
      ‖((sourceRatio h a : ℂ)-sourceRatio h b)*sourceChar w h‖ ≤
        (sourceRatio h a-sourceRatio h b)*Real.exp (B*h) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hmono : sourceRatio h b ≤ sourceRatio h a := sourceRatio_antitone_all ⟨h, hh.le⟩ hab
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hmono), norm_sourceChar]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right him hh.le)) (sub_nonneg.mpr hmono)
  calc
    _ = ‖w‖ * ‖∫ h in Ioi (0 : ℝ),
        ((sourceRatio h a : ℂ)-sourceRatio h b)*sourceChar w h‖ := by
      rw [hdiff, norm_mul, norm_mul, norm_I, one_mul]
    _ ≤ (‖z‖+1) * ∫ h in Ioi (0 : ℝ),
        (sourceRatio h a-sourceRatio h b)*Real.exp (B*h) :=
      mul_le_mul hnw (norm_integral_le_of_norm_le hi hb) (norm_nonneg _) (by positivity)
    _ = _ := by
      simp_rw [sub_mul]
      rw [integral_sub (integrable_sourceRatio_tilt B a).integrableOn
        (integrable_sourceRatio_tilt B b).integrableOn]
      unfold parameterVariationBudget
      dsimp [B]
      ring

theorem flatParameterJet_increment (n : ℕ) (z : ℂ) {a b : ℝ} (hab : a ≤ b) :
    ‖flatParameterJet n z b-flatParameterJet n z a‖ ≤
      (n.factorial : ℝ)*(parameterVariationBudget z a-parameterVariationBudget z b) := by
  have hf := (differentiable_flatQuotient_parameter b).sub
    (differentiable_flatQuotient_parameter a)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n (R := 1) one_pos hf.diffContOnCl
    (fun _ hw => flatQuotient_increment_parameter_circle z hab hw)
  rw [iteratedDeriv_sub
    ((differentiable_flatQuotient_parameter b).analyticAt z).contDiffAt
    ((differentiable_flatQuotient_parameter a).analyticAt z).contDiffAt] at h
  simpa only [flatParameterJet, one_pow, div_one] using h

/-- Every parameter order is admitted on every native right ray. -/
theorem boundedVariationOn_flatParameterJet_Ici (n : ℕ) (z : ℂ) (A : ℝ) :
    BoundedVariationOn (flatParameterJet n z) (Ici A) := by
  apply ne_top_of_le_ne_top (b := ENNReal.ofReal
    ((n.factorial : ℝ)*parameterVariationBudget z A)) (by finiteness)
  apply iSup_le
  rintro ⟨N, ⟨u, hu, us⟩⟩
  have hdec (i : ℕ) := parameterVariationBudget_antitone z (hu (Nat.le_succ i))
  calc
    (∑ i ∈ Finset.range N, edist (flatParameterJet n z (u (i+1)))
        (flatParameterJet n z (u i))) ≤
      ∑ i ∈ Finset.range N, ENNReal.ofReal ((n.factorial : ℝ)*
        (parameterVariationBudget z (u i)-parameterVariationBudget z (u (i+1)))) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [edist_dist, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal (flatParameterJet_increment n z (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal ((n.factorial : ℝ)*
        (parameterVariationBudget z (u 0)-parameterVariationBudget z (u N))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ Finset.range N) =>
        show 0 ≤ (n.factorial : ℝ)*(parameterVariationBudget z (u i)-
          parameterVariationBudget z (u (i+1))) from
            mul_nonneg (by positivity) (sub_nonneg.mpr (hdec i))), ← Finset.mul_sum]
      have ht := Finset.sum_range_sub (fun i => -parameterVariationBudget z (u i)) N
      rw [show (∑ i ∈ Finset.range N, (parameterVariationBudget z (u i)-
        parameterVariationBudget z (u (i+1)))) =
          parameterVariationBudget z (u 0)-parameterVariationBudget z (u N) by
            simpa only [neg_sub_neg] using ht]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      ((sub_le_self _ (parameterVariationBudget_nonneg z _)).trans
        (parameterVariationBudget_antitone z (us 0))) (by positivity))

end RHTower.PaperThetaEndpoint
