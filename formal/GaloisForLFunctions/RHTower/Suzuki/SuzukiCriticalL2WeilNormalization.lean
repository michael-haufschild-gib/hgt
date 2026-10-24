import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2Energy
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalWeilNormalization
import GaloisForLFunctions.«arithmetic-positivity-theory».CollaredCriticalArchimedeanLogCoercivity

/-!
# Extended Weil normalization on the L² source domain

The complete nonnegative Lévy energy differs from the primary tangent by an
integrable exponential tail. Splitting that positive integral before applying
the Gamma recurrence retains infinite energies without subtracting infinities.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped ENNReal
open GaloisForLFunctions.ArithmeticPositivityTheory GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm


namespace RHTower
noncomputable section

private theorem source_autocorr_eq (f : ℝ → ℝ) (t : ℝ) :
    sourceAutocorrelation f t = autocorr f t := by
  rw [← autocorr_neg]
  unfold sourceAutocorrelation autocorr
  simp only [sub_eq_add_neg]

private theorem tangent_add_decay {t : ℝ} (ht : 0 < t) :
    archLevySinhWeight t =
      2 * Real.exp (-(5/2 : ℝ)*t) / (1-Real.exp (-2*t)) + 2*Real.exp (-t/2) := by
  rw [archLevySinhWeight, exp_half_div_sinh_eq ht, archLevyDensity]
  rw [← mul_div_assoc]
  have he : Real.exp (-(5/2 : ℝ)*t) = Real.exp (-t/2)*Real.exp (-2*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hd : 1-Real.exp (-2*t) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  rw [he]
  apply (div_eq_iff hd).mpr
  rw [add_mul, div_mul_cancel₀ _ hd]
  ring

private theorem decay_integrable :
    IntegrableOn (fun t : ℝ => Real.exp (-t/2)) (Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ)<0) (0 : ℝ)
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  change Real.exp ((-1/2)*t) = Real.exp (-t/2)
  congr 1
  ring

private theorem decay_integral : (∫ t in Ioi (0 : ℝ), Real.exp (-t/2)) = 2 := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), Real.exp ((-1/2)*t) := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      ring
    _ = 2 := by
      simpa using integral_exp_mul_Ioi (by norm_num : (-1/2 : ℝ)<0) (0 : ℝ)

private theorem correlation_decay_integrable {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    IntegrableOn (fun t => autocorr f t * Real.exp (-t/2)) (Ioi 0) := by
  apply decay_integrable.bdd_mul (continuous_autocorr_of_memLp hf).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [Real.norm_eq_abs] using abs_autocorr_le_zero_of_memLp hf t

private theorem deficit_decay_integrable {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    IntegrableOn (fun t => (autocorr f 0-autocorr f t)*(2*Real.exp (-t/2))) (Ioi 0) := by
  have hi : IntegrableOn (fun t => (2*autocorr f 0)*Real.exp (-t/2) -
      2*(autocorr f t*Real.exp (-t/2))) (Ioi 0) :=
    (decay_integrable.const_mul (2*autocorr f 0)).sub
      ((correlation_decay_integrable hf).const_mul 2)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  dsimp only [Pi.sub_apply]
  ring

private theorem deficit_decay_integral {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    (∫ t in Ioi 0, (autocorr f 0-autocorr f t)*(2*Real.exp (-t/2))) =
      4*autocorr f 0-2*∫ t in Ioi 0, autocorr f t * Real.exp (-t/2) := by
  have he : (fun t => (autocorr f 0-autocorr f t)*(2*Real.exp (-t/2))) =
      fun t => (2*autocorr f 0)*Real.exp (-t/2) - 2*(autocorr f t * Real.exp (-t/2)) := by
    funext t
    ring
  rw [he, integral_sub (decay_integrable.const_mul _) ((correlation_decay_integrable hf).const_mul _),
    integral_const_mul, integral_const_mul, decay_integral]
  ring

/-- The full extended Lévy energy is the primary energy plus its finite positive tail. -/
theorem sourceLevyEnergy_eq_suzukiCriticalEnergy {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    sourceLevyEnergy f = suzukiCriticalLimitingCompensatedEnergy
      (fun t => autocorr f 0-autocorr f t) +
        ENNReal.ofReal (4*autocorr f 0-2*∫ t in Ioi 0, autocorr f t * Real.exp (-t/2)) := by
  have hDm : Measurable (fun t => autocorr f 0-autocorr f t) :=
    measurable_const.sub (continuous_autocorr_of_memLp hf).measurable
  have hK : Measurable (fun t : ℝ => ENNReal.ofReal ((autocorr f 0-autocorr f t) *
      (2*Real.exp (-(5/2 : ℝ)*t)/(1-Real.exp (-2*t))))) :=
    (hDm.mul (by fun_prop)).ennreal_ofReal
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ (autocorr f 0-autocorr f t)*(2*Real.exp (-t/2)) :=
    Eventually.of_forall fun t => mul_nonneg (AutocorrelationKrein.deficit_nonneg hf t) (by positivity)
  calc
    _ = ∫⁻ t in Ioi 0, ENNReal.ofReal ((autocorr f 0-autocorr f t) *
        (2*Real.exp (-(5/2 : ℝ)*t)/(1-Real.exp (-2*t)))) +
        ENNReal.ofReal ((autocorr f 0-autocorr f t)*(2*Real.exp (-t/2))) := by
      unfold sourceLevyEnergy
      simp only [source_autocorr_eq]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0 < t at ht
      have hD := AutocorrelationKrein.deficit_nonneg hf t
      have hd : 0 < 1-Real.exp (-2*t) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      rw [tangent_add_decay ht, mul_add, ENNReal.ofReal_add
        (mul_nonneg hD (by positivity)) (mul_nonneg hD (by positivity))]
    _ = suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr f 0-autocorr f t) +
        ∫⁻ t in Ioi 0, ENNReal.ofReal ((autocorr f 0-autocorr f t)*(2*Real.exp (-t/2))) := by
      rw [lintegral_add_left hK]
      rfl
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (deficit_decay_integrable hf) hnn,
        deficit_decay_integral hf]

/-- The positive tail splitting remains exact in the extended reals. -/
theorem coe_sourceLevyEnergy_eq_suzukiCriticalEnergy {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    (sourceLevyEnergy f : EReal) =
      (suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr f 0-autocorr f t) : EReal) +
        ((4*autocorr f 0-2*∫ t in Ioi 0, autocorr f t * Real.exp (-t/2) : ℝ) : EReal) := by
  have hnn : 0 ≤ 4*autocorr f 0-2*∫ t in Ioi 0, autocorr f t * Real.exp (-t/2) := by
    rw [← deficit_decay_integral hf]
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun t => mul_nonneg (AutocorrelationKrein.deficit_nonneg hf t)
      (by positivity)
  rw [sourceLevyEnergy_eq_suzukiCriticalEnergy hf, EReal.coe_ennreal_add,
    EReal.coe_ennreal_ofReal, max_eq_left hnn]

private theorem digamma_shift :
    (Complex.digamma ((5/4 : ℝ) : ℂ)).re = (Complex.digamma ((1/4 : ℝ) : ℂ)).re + 4 := by
  have hp : ∀ n : ℕ, ((1/4 : ℝ) : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := congrArg Complex.re (Complex.digamma_apply_add_one ((1/4 : ℝ) : ℂ) hp)
  norm_num at h ⊢
  exact h

/-- The Gamma recurrence combines the primary tangent and growing pole into the full Weil form. -/
theorem suzukiCriticalL2Weil_normalization {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) :
    (suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr f 0-autocorr f t) : EReal) +
      ((((Complex.digamma ((5/4 : ℝ) : ℂ)).re-Real.log Real.pi)*autocorr f 0 +
        2*∫ t in Ioi 0, autocorr f t * Real.exp (t/2) : ℝ) : EReal) =
      (sourceLevyEnergy f : EReal) +
        ((EF.gammaBracket 0 * autocorr f 0 +
          4*∫ t in Ioi 0, autocorr f t * Real.cosh (t/2) : ℝ) : EReal) := by
  have hp : IntegrableOn (fun t => autocorr f t * Real.exp (t/2)) (Ioi 0) := by
    have hc : Continuous (fun t => autocorr f t * Real.exp (t/2)) :=
      (continuous_autocorr_of_memLp hf).mul (by fun_prop)
    exact (hc.integrable_of_hasCompactSupport (hasCompactSupport_autocorr hfc).mul_right).integrableOn
  have hm := correlation_decay_integrable hf
  have hpolar : 4*(∫ t in Ioi 0, autocorr f t * Real.cosh (t/2)) =
      2*(∫ t in Ioi 0, autocorr f t * Real.exp (t/2)) +
      2*(∫ t in Ioi 0, autocorr f t * Real.exp (-t/2)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hp.const_mul 2) (hm.const_mul 2)]
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.cosh_eq, neg_div]
    ring
  have hg := gammaBracket_eq_re_digamma 0
  simp only [zero_div, Complex.ofReal_zero, zero_mul, add_zero] at hg
  rw [coe_sourceLevyEnergy_eq_suzukiCriticalEnergy hf, add_assoc, ← EReal.coe_add]
  congr 1
  congr 1
  rw [hpolar, digamma_shift, hg]
  ring

end
end RHTower
