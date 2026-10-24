import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalBetaKernel
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalLogKernel
import GaloisForLFunctions.RHTower.ThetaBVArithmeticAdmission

/-!
# The pointwise critical limit of the causal Suzuki pole

The first displacement moment of the positive primary density tends to zero.
Its exact pole convolution is a truncated exponential average; the discarded
mass is bounded by that first moment. This gives the growing pole limit and
an explicit local majorant before choosing any test source.
-/

open MeasureTheory Set Filter Topology


namespace RHTower
noncomputable section

/-- The causal triangle integral is measurable in its endpoint. -/
theorem measurable_suzukiCriticalPoleDensity (omega : ℝ) :
    Measurable (suzukiCriticalPoleDensity omega) := by
  let F : ℝ × ℝ → ℝ := fun p => if 0 < p.2 ∧ p.2 < p.1 then
    suzukiCriticalPrimaryDensity omega p.2 * Real.exp ((1/2-omega)*(p.1-p.2)) else 0
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hm : Measurable F := Measurable.ite hset
    (((measurable_suzukiCriticalPrimaryDensity omega).comp measurable_snd).mul
      (by fun_prop)) measurable_const
  have he (t : ℝ) : suzukiCriticalPoleDensity omega t = ∫ r, F (t,r) := by
    rw [suzukiCriticalPoleDensity, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [F]
    by_cases hr : r ∈ Ioo (0 : ℝ) t
    · rw [indicator_of_mem hr, if_pos (show 0 < r ∧ r < t from hr)]
    · rw [indicator_of_notMem hr, if_neg (show ¬ (0 < r ∧ r < t) from hr)]
  rw [show suzukiCriticalPoleDensity omega = (fun t => ∫ r, F (t,r)) from funext he]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The causal pole vanishes at nonpositive logarithmic arguments. -/
theorem suzukiCriticalPoleDensity_eq_zero_of_nonpos {omega t : ℝ} (ht : t ≤ 0) :
    suzukiCriticalPoleDensity omega t = 0 := by
  rw [suzukiCriticalPoleDensity, Ioo_eq_empty_of_le ht]
  simp

/-- The literal signed source vanishes outside the positive logarithmic ray. -/
theorem suzukiCriticalSourceDensity_eq_zero_of_nonpos {omega t : ℝ} (ht : t ≤ 0) :
    suzukiCriticalSourceDensity omega t = 0 := by
  unfold suzukiCriticalSourceDensity suzukiSourceG
  have he : 1 ≤ Real.exp (-t) := Real.one_le_exp_iff.mpr (by linarith)
  rw [if_neg (fun h => (not_lt_of_ge he) h.2)]
  simp

private theorem firstMoment_levy_integrable :
    IntegrableOn (fun t : ℝ => t *
      (2 * Real.exp (-t/2) / (1-Real.exp (-2*t)))) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => 2*(t*archLevyDensity t)) (Ioi 0) :=
    CHMDDoobGraph.integrable_archLevy_firstMoment.const_mul 2
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  dsimp only
  unfold archLevyDensity
  ring

/-- First displacement moment of the literal positive primary density. -/
def suzukiCriticalPrimaryFirstMoment (omega : ℝ) : ℝ :=
  ∫ t in Ioi 0, t * suzukiCriticalPrimaryDensity omega t

/-- The first displacement moment is finite at every positive shift at most two. -/
theorem integrableOn_suzukiCriticalPrimaryFirstMoment {omega : ℝ} (homega : 0 < omega)
    (homega2 : omega ≤ 2) :
    IntegrableOn (fun t : ℝ => t * suzukiCriticalPrimaryDensity omega t) (Ioi 0) := by
  apply (firstMoment_levy_integrable.const_mul
    (omega*suzukiCriticalPrimaryScale omega)).mono'
      (measurable_id.mul (measurable_suzukiCriticalPrimaryDensity omega)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  dsimp only [Pi.mul_apply, id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.le
    (suzukiCriticalPrimaryDensity_pos homega ht).le)]
  have hb := (div_le_iff₀ homega).mp
    (suzukiCriticalPrimaryDensity_div_le homega homega2 ht)
  calc
    _ ≤ t * (suzukiCriticalPrimaryScale omega *
        (2 * Real.exp (-t/2) / (1-Real.exp (-2*t))) * omega) :=
      mul_le_mul_of_nonneg_left hb ht.le
    _ = _ := by ring

/-- The primary mass concentrates at the origin in first moment. -/
theorem tendsto_suzukiCriticalPrimaryFirstMoment :
    Tendsto suzukiCriticalPrimaryFirstMoment (𝓝[>] 0) (𝓝 0) := by
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ t :=
    (ae_restrict_mem measurableSet_Ioi).mono fun _ ht => ht.le
  have hlim := tendsto_integral_compensated_suzukiCriticalPrimaryDensity
    measurable_id.aestronglyMeasurable hnn firstMoment_levy_integrable
  have hi : Tendsto (fun omega : ℝ => omega) (𝓝[>] 0) (𝓝 0) := continuousWithinAt_id
  have h := hlim.mul hi
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with omega homega
  change 0 < omega at homega
  rw [suzukiCriticalPrimaryFirstMoment, ← integral_mul_const]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only [id_eq]
    field_simp [ne_of_gt homega]

private def poleWeight (omega t : ℝ) : ℝ → ℝ :=
  (Iio t).indicator (fun r => Real.exp (-(1/2-omega)*r))

private theorem poleWeight_measurable (omega t : ℝ) : Measurable (poleWeight omega t) :=
  (show Measurable (fun r : ℝ => Real.exp (-(1/2-omega)*r)) by fun_prop).indicator measurableSet_Iio

private theorem poleWeight_bounds {omega t r : ℝ}
    (homega2 : omega ≤ 1/2) (hr : 0 < r) :
    0 ≤ poleWeight omega t r ∧ poleWeight omega t r ≤ 1 := by
  by_cases hrt : r < t
  · rw [poleWeight, indicator_of_mem (show r ∈ Iio t from hrt)]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) hr.le)⟩
  · rw [poleWeight, indicator_of_notMem (show r ∉ Iio t from hrt)]
    exact ⟨le_refl 0, zero_le_one⟩

private theorem poleWeight_deficit_le {omega t r : ℝ} (homega : 0 < omega)
    (ht : 0 < t) (hr : 0 < r) :
    1-poleWeight omega t r ≤ (1+1/t)*r := by
  by_cases hrt : r < t
  · rw [poleWeight, indicator_of_mem (show r ∈ Iio t from hrt)]
    have he := Real.add_one_le_exp (-(1/2-omega)*r)
    have hwr : 0 ≤ omega*r := mul_nonneg homega.le hr.le
    have htr : 0 ≤ r/t := div_nonneg hr.le ht.le
    have hmul : (1+1/t)*r = r+r/t := by ring
    rw [hmul]
    nlinarith only [he, hwr, htr, hr]
  · rw [poleWeight, indicator_of_notMem (show r ∉ Iio t from hrt)]
    have htr : 1 ≤ r/t := (le_div_iff₀ ht).mpr (by simpa using le_of_not_gt hrt)
    have hmul : (1+1/t)*r = r+r/t := by ring
    rw [hmul]
    linarith only [htr, hr]

private def poleMass (omega t : ℝ) : ℝ :=
  ∫ r in Ioi 0, poleWeight omega t r * suzukiCriticalPrimaryDensity omega r

private theorem poleMass_integrable {omega : ℝ} (homega : 0 < omega)
    (homega2 : omega ≤ 1/2) (t : ℝ) :
    IntegrableOn (fun r => poleWeight omega t r * suzukiCriticalPrimaryDensity omega r)
      (Ioi 0) := by
  apply (integrableOn_suzukiCriticalPrimaryDensity homega (by linarith)).bdd_mul
    (poleWeight_measurable omega t).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hw := poleWeight_bounds (t := t) homega2 hr
  simpa only [Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2

private theorem poleDensity_eq_exp_mul_mass (omega t : ℝ) :
    suzukiCriticalPoleDensity omega t = Real.exp ((1/2-omega)*t) * poleMass omega t := by
  have hwindow : poleMass omega t =
      ∫ r in Ioo 0 t, Real.exp (-(1/2-omega)*r) * suzukiCriticalPrimaryDensity omega r := by
    have he : (fun r => poleWeight omega t r * suzukiCriticalPrimaryDensity omega r) =
        (Iio t).indicator (fun r => Real.exp (-(1/2-omega)*r) * suzukiCriticalPrimaryDensity omega r) := by
      funext r
      by_cases hr : r ∈ Iio t
      · simp only [poleWeight, indicator_of_mem hr]
      · simp only [poleWeight, indicator_of_notMem hr, zero_mul]
    rw [poleMass, he, setIntegral_indicator measurableSet_Iio]
    rfl
  rw [hwindow, suzukiCriticalPoleDensity, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  have he : Real.exp ((1/2-omega)*(t-r)) =
      Real.exp ((1/2-omega)*t) * Real.exp (-(1/2-omega)*r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

private theorem poleMass_bounds {omega t : ℝ} (homega : 0 < omega)
    (homega2 : omega ≤ 1/2) :
    0 ≤ poleMass omega t ∧ poleMass omega t ≤ suzukiCriticalPrimaryMass omega := by
  have hB := integrableOn_suzukiCriticalPrimaryDensity homega (by linarith : omega < 5/2)
  have hi := poleMass_integrable homega homega2 t
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (poleWeight_bounds homega2 hr).1
      (suzukiCriticalPrimaryDensity_pos homega hr).le
  · rw [← integral_suzukiCriticalPrimaryDensity homega (by linarith : omega < 5/2)]
    apply integral_mono_ae hi hB
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_of_le_one_left (suzukiCriticalPrimaryDensity_pos homega hr).le
      (poleWeight_bounds homega2 hr).2

private theorem poleMass_deficit_le {omega t : ℝ} (homega : 0 < omega)
    (homega2 : omega ≤ 1/2) (ht : 0 < t) :
    suzukiCriticalPrimaryMass omega-poleMass omega t ≤ (1+1/t)*suzukiCriticalPrimaryFirstMoment omega := by
  have hB := integrableOn_suzukiCriticalPrimaryDensity homega (by linarith : omega < 5/2)
  have hi := poleMass_integrable homega homega2 t
  rw [← integral_suzukiCriticalPrimaryDensity homega (by linarith : omega < 5/2),
    poleMass, ← integral_sub hB hi, suzukiCriticalPrimaryFirstMoment, ← integral_const_mul]
  apply integral_mono_ae (hB.sub hi)
    ((integrableOn_suzukiCriticalPrimaryFirstMoment homega (by linarith)).const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have h := mul_le_mul_of_nonneg_right (poleWeight_deficit_le homega ht hr)
    (suzukiCriticalPrimaryDensity_pos homega hr).le
  dsimp only [Pi.sub_apply]
  nlinarith only [h]

/-- The positive causal pole is bounded by the exact primary mass and the growing exponential. -/
theorem suzukiCriticalPoleDensity_bounds {omega t : ℝ} (homega : 0 < omega)
    (homega2 : omega ≤ 1/2) (ht : 0 < t) :
    0 ≤ suzukiCriticalPoleDensity omega t ∧
      suzukiCriticalPoleDensity omega t ≤ suzukiCriticalPrimaryMass omega * Real.exp (t/2) := by
  have hp := poleMass_bounds (t := t) homega homega2
  rw [poleDensity_eq_exp_mul_mass]
  have he : Real.exp ((1/2-omega)*t) ≤ Real.exp (t/2) := by
    apply Real.exp_le_exp.mpr
    have hwt := mul_nonneg homega.le ht.le
    nlinarith only [hwt]
  exact ⟨mul_nonneg (Real.exp_pos _).le hp.1,
    (mul_le_mul he hp.2 hp.1 (Real.exp_pos _).le).trans_eq (mul_comm _ _)⟩

/-- At every positive argument the causal pole tends to its growing critical exponential. -/
theorem tendsto_suzukiCriticalPoleDensity {t : ℝ} (ht : 0 < t) :
    Tendsto (fun omega => suzukiCriticalPoleDensity omega t) (𝓝[>] 0)
      (𝓝 (Real.exp (t/2))) := by
  have ho : ∀ᶠ omega : ℝ in 𝓝[>] 0, omega < 1/2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  have hsmall : ∀ᶠ omega : ℝ in 𝓝[>] 0, 0 < omega ∧ omega < 1/2 := by
    filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
    exact ⟨homega,ho⟩
  have hd : Tendsto (fun omega => suzukiCriticalPrimaryMass omega-poleMass omega t)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [hsmall] with omega homega
      exact sub_nonneg.mpr (poleMass_bounds homega.1 homega.2.le).2
    · filter_upwards [hsmall] with omega homega
      exact poleMass_deficit_le homega.1 homega.2.le ht
    · simpa only [mul_zero] using tendsto_suzukiCriticalPrimaryFirstMoment.const_mul (1+1/t)
  have hM := tendsto_suzukiCriticalPrimaryMass.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hp : Tendsto (fun omega => poleMass omega t) (𝓝[>] 0) (𝓝 1) := by
    simpa only [sub_sub_cancel, sub_zero] using hM.sub hd
  have he : Tendsto (fun omega : ℝ => Real.exp ((1/2-omega)*t)) (𝓝[>] 0)
      (𝓝 (Real.exp (t/2))) := by
    have hc : Continuous (fun omega : ℝ => Real.exp ((1/2-omega)*t)) := by fun_prop
    have heq : (1/2-(0 : ℝ))*t = t/2 := by ring
    simpa only [heq] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa only [← poleDensity_eq_exp_mul_mass, mul_one] using he.mul hp

end
end RHTower

