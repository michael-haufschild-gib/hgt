import GaloisForLFunctions.RHTower.RoutePNativeMixedLaplaceTransform

/-!
# Weighted FTC for the actual corrected mixed primitive

Every physical removal has already been absorbed in P. Multiplication
by a complex exponential preserves its everywhere right derivative;
the actual velocity agrees almost everywhere with the right velocity.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.NativeMixedLaplace

private theorem expRay_hasDeriv (w : ℂ) (t : ℝ) :
    HasDerivAt (expRay w) (-w * expRay w t) t := by
  change HasDerivAt (fun x : ℝ => Complex.exp (-(w * (x : ℂ))))
    (-w * Complex.exp (-(w * (t : ℂ)))) t
  have h : HasDerivAt (fun x : ℝ => Complex.exp (-(w * (x : ℂ))))
      (-(Complex.exp (-(w * (t : ℂ))) * w)) t := by
    simpa only [neg_mul, mul_neg, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
      using (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-w)).cexp)
  convert h using 1
  ring

private theorem expRay_shift (w : ℂ) (δ t : ℝ) :
    expRay w t * (Real.exp (δ * t) : ℂ) = expRay (w - (δ : ℂ)) t := by
  simp only [expRay, Complex.ofReal_exp, Complex.ofReal_mul]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The native profile's transform is admitted on its unconditional
convergence half-plane. No source admission near the axis is asserted. -/
theorem native_admission {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 1 / 2 < z.re) :
    IntegrableOn (fun t => expRay z t * (routePNativeCriticalProfile t : ℂ)) (Ioi a) := by
  apply complex_admission z continuous_routePNativeCriticalProfile.aestronglyMeasurable.restrict
  apply integrable_criticalAbelLogProfile.norm.integrableOn.mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      continuous_routePNativeCriticalProfile).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ha.trans ht.le
    rw [routePNativeCriticalProfile_eq_exp_mul_logProfile]
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← mul_assoc, ← Real.exp_add]
    have he : Real.exp (-z.re * t + t / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans_eq (one_mul _)

/-- Exact complex weighted integration by parts for the literal native
corrected primitive. The growth hypothesis supplies only admission of
the density, and will be discharged by the analytic obstruction. -/
theorem exists_weightedFTC :
    ∃ T : ℝ, 0 < T ∧ ∀ ε b a C : ℝ, T < a → 0 ≤ b → 0 ≤ C →
      (∀ t : ℝ, a < t → |routePNativeLatePrimeMixedPrimitive ε t| ≤ C * Real.exp (b * t)) →
      ∀ u : ℝ, a ≤ u → ∀ w : ℂ, b < w.re →
        (∫ t in a..u, expRay (w - ((1 / 2 - ε : ℝ) : ℂ)) t *
          (routePNativeCriticalProfile t : ℂ)) =
          expRay w u * (routePNativeMixedCorrectedPrimitive ε u : ℂ) -
            expRay w a * (routePNativeMixedCorrectedPrimitive ε a : ℂ) +
          (∫ t in a..u, expRay w t * (density ε t : ℂ)) +
          w * ∫ t in a..u, expRay w t * (routePNativeMixedCorrectedPrimitive ε t : ℂ) := by
  obtain ⟨Tg, hTg, hg⟩ := exists_growthTransfer
  obtain ⟨Tc, _, hc⟩ := exists_routePNativeMixedCorrectedPrimitiveCalculus
  refine ⟨max Tg Tc, hTg.trans_le (le_max_left _ _), ?_⟩
  intro ε b a C hTa hb hC hQ u hau w hw
  have hga : Tg < a := (le_max_left _ _).trans_lt hTa
  have hca : Tc < a := (le_max_right _ _).trans_lt hTa
  have ha : 0 < a := hTg.trans hga
  have hPc : ContinuousOn (fun t => (routePNativeMixedCorrectedPrimitive ε t : ℂ))
      (Icc a u) := Complex.continuous_ofReal.comp_continuousOn
    ((hc ε).1.mono (fun t ht => hca.trans_le ht.1))
  have hQcont : ContinuousOn (routePNativeLatePrimeMixedPrimitive ε) (Ioi a) := by
    intro t ht
    exact (continuousAt_routePNativeLatePrimeMixedPrimitive ε (ha.trans ht)).continuousWithinAt
  have hDm : AEStronglyMeasurable (density ε) (volume.restrict (Ioi a)) :=
    (hQcont.aestronglyMeasurable measurableSet_Ioi).mul
      (measurable_routePLatePrimeVelocity.div
        (measurable_routePLatePrimeIncrement.pow_const 2)).aestronglyMeasurable.restrict
  have hDi := complex_admission w hDm (hg ε b a C hga.le hb hC hQ w.re hw).2.1
  have hD : IntervalIntegrable (fun t => expRay w t * (density ε t : ℂ)) volume a u :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hau).mpr
      (hDi.mono_set (fun _ ht => ht.1))
  let dr : ℝ → ℝ := fun t => routePNativeLatePrimeMixedPrimitive ε t *
    routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2
  have hdr : dr =ᶠ[ae volume] density ε := by
    filter_upwards [routePLatePrimeRightVelocity_ae_eq] with t ht
    dsimp only [dr, density]
    rw [ht]
    ring
  have hDr : IntervalIntegrable (fun t => expRay w t * (dr t : ℂ)) volume a u := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hau).mpr
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hau).mp hD).congr
    apply ae_restrict_of_ae
    filter_upwards [hdr] with t ht
    rw [ht]
  have hH : IntervalIntegrable (fun t => expRay (w - ((1 / 2 - ε : ℝ) : ℂ)) t *
      (routePNativeCriticalProfile t : ℂ)) volume a u :=
    ((continuous_expRay _).mul
      (Complex.continuous_ofReal.comp continuous_routePNativeCriticalProfile)).intervalIntegrable a u
  have hWPc := (continuous_expRay w).continuousOn.mul hPc
  have hP : IntervalIntegrable (fun t => expRay w t *
      (routePNativeMixedCorrectedPrimitive ε t : ℂ)) volume a u := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hau).mpr
    exact hWPc.integrableOn_Icc
  let F : ℝ → ℂ := fun t =>
    expRay (w - ((1 / 2 - ε : ℝ) : ℂ)) t * (routePNativeCriticalProfile t : ℂ) -
      expRay w t * (dr t : ℂ) -
      w * (expRay w t * (routePNativeMixedCorrectedPrimitive ε t : ℂ))
  have hF : IntervalIntegrable F volume a u := by
    simpa only [F, Pi.sub_def] using (hH.sub hDr).sub (hP.const_mul w)
  have hder : ∀ t ∈ Ioo a u, HasDerivWithinAt
      (fun s => expRay w s * (routePNativeMixedCorrectedPrimitive ε s : ℂ))
      (F t) (Ioi t) t := by
    intro t ht
    have hp := ((hc ε).2 t (hca.trans ht.1)).ofReal_comp
    change HasDerivWithinAt (expRay w *
      (fun s => (routePNativeMixedCorrectedPrimitive ε s : ℂ))) (F t) (Ioi t) t
    apply ((expRay_hasDeriv w t).hasDerivWithinAt.mul hp).congr_deriv
    dsimp only [F, dr]
    rw [← expRay_shift]
    push_cast
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hau hWPc hder hF
  change (∫ t in a..u, _ - _ - _) = _ at hftc
  rw [intervalIntegral.integral_sub (hH.sub hDr) (hP.const_mul w),
    intervalIntegral.integral_sub hH hDr, intervalIntegral.integral_const_mul] at hftc
  have heq : (∫ t in a..u, expRay w t * (dr t : ℂ)) =
      ∫ t in a..u, expRay w t * (density ε t : ℂ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdr] with t ht _
    rw [ht]
  rw [heq] at hftc
  simp only [Pi.mul_apply] at hftc
  linear_combination hftc

/-- The candidate tail formula agrees with the native transform on the
proved absolute-convergence half-plane, with the finite boundary retained. -/
theorem exists_tailIdentity :
    ∃ T : ℝ, 0 < T ∧ ∀ ε b a C : ℝ, T < a → 0 ≤ b → 0 ≤ C →
      (∀ t : ℝ, a < t → |routePNativeLatePrimeMixedPrimitive ε t| ≤ C * Real.exp (b * t)) →
      ∀ w : ℂ, b < w.re → 1 / 2 < (w - ((1 / 2 - ε : ℝ) : ℂ)).re →
        tail routePNativeCriticalProfile a (w - ((1 / 2 - ε : ℝ) : ℂ)) =
          -(expRay w a * (routePNativeMixedCorrectedPrimitive ε a : ℂ)) +
          tail (density ε) a w + w * tail (routePNativeMixedCorrectedPrimitive ε) a w := by
  obtain ⟨Tw, hTw, hW⟩ := exists_weightedFTC
  obtain ⟨Tg, _, hg⟩ := exists_growthTransfer
  obtain ⟨Tc, _, hc⟩ := exists_routePNativeMixedCorrectedPrimitiveCalculus
  refine ⟨max Tw (max Tg Tc), hTw.trans_le (le_max_left _ _), ?_⟩
  intro ε b a C hTa hb hC hQ w hw hz
  have hwa : Tw < a := (le_max_left _ _).trans_lt hTa
  have hga : Tg < a := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hTa
  have hca : Tc < a := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hTa
  have ha : 0 < a := hTw.trans hwa
  have hPm := ((hc ε).1.mono (Ioi_subset_Ioi hca.le)).aestronglyMeasurable
    (μ := volume) measurableSet_Ioi
  have hQcont : ContinuousOn (routePNativeLatePrimeMixedPrimitive ε) (Ioi a) := by
    intro t ht
    exact (continuousAt_routePNativeLatePrimeMixedPrimitive ε (ha.trans ht)).continuousWithinAt
  have hDm : AEStronglyMeasurable (density ε) (volume.restrict (Ioi a)) :=
    (hQcont.aestronglyMeasurable measurableSet_Ioi).mul
      (measurable_routePLatePrimeVelocity.div
        (measurable_routePLatePrimeIncrement.pow_const 2)).aestronglyMeasurable.restrict
  have hi := hg ε b a C hga.le hb hC hQ w.re hw
  have hP := complex_admission w hPm hi.1
  have hD := complex_admission w hDm hi.2.1
  have hH := native_admission ha.le hz
  have hterminal := complex_terminal w hi.2.2
  have hright := ((hterminal.sub_const
      (expRay w a * (routePNativeMixedCorrectedPrimitive ε a : ℂ))).add
      (intervalIntegral_tendsto_integral_Ioi a hD tendsto_id)).add
      ((intervalIntegral_tendsto_integral_Ioi a hP tendsto_id).const_mul w)
  have heq : (fun u => expRay w u * (routePNativeMixedCorrectedPrimitive ε u : ℂ) -
      expRay w a * (routePNativeMixedCorrectedPrimitive ε a : ℂ) +
      (∫ t in a..u, expRay w t * (density ε t : ℂ)) +
      w * ∫ t in a..u, expRay w t * (routePNativeMixedCorrectedPrimitive ε t : ℂ)) =ᶠ[atTop]
      (fun u => ∫ t in a..u, expRay (w - ((1 / 2 - ε : ℝ) : ℂ)) t *
        (routePNativeCriticalProfile t : ℂ)) := by
    filter_upwards [eventually_ge_atTop a] with u hu
    exact (hW ε b a C hwa hb hC hQ u hu w hw).symm
  have hid := tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi a hH tendsto_id) (hright.congr' heq)
  simp only [zero_sub] at hid
  simpa only [tail_eq_integral _ ha.le] using hid

end RHTower.NativeMixedLaplace
