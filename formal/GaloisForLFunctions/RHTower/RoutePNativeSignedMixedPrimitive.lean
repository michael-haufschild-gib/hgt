import GaloisForLFunctions.RHTower.RoutePLatePrimeIncrementLimits

/-!
# The literal signed mixed-work primitive

The complete moving prime increment is locally integrable, and its
physical right-continuity gives the primitive's right derivative at
every positive clock. No signed growth bound is assumed or asserted.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

/-- The signed mixed work accumulated through the literal physical clock. -/
def routePNativeLatePrimeMixedPrimitive (ε t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, routePNativeLatePrimeMixedWork ε s

theorem integrableOn_routePLatePrimeIncrement_Ioc (T : ℝ) :
    IntegrableOn routePLatePrimeIncrement (Ioc (0 : ℝ) T) := by
  by_cases hT : 0 ≤ T
  · have hv : IntervalIntegrable routePLatePrimeVelocity volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
        (integrableOn_routePLatePrimeVelocity_Ioc T)
    have hc : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, routePLatePrimeVelocity s)
        (Icc 0 T) := by
      simpa only [uIcc_of_le hT] using
        intervalIntegral.continuousOn_primitive_interval' hv
          (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
    have ha : IntegrableOn (fun s : ℝ =>
        ∑ p ∈ Nat.primesLE ⌊Real.exp (T / 2)⌋₊,
          if 2 * Real.log p ≤ s then criticalAbelLogProfile (Real.log p) / p else 0)
        (Ioc (0 : ℝ) T) := by
      apply integrable_finsetSum
      intro p _
      have hi := (show Continuous (fun _ : ℝ =>
        criticalAbelLogProfile (Real.log p) / p) from continuous_const).integrableOn_Ioc
        (a := (0 : ℝ)) (b := T) (μ := volume)
      have heq : (fun s : ℝ => if 2 * Real.log p ≤ s then
          criticalAbelLogProfile (Real.log p) / p else 0) =
          (Ici (2 * Real.log (p : ℝ))).indicator
            (fun _ => criticalAbelLogProfile (Real.log p) / p) := by
        funext s
        simp only [Set.indicator_apply, Set.mem_Ici]
      rw [heq]
      exact hi.indicator measurableSet_Ici
    apply ((hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).sub ha).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [routePLatePrimeIncrement_eq_velocity_sub_removals ht.1.le,
      routePLatePrimeRemovalMass_eq_finite ht.2]
    simp only [Pi.sub_apply]
  · rw [Ioc_eq_empty (not_lt.mpr (le_of_not_ge hT))]
    exact integrableOn_empty

theorem measurable_routePNativeLatePrimeMixedWork (ε : ℝ) :
    Measurable (routePNativeLatePrimeMixedWork ε) :=
  (((measurable_const.mul measurable_id).exp).mul
    measurable_criticalAbelLogProfile).mul measurable_routePLatePrimeIncrement

theorem integrableOn_routePNativeLatePrimeMixedWork_Ioc (ε T : ℝ) :
    IntegrableOn (routePNativeLatePrimeMixedWork ε) (Ioc (0 : ℝ) T) := by
  have hc : ContinuousOn (fun t : ℝ =>
      Real.exp ((1 - ε) * t) * criticalAbelLogProfile t) (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      continuous_criticalAbelLogProfile).continuousOn
  have hi := (integrableOn_routePLatePrimeIncrement_Ioc T).mul_continuousOn_of_subset
    hc measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  apply hi.congr
  filter_upwards [] with t
  unfold routePNativeLatePrimeMixedWork
  ring

theorem continuousWithinAt_routePNativeLatePrimeMixedWork_right (ε : ℝ)
    {t : ℝ} (ht : 0 < t) :
    ContinuousWithinAt (routePNativeLatePrimeMixedWork ε) (Ici t) t :=
  (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    continuous_criticalAbelLogProfile).continuousAt.continuousWithinAt).mul
      (continuousWithinAt_routePLatePrimeIncrement_right ht)

theorem continuousAt_routePNativeLatePrimeMixedPrimitive (ε : ℝ)
    {t : ℝ} (ht : 0 < t) :
    ContinuousAt (routePNativeLatePrimeMixedPrimitive ε) t := by
  have hT : 0 ≤ t + 1 := by linarith
  have hi : IntervalIntegrable (routePNativeLatePrimeMixedWork ε) volume 0 (t + 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      (integrableOn_routePNativeLatePrimeMixedWork_Ioc ε (t + 1))
  have hc : ContinuousOn (routePNativeLatePrimeMixedPrimitive ε) (Icc 0 (t + 1)) := by
    change ContinuousOn (fun u => ∫ s in (0 : ℝ)..u, routePNativeLatePrimeMixedWork ε s)
      (Icc 0 (t + 1))
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hi
        (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 (t + 1))
  exact hc.continuousAt (Icc_mem_nhds ht (by linarith))

/-- The derivative uses the literal right value of the complete mixed work,
including every arithmetic entry and removal clock. -/
theorem routePNativeLatePrimeMixedPrimitive_hasDeriv_right (ε : ℝ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (routePNativeLatePrimeMixedPrimitive ε)
      (routePNativeLatePrimeMixedWork ε t) (Ioi t) t := by
  have hi : IntervalIntegrable (routePNativeLatePrimeMixedWork ε) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr
      (integrableOn_routePNativeLatePrimeMixedWork_Ioc ε t)
  have hmeas : StronglyMeasurableAtFilter (routePNativeLatePrimeMixedWork ε) (𝓝[Ioi t] t) :=
    (measurable_routePNativeLatePrimeMixedWork ε).aestronglyMeasurable.stronglyMeasurableAtFilter
  have hc := (continuousWithinAt_routePNativeLatePrimeMixedWork_right ε ht).mono
    Ioi_subset_Ici_self
  exact (intervalIntegral.integral_hasDerivWithinAt_right hi (s := Ici t) hmeas hc).mono
    Ioi_subset_Ici_self

end RHTower
