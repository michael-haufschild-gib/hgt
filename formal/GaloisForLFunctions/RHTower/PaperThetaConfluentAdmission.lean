import GaloisForLFunctions.RHTower.PaperThetaConfluentQuantile

/-! # Compact admission and the exact confluent matching threshold

All parameter jets are actual compact BV functions. Every slot below a Xi
multiplicity is an uncut absolutely continuous mode; the terminal slot has a
nonzero jump at every finite cut. No simplicity or zero-location input occurs.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

theorem leftClosedParameterJet_interior (n : ℕ) (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    leftClosedParameterJet n z t.val = leftParameterJet n z (thetaSource.quantileFun t.val) := by
  rw [leftClosedParameterJet_eq, leftParameterJet_eq]
  congr 1
  funext w
  exact leftClosedQuantileMode_interior w t

theorem continuousAt_closedParameterJet (n : ℕ) (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    ContinuousAt (closedParameterJet n z) t.val := by
  change Tendsto _ _ _
  rw [closedParameterJet_interior n z t]
  apply ((continuous_flatParameterJet n z).continuousAt.tendsto.comp
    (hasDerivAt_quantileFun thetaSource t.property).continuousAt.tendsto).congr'
  filter_upwards [Ioo_mem_nhds t.property.1 t.property.2] with x hx
  exact (closedParameterJet_interior n z ⟨x, hx⟩).symm

theorem continuousAt_leftClosedParameterJet (n : ℕ) (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    ContinuousAt (leftClosedParameterJet n z) t.val := by
  change Tendsto _ _ _
  rw [leftClosedParameterJet_interior n z t]
  apply ((continuous_leftParameterJet n z).continuousAt.tendsto.comp
    (hasDerivAt_quantileFun thetaSource t.property).continuousAt.tendsto).congr'
  filter_upwards [Ioo_mem_nhds t.property.1 t.property.2] with x hx
  exact (leftClosedParameterJet_interior n z ⟨x, hx⟩).symm

theorem leftClosedParameterJet_zero (n : ℕ) (z : ℂ) :
    leftClosedParameterJet n z 0 = parameterEndpointTrace n := by
  rw [leftClosedParameterJet, sub_zero, (closedParameterJet_endpoints n (-z)).2]
  cases n <;> simp [parameterEndpointTrace]

theorem cutQuantileParameterJet_left (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t < c.val) :
    cutQuantileParameterJet n z c t = leftClosedParameterJet n z t := by
  simp only [cutQuantileParameterJet, cutQuantileMode, if_pos ht, leftClosedParameterJet_eq]

theorem cutQuantileParameterJet_right (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : c.val ≤ t) :
    cutQuantileParameterJet n z c t = closedParameterJet n z t := by
  simp only [cutQuantileParameterJet, cutQuantileMode, if_neg (not_lt.mpr ht), closedParameterJet]

theorem cutQuantileParameterJet_endpoints (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    cutQuantileParameterJet n z c 0 = parameterEndpointTrace n ∧
      cutQuantileParameterJet n z c 1 = parameterEndpointTrace n := by
  rw [cutQuantileParameterJet_left n z c c.property.1, leftClosedParameterJet_zero,
    cutQuantileParameterJet_right n z c c.property.2.le, (closedParameterJet_endpoints n z).2]
  exact ⟨rfl, rfl⟩

theorem cutQuantileParameterJet_interior (n : ℕ) (z : ℂ) (c t : Ioo (0 : ℝ) 1) :
    cutQuantileParameterJet n z c t.val = cutParameterJet n z
      (thetaSource.quantileFun c.val) (thetaSource.quantileFun t.val) := by
  unfold cutQuantileParameterJet cutParameterJet
  congr 1
  funext w
  exact cutQuantileMode_interior w c t

theorem closedParameterJet_sub_left (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    closedParameterJet n z c.val-leftClosedParameterJet n z c.val =
      iteratedDeriv n (fun w => cutCharge w (thetaSource.quantileFun c.val)) z := by
  rw [closedParameterJet_interior n z c, leftClosedParameterJet_interior n z c,
    flatParameterJet_sub_left]

theorem tendsto_cutQuantileParameterJet_left (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    Tendsto (cutQuantileParameterJet n z c) (𝓝[<] c.val)
      (𝓝 (leftClosedParameterJet n z c.val)) := by
  apply ((continuousAt_leftClosedParameterJet n z c).tendsto.mono_left
    nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (cutQuantileParameterJet_left n z c ht).symm

/-- Full compact BV admission includes all orders and all complex parameters. -/
theorem boundedVariationOn_cutQuantileParameterJet (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    BoundedVariationOn (cutQuantileParameterJet n z c) (Icc (0 : ℝ) 1) := by
  have hL : BoundedVariationOn (leftClosedParameterJet n z) (Icc (0 : ℝ) c.val) := by
    simpa only [uIcc_of_le c.property.1.le] using
      (absolutelyContinuousOnInterval_leftClosedParameterJet n z c).boundedVariationOn
  have hl : eVariationOn (cutQuantileParameterJet n z c) (Ico (0 : ℝ) c.val) ≠ ⊤ := by
    rw [eVariationOn.congr (s := Ico (0 : ℝ) c.val)
      (fun _ ht => cutQuantileParameterJet_left n z c ht.2)]
    exact hL.mono Ico_subset_Icc_self
  have he := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
    (f := cutQuantileParameterJet n z c) (s := Ici (0 : ℝ)) (a := c.val)
    (l := leftClosedParameterJet n z c.val)
    (by rw [Ici_inter_Iio, nhdsWithin_Ico_eq_nhdsLT c.property.1]; infer_instance)
    c.property.1.le
    (by simpa only [Ici_inter_Iio, nhdsWithin_Ico_eq_nhdsLT c.property.1] using
      tendsto_cutQuantileParameterJet_left n z c)
  rw [Ici_inter_Iic, Ici_inter_Iio] at he
  have hlc : eVariationOn (cutQuantileParameterJet n z c) (Icc (0 : ℝ) c.val) ≠ ⊤ := by
    rw [he]
    exact ENNReal.add_ne_top.mpr ⟨hl, edist_ne_top _ _⟩
  have hr : eVariationOn (cutQuantileParameterJet n z c) (Icc c.val 1) ≠ ⊤ := by
    rw [eVariationOn.congr (s := Icc c.val 1)
      (fun _ ht => cutQuantileParameterJet_right n z c ht.1)]
    change BoundedVariationOn (closedParameterJet n z) (Icc c.val 1)
    simpa only [uIcc_of_le c.property.2.le] using
      (absolutelyContinuousOnInterval_closedParameterJet_right n z c).boundedVariationOn
  change eVariationOn (cutQuantileParameterJet n z c) (Icc (0 : ℝ) 1) ≠ ⊤
  rw [← Icc_union_Icc_eq_Icc c.property.1.le c.property.2.le,
    eVariationOn.union (cutQuantileParameterJet n z c)
      (s := Icc (0 : ℝ) c.val) (t := Icc c.val 1) (x := c.val)
      ⟨⟨c.property.1.le, le_rfl⟩, fun _ h => h.2⟩
      ⟨⟨le_rfl, c.property.2.le⟩, fun _ h => h.1⟩]
  exact ENNReal.add_ne_top.mpr ⟨hlc, hr⟩

theorem cutQuantileParameterJet_eq_native (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) (c : Ioo (0 : ℝ) 1) (t : Icc (0 : ℝ) 1) :
    cutQuantileParameterJet j.val (xiSpectralPointSupport rho) c t.val =
      closedParameterJet j.val (xiSpectralPointSupport rho) t.val := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with ht | ht | ht
  · rw [ht, (cutQuantileParameterJet_endpoints _ _ c).1, (closedParameterJet_endpoints _ _).1]
  · rw [ht, (cutQuantileParameterJet_endpoints _ _ c).2, (closedParameterJet_endpoints _ _).2]
  · rw [cutQuantileParameterJet_interior _ _ c ⟨t.val, ht⟩,
      cutParameterJet_eq_native rho j, closedParameterJet_interior _ _ ⟨t.val, ht⟩]

/-- The full confluent packet is admitted as uncut AC modes in the original compact domain. -/
theorem absolutelyContinuousOnInterval_divisor_closedParameterJet (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) :
    AbsolutelyContinuousOnInterval (closedParameterJet j.val (xiSpectralPointSupport rho)) 0 1 := by
  let c : Ioo (0 : ℝ) 1 := ⟨1/2, by constructor <;> linarith⟩
  let z := xiSpectralPointSupport rho
  have hmatch : leftClosedParameterJet j.val z c.val = closedParameterJet j.val z c.val := by
    have hj := (cutCharge_full_multiplicity_jets rho (thetaSource.quantileFun c.val)).1 j.val j.isLt
    rw [← closedParameterJet_sub_left j.val z c] at hj
    exact (sub_eq_zero.mp hj).symm
  have hp := AbsolutelyContinuousOnInterval.piecewise_Iic c.property.1.le c.property.2.le
    (absolutelyContinuousOnInterval_leftClosedParameterJet j.val z c)
    (absolutelyContinuousOnInterval_closedParameterJet_right j.val z c) hmatch
  apply hp.congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  by_cases htc : t ≤ c.val
  · rw [Set.piecewise, if_pos (show t ∈ Iic c.val from htc)]
    rcases lt_or_eq_of_le htc with hlt | rfl
    · rw [← cutQuantileParameterJet_left j.val z c hlt]
      exact cutQuantileParameterJet_eq_native rho j c ⟨t, ht⟩
    · exact hmatch
  · rw [Set.piecewise, if_neg (show t ∉ Iic c.val from htc)]

/-- Terminal nonmatching is an actual discontinuity, not only a scalar order statement. -/
theorem not_continuousAt_terminal_cutQuantileParameterJet (rho : XiDivisorSupport)
    (c : Ioo (0 : ℝ) 1) :
    ¬ ContinuousAt (cutQuantileParameterJet (xiSupportMultiplicity rho)
      (xiSpectralPointSupport rho) c) c.val := by
  intro hc
  have he := tendsto_nhds_unique (hc.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] c.val ≤ 𝓝 c.val))
    (tendsto_cutQuantileParameterJet_left _ _ c)
  rw [cutQuantileParameterJet_right _ _ c le_rfl] at he
  have hj := (cutCharge_full_multiplicity_jets rho (thetaSource.quantileFun c.val)).2
  rw [← closedParameterJet_sub_left, he, sub_self] at hj
  exact hj rfl

end RHTower.PaperThetaEndpoint
