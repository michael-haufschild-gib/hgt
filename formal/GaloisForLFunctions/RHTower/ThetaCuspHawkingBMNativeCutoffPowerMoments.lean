import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffMellinAdmission

/-! Both original cutoff power moments are values of one finite-transition expression. -/
open Complex MeasureTheory Set
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section

/-- The original smooth transition is retained on its entire finite interval. -/
def nativeCutoffTransitionMoment (w : ℂ) : ℂ :=
  ∫ y in Ioc (2:ℝ) 3, cutoff ![0,y]*(y:ℂ)^(w-1)

/-- The power tail and the unchanged finite transition form the cutoff Mellin continuation. -/
def nativeCutoffMellinContinuation (w : ℂ) : ℂ :=
  (3:ℂ)^w/w-nativeCutoffTransitionMoment w

theorem nativeCutoff_height_continuous : Continuous (fun y : ℝ => cutoff ![0,y]) := by
  change Continuous (fun y : ℝ => (Real.smoothTransition (y-2):ℂ))
  exact Complex.continuous_ofReal.comp ((Real.smoothTransition.contDiff (n := 1)).continuous.comp
    (continuous_id.sub continuous_const))

private theorem cutoff_low (y : ℝ) (hy : y ≤ 2) : cutoff ![0,y] = 0 := by
  unfold cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by change y-2≤0; linarith)]
  simp

private theorem cutoff_high (y : ℝ) (hy : 3 ≤ y) : cutoff ![0,y] = 1 := by
  unfold cutoff
  rw [Real.smoothTransition.one_of_one_le (by change 1≤y-2; linarith)]
  simp

/-- The original transition moment is integrable for every complex exponent. -/
theorem nativeCutoffTransition_integrable (w : ℂ) :
    IntegrableOn (fun y : ℝ => cutoff ![0,y]*(y:ℂ)^(w-1)) (Ioc (2:ℝ) 3) := by
  have hc : ContinuousOn (fun y : ℝ => cutoff ![0,y]*(y:ℂ)^(w-1)) (Icc (2:ℝ) 3) := by
    intro y hy
    have hy2 : (2:ℝ) ≤ y := hy.1
    exact (nativeCutoff_height_continuous.continuousAt.mul
      (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (by linarith : y ≠ 0)))).continuousWithinAt
  exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self

private theorem low_indicator (w : ℂ) (y : ℝ) (hy : 0 < y) :
    (1-cutoff ![0,y])*(y:ℂ)^(w-1) =
      (Ioc (0:ℝ) 3).indicator (fun y : ℝ => (y:ℂ)^(w-1)) y-
      (Ioc (2:ℝ) 3).indicator (fun y : ℝ => cutoff ![0,y]*(y:ℂ)^(w-1)) y := by
  by_cases h2 : y ≤ 2
  · rw [cutoff_low y h2,Set.indicator_of_mem (show y ∈ Ioc (0:ℝ) 3 from ⟨hy,by linarith⟩),
      Set.indicator_of_notMem (show y ∉ Ioc (2:ℝ) 3 from fun h => not_lt_of_ge h2 h.1)]
    ring
  · by_cases h3 : y ≤ 3
    · rw [Set.indicator_of_mem (show y ∈ Ioc (0:ℝ) 3 from ⟨hy,h3⟩),
        Set.indicator_of_mem (show y ∈ Ioc (2:ℝ) 3 from ⟨lt_of_not_ge h2,h3⟩)]
      ring
    · rw [cutoff_high y (le_of_lt (lt_of_not_ge h3)),
        Set.indicator_of_notMem (show y ∉ Ioc (0:ℝ) 3 from fun h => h3 h.2),
        Set.indicator_of_notMem (show y ∉ Ioc (2:ℝ) 3 from fun h => h3 h.2)]
      ring

private theorem lower_power_integrable (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ => (y:ℂ)^(w-1)) (Ioc (0:ℝ) 3) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤3)]
  exact intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)

/-- The original complementary cutoff power integral is absolutely admitted on its positive chamber. -/
theorem nativeCutoffLowPower_integrable (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ => (1-cutoff ![0,y])*(y:ℂ)^(w-1)) (Ioi (0:ℝ)) := by
  have hi := (((lower_power_integrable w hw).integrable_indicator measurableSet_Ioc).sub
    ((nativeCutoffTransition_integrable w).integrable_indicator measurableSet_Ioc)).integrableOn (s := Ioi (0:ℝ))
  exact hi.congr_fun (fun y hy => (low_indicator w y hy).symm) measurableSet_Ioi

/-- The original lower cutoff integral equals the derived power tail minus its unchanged transition. -/
theorem nativeCutoffLowPower_value (w : ℂ) (hw : 0 < w.re) :
    (∫ y in Ioi (0:ℝ), (1-cutoff ![0,y])*(y:ℂ)^(w-1)) = nativeCutoffMellinContinuation w := by
  have he := setIntegral_congr_fun (μ := volume) measurableSet_Ioi (low_indicator w)
  rw [he,integral_sub
    ((lower_power_integrable w hw).integrable_indicator measurableSet_Ioc).integrableOn
    ((nativeCutoffTransition_integrable w).integrable_indicator measurableSet_Ioc).integrableOn,
    setIntegral_indicator measurableSet_Ioc,setIntegral_indicator measurableSet_Ioc]
  rw [show Ioi (0:ℝ) ∩ Ioc (0:ℝ) 3 = Ioc (0:ℝ) 3 from inter_eq_right.mpr (fun _ hy => hy.1),
    show Ioi (0:ℝ) ∩ Ioc (2:ℝ) 3 = Ioc (2:ℝ) 3 from inter_eq_right.mpr (fun _ hy => lt_trans (by norm_num : (0:ℝ)<2) hy.1)]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤3),integral_cpow (Or.inl (by simp; linarith))]
  rw [show w-1+1=w by ring,Complex.ofReal_zero,Complex.zero_cpow (by intro h; rw [h] at hw; simp at hw)]
  simp only [sub_zero,Complex.ofReal_ofNat]
  rfl

/-- The original upper cutoff power integral is absolutely admitted on its negative chamber. -/
theorem nativeCutoffHighPower_integrable (w : ℂ) (hw : w.re < 0) :
    IntegrableOn (fun y : ℝ => cutoff ![0,y]*(y:ℂ)^(w-1)) (Ioi (2:ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (2:ℝ)≤3)]
  refine (nativeCutoffTransition_integrable w).union ?_
  have hi : IntegrableOn (fun y : ℝ => (y:ℂ)^(w-1)) (Ioi (3:ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) (by norm_num)
  apply hi.congr_fun _ measurableSet_Ioi
  intro y hy
  dsimp only
  rw [cutoff_high y (le_of_lt hy),one_mul]

/-- The original upper moment is the negative of the same cutoff continuation. -/
theorem nativeCutoffHighPower_value (w : ℂ) (hw : w.re < 0) :
    (∫ y in Ioi (2:ℝ), cutoff ![0,y]*(y:ℂ)^(w-1)) = -nativeCutoffMellinContinuation w := by
  have hi := nativeCutoffHighPower_integrable w hw
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (2:ℝ)≤3),setIntegral_union
    (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (nativeCutoffTransition_integrable w)
    (hi.mono_set (fun y hy => lt_trans (by norm_num : (2:ℝ)<3) hy))]
  have he : (∫ y in Ioi (3:ℝ), cutoff ![0,y]*(y:ℂ)^(w-1)) = ∫ y in Ioi (3:ℝ), (y:ℂ)^(w-1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [cutoff_high y (le_of_lt hy),one_mul]
  rw [he,integral_Ioi_cpow_of_lt (by simp; linarith) (by norm_num),show w-1+1=w by ring]
  unfold nativeCutoffMellinContinuation nativeCutoffTransitionMoment
  norm_num only [Complex.ofReal_ofNat]
  ring

end
end RHTower.D4BMJointSource
