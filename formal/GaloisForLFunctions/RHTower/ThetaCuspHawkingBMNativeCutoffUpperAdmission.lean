import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffPairingSeeds

/-! Absolute admission of the original high cutoff paired with the complete reverse orbit kernel. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

private theorem point_im (x y : ℝ) (hy : 0 < y) : (ofComplex (⟨x,y⟩:ℂ)).im = y := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy)]
  rfl

private theorem line_bound (q : XiZeroCopy) (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖nativeCutoffUpperPair q P.s (ofComplex (⟨x,y⟩:ℂ))‖ ≤
      ‖nativeSquareCutoffHeight q y‖*positiveLowCuspRows P.s.re (ofComplex (⟨x,y⟩:ℂ)) := by
  rw [nativeCutoffUpperPair,norm_mul,point_im x y hy]
  exact mul_le_mul_of_nonneg_left (lowCuspPower_periodize_norm_le P _) (norm_nonneg _)

/-- The original upper product has admitted horizontal slices, with its low-height zero retained. -/
theorem nativeCutoffUpperPair_horizontal_integrable (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => nativeCutoffUpperPair q P.s (ofComplex (⟨x,y⟩:ℂ))) (Ico (0:ℝ) 1) := by
  by_cases hy2 : y ≤ 2
  · have he (x : ℝ) : nativeCutoffUpperPair q P.s (ofComplex (⟨x,y⟩:ℂ)) = 0 :=
      nativeCutoffUpperPair_zero q P.s _ (by rw [point_im x y hy]; exact hy2)
    simp_rw [he]
    exact integrableOn_zero
  · have hm : Measurable (fun x : ℝ => nativeCutoffUpperPair q P.s (ofComplex (⟨x,y⟩:ℂ))) :=
      (nativeCutoffUpperPair_measurable q P).comp
        (cuspStripPoint_measurable.comp (measurable_const.prodMk measurable_id))
    apply ((positiveLowCuspRows_horizontal_integrable P.s.re P.re_gt_one (le_of_not_ge hy2)).const_mul
      ‖nativeSquareCutoffHeight q y‖).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun x => line_bound q P hy x)

/-- The native high cutoff and its reverse kernel are absolutely integrable in the common chamber. -/
theorem nativeCutoffUpperPair_integrable (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (nativeCutoffUpperPair q s) modularStrip volume := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨s,by linarith⟩
  obtain ⟨C,hC,hb⟩ := nativeSquareCutoffHeight_quadratic_bound q
  let M : ℝ → ℝ := fun y => (y^(2 : ℕ))⁻¹*∫ x in Ico (0:ℝ) 1,
    ‖nativeCutoffUpperPair q s (ofComplex (⟨x,y⟩:ℂ))‖
  have hm : Measurable M := (measurable_id.pow_const 2).inv.mul
    (cuspHorizontalNormMean_measurable _ (nativeCutoffUpperPair_measurable q P))
  have hlo : IntegrableOn M (Ioc (0:ℝ) 2) := by
    have he : EqOn M 0 (Ioc (0:ℝ) 2) := by
      intro y hy
      have hz (x : ℝ) : nativeCutoffUpperPair q s (ofComplex (⟨x,y⟩:ℂ)) = 0 :=
        nativeCutoffUpperPair_zero q s _ (by rw [point_im x y hy.1]; exact hy.2)
      simp [M,hz]
    exact (integrableOn_congr_fun he measurableSet_Ioc).mpr integrableOn_zero
  have hhi : IntegrableOn M (Ioi (2:ℝ)) := by
    have hg : IntegrableOn (fun y : ℝ => (C*cuspReflectionNorm s.re)*y^(1-s.re)) (Ioi (2:ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : 1-s.re < -1) (by norm_num : (0:ℝ)<2)).const_mul _
    apply hg.mono' hm.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := lt_trans (by norm_num : (0:ℝ)<2) hy
    have hi := integral_mono (nativeCutoffUpperPair_horizontal_integrable q P hy0).norm
      ((positiveLowCuspRows_horizontal_integrable s.re P.re_gt_one hy.le).const_mul ‖nativeSquareCutoffHeight q y‖)
      (fun x => line_bound q P hy0 x)
    rw [integral_const_mul,positiveLowCuspRows_mean s.re P.re_gt_one hy.le] at hi
    have ha := mul_le_mul_of_nonneg_right (hb y)
      (mul_nonneg (cuspReflectionNorm_nonneg s.re) (Real.rpow_nonneg hy0.le (1-s.re)))
    have hM : 0 ≤ M y := mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))
    rw [Real.norm_eq_abs,abs_of_nonneg hM]
    calc
      M y ≤ (y^(2 : ℕ))⁻¹*((C*y^(2 : ℕ))*(cuspReflectionNorm s.re*y^(1-s.re))) :=
        mul_le_mul_of_nonneg_left (hi.trans ha) (by positivity)
      _ = (C*cuspReflectionNorm s.re)*y^(1-s.re) := by field_simp
  apply modularStrip_integrable_of_norm_mean _ (nativeCutoffUpperPair_measurable q P)
    (fun y hy => nativeCutoffUpperPair_horizontal_integrable q P hy)
  apply (hlo.union hhi).mono_set
  intro y hy
  by_cases hh : y ≤ 2
  · exact Or.inl ⟨hy,hh⟩
  · exact Or.inr (lt_of_not_ge hh)

end
end RHTower.D4BMJointSource
