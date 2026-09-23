import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffPairingSeeds

/-! Absolute admission of the complete original lower-strip cutoff Mellin product. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

private theorem point_im (x y : ℝ) (hy : 0 < y) : (ofComplex (⟨x,y⟩:ℂ)).im = y := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy)]
  rfl

private theorem orbit_bound (q : XiZeroCopy) (C : ℝ)
    (hb : ∀ y : ℝ, ‖nativeSquareCutoffHeight q y‖ ≤ C*y^(2 : ℕ)) (z : UpperHalfPlane) :
    ‖periodize (squareCutoffSeed q) z‖ ≤ C*positiveCuspRows 2 z := by
  rw [squareCutoffSeed_eq_heightSeed q]
  exact highCuspHeight_periodize_norm_le _ (nativeSquareCutoffHeight_zero q) C hb z

private theorem line_bound (q : XiZeroCopy) (s : ℂ) (C : ℝ)
    (hb : ∀ y : ℝ, ‖nativeSquareCutoffHeight q y‖ ≤ C*y^(2 : ℕ)) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖nativeCutoffLowerPair q s (ofComplex (⟨x,y⟩:ℂ))‖ ≤
      (‖lowCuspPower s y‖*C)*positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ)) := by
  rw [nativeCutoffLowerPair,norm_mul,point_im x y hy]
  exact (mul_le_mul_of_nonneg_left (orbit_bound q C hb _) (norm_nonneg _)).trans_eq (by ring)

/-- Every actual horizontal slice is admitted before taking its norm mean. -/
theorem nativeCutoffLowerPair_horizontal_integrable (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => nativeCutoffLowerPair q P.s (ofComplex (⟨x,y⟩:ℂ))) (Ico (0:ℝ) 1) := by
  obtain ⟨C,_,hb⟩ := nativeSquareCutoffHeight_quadratic_bound q
  have hm : Measurable (fun x : ℝ => nativeCutoffLowerPair q P.s (ofComplex (⟨x,y⟩:ℂ))) :=
    (nativeCutoffLowerPair_measurable q P).comp
      (cuspStripPoint_measurable.comp (measurable_const.prodMk measurable_id))
  apply ((positiveCuspRows_horizontal_integrable 2 (by norm_num) hy).const_mul (‖lowCuspPower P.s y‖*C)).mono'
    hm.aestronglyMeasurable
  exact ae_of_all _ (fun x => line_bound q P.s C hb hy x)

private theorem lower_density_identity (s C D y : ℝ) (hy : 0 < y) :
    (y^(2 : ℕ))⁻¹*((y^s*C)*(y^(2 : ℕ)+D*y^(-1:ℝ))) = C*(y^s+D*y^(s-3)) := by
  have h2 : y^(-2:ℝ)*y^s*y^(2:ℝ) = y^s := by
    rw [← Real.rpow_add hy,← Real.rpow_add hy]
    congr 1
    ring
  have h3 : y^(-2:ℝ)*y^s*y^(-1:ℝ) = y^(s-3) := by
    rw [← Real.rpow_add hy,← Real.rpow_add hy]
    congr 1
    ring
  rw [← Real.rpow_two,← Real.rpow_neg hy.le]
  calc
    _ = C*(y^(-2:ℝ)*y^s*y^(2:ℝ))+C*D*(y^(-2:ℝ)*y^s*y^(-1:ℝ)) := by ring
    _ = _ := by rw [h2,h3]; ring

/-- All lower-strip norm-integral bounds are derived for the native Xi cutoff itself. -/
theorem nativeCutoffLowerPair_integrable (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (nativeCutoffLowerPair q s) modularStrip volume := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨s,by linarith⟩
  obtain ⟨C,hC,hb⟩ := nativeSquareCutoffHeight_quadratic_bound q
  let M : ℝ → ℝ := fun y => (y^(2 : ℕ))⁻¹*∫ x in Ico (0:ℝ) 1,
    ‖nativeCutoffLowerPair q s (ofComplex (⟨x,y⟩:ℂ))‖
  have hm : Measurable M := (measurable_id.pow_const 2).inv.mul
    (cuspHorizontalNormMean_measurable _ (nativeCutoffLowerPair_measurable q P))
  have hlo : IntegrableOn M (Ioc (0:ℝ) (1/2:ℝ)) := by
    have hg1 : IntegrableOn (fun y : ℝ => y^s.re) (Ioc (0:ℝ) (1/2:ℝ)) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < s.re)
        (a := (0:ℝ)) (b := (1/2:ℝ))).1
    have hg2 : IntegrableOn (fun y : ℝ => y^(s.re-3)) (Ioc (0:ℝ) (1/2:ℝ)) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < s.re-3)
        (a := (0:ℝ)) (b := (1/2:ℝ))).1
    apply ((hg1.add (hg2.const_mul (cuspReflectionNorm 2))).const_mul C).mono' hm.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro y hy
    have hp : ‖lowCuspPower s y‖ = y^s.re := by rw [lowCuspPower_norm s hy.1,if_pos hy.2]
    have hi := integral_mono (nativeCutoffLowerPair_horizontal_integrable q P hy.1).norm
      ((positiveCuspRows_horizontal_integrable 2 (by norm_num) hy.1).const_mul (‖lowCuspPower s y‖*C))
      (fun x => line_bound q s C hb hy.1 x)
    rw [integral_const_mul,hp] at hi
    have ha := mul_le_mul_of_nonneg_left (positiveCuspRows_mean_le 2 (by norm_num) hy.1)
      (mul_nonneg (Real.rpow_nonneg hy.1.le s.re) hC)
    norm_num only [Real.rpow_two,show (1:ℝ)-2 = -1 by norm_num] at ha
    have hM : 0 ≤ M y := mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))
    rw [Real.norm_eq_abs,abs_of_nonneg hM]
    calc
      M y ≤ (y^(2 : ℕ))⁻¹*((y^s.re*C)*(y^(2 : ℕ)+cuspReflectionNorm 2*y^(-1:ℝ))) :=
        mul_le_mul_of_nonneg_left (hi.trans ha) (by positivity)
      _ = C*(y^s.re+cuspReflectionNorm 2*y^(s.re-3)) := lower_density_identity _ _ _ _ hy.1
  have hhi : IntegrableOn M (Ioi (1/2:ℝ)) := by
    have he : EqOn M 0 (Ioi (1/2:ℝ)) := by
      intro y hy
      have hy0 : 0 < y := lt_trans (by norm_num : (0:ℝ)<1/2) hy
      have hz (x : ℝ) : nativeCutoffLowerPair q s (ofComplex (⟨x,y⟩:ℂ)) = 0 :=
        nativeCutoffLowerPair_zero q s _ (by rw [point_im x y hy0]; exact hy)
      simp [M,hz]
    exact (integrableOn_congr_fun he measurableSet_Ioi).mpr (integrableOn_zero)
  apply modularStrip_integrable_of_norm_mean _ (nativeCutoffLowerPair_measurable q P)
    (fun y hy => nativeCutoffLowerPair_horizontal_integrable q P hy)
  apply (hlo.union hhi).mono_set
  intro y hy
  by_cases hh : y ≤ 1/2
  · exact Or.inl ⟨hy,hh⟩
  · exact Or.inr (lt_of_not_ge hh)

end
end RHTower.D4BMJointSource
