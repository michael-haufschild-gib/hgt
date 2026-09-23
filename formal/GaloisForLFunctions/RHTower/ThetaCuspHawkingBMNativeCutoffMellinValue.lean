import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffPairingUnfolding

/-! The complete original lower cutoff orbit has its derived reflected Mellin value. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

private theorem point_im (x y : ℝ) (hy : 0 < y) : (ofComplex (⟨x,y⟩:ℂ)).im = y := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy)]
  rfl

private theorem density_power (s : ℂ) (c : ℂ) {y : ℝ} (hy : 0 < y) :
    (y^(2 : ℕ))⁻¹ • ((y:ℂ)^s*c) = (y:ℂ)^(s-2)*c := by
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have htwo : (y:ℂ)^(2:ℂ)=(y:ℂ)^(2 : ℕ) := by norm_cast
  rw [Complex.cpow_sub _ _ hn,htwo]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  ring

private theorem lower_density (q : XiZeroCopy) (s : ℂ) {y : ℝ} (hy : 0 < y) (hyh : y ≤ 1/2) :
    (y^(2 : ℕ))⁻¹ • (∫ x in Ico (0:ℝ) 1, nativeCutoffLowerPair q s (ofComplex (⟨x,y⟩:ℂ))) =
      (y:ℂ)^(s-2)*squareCutoffStripMean q y := by
  have he (x : ℝ) : nativeCutoffLowerPair q s (ofComplex (⟨x,y⟩:ℂ)) =
      (y:ℂ)^s*periodize (squareCutoffSeed q) (ofComplex (⟨x,y⟩:ℂ)) := by
    rw [nativeCutoffLowerPair,point_im x y hy,lowCuspPower,if_pos hyh]
  simp_rw [he]
  rw [integral_const_mul]
  exact density_power s (squareCutoffStripMean q y) hy

private theorem lower_density_zero (q : XiZeroCopy) (s : ℂ) {y : ℝ} (hy : 1/2 < y) :
    (y^(2 : ℕ))⁻¹ • (∫ x in Ico (0:ℝ) 1, nativeCutoffLowerPair q s (ofComplex (⟨x,y⟩:ℂ))) = 0 := by
  have hy0 : 0 < y := lt_trans (by norm_num : (0:ℝ)<1/2) hy
  have hz (x : ℝ) := nativeCutoffLowerPair_zero q s (ofComplex (⟨x,y⟩:ℂ))
    (by rw [point_im x y hy0]; exact hy)
  simp [hz]

/-- The admitted original lower strip is exactly its complete cutoff-mean Mellin integral. -/
theorem nativeCutoffLowerPair_eq_mellin (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    (∫ z : UpperHalfPlane in modularStrip, nativeCutoffLowerPair q s z) =
      ∫ y in Ioc (0:ℝ) (1/2:ℝ), (y:ℂ)^(s-2)*squareCutoffStripMean q y := by
  rw [setIntegral_modularStrip_eq_iterated _ (nativeCutoffLowerPair_integrable q s hs)]
  have he : (∫ y in Ioi (0:ℝ), (y^(2 : ℕ))⁻¹ • ∫ x in Ico (0:ℝ) 1,
      nativeCutoffLowerPair q s (ofComplex (⟨x,y⟩:ℂ))) =
      ∫ y in Ioi (0:ℝ), (Iic (1/2:ℝ)).indicator
        (fun y : ℝ => (y:ℂ)^(s-2)*squareCutoffStripMean q y) y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    by_cases hh : y ≤ 1/2
    · rw [Set.indicator_of_mem (s := Iic (1/2:ℝ)) hh]
      exact lower_density q s hy hh
    · rw [Set.indicator_of_notMem (s := Iic (1/2:ℝ)) hh]
      exact lower_density_zero q s (lt_of_not_ge hh)
  rw [he,setIntegral_indicator measurableSet_Iic]
  rfl

private theorem integrated_height_admitted (F : UpperHalfPlane → ℂ)
    (hi : IntegrableOn F modularStrip volume) :
    IntegrableOn (fun y : ℝ => (y^(2 : ℕ))⁻¹ • ∫ x in Ico (0:ℝ) 1,
      F (ofComplex (⟨x,y⟩:ℂ))) (Ioi (0:ℝ)) := by
  have hc := (integrableOn_modularStrip_iff F).mp hi
  rw [Measure.volume_eq_prod,IntegrableOn,← Measure.prod_restrict] at hc
  have hm : IntegrableOn (fun y : ℝ => ∫ x in Ico (0:ℝ) 1,
      stripChartIntegrand F (y,x)) (Ioi (0:ℝ)) := hc.integral_prod_left
  apply hm.congr_fun _ measurableSet_Ioi
  intro y _
  simp only [stripChartIntegrand,integral_smul]

/-- The lower cutoff Mellin integral itself is absolutely admitted, not only assigned a totalized value. -/
theorem nativeCutoffLowerMellin_integrable (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (fun y : ℝ => (y:ℂ)^(s-2)*squareCutoffStripMean q y) (Ioc (0:ℝ) (1/2:ℝ)) := by
  have hi := integrated_height_admitted _ (nativeCutoffLowerPair_integrable q s hs)
  apply (hi.mono_set (fun y hy => hy.1)).congr_fun _ measurableSet_Ioc
  intro y hy
  exact lower_density q s hy.1 hy.2

private theorem upper_density (q : XiZeroCopy) (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : 2 < y) :
    reflectedCompletedLambda (2*P.s)*((y^(2 : ℕ))⁻¹ •
      ∫ x in Ico (0:ℝ) 1, nativeCutoffUpperPair q P.s (ofComplex (⟨x,y⟩:ℂ))) =
      reflectedCompletedLambda (2*P.s-1)*(y:ℂ)^(-P.s-1)*nativeSquareCutoffHeight q y := by
  have hy0 : 0 < y := lt_trans (by norm_num : (0:ℝ)<2) hy
  have he (x : ℝ) : nativeCutoffUpperPair q P.s (ofComplex (⟨x,y⟩:ℂ)) =
      nativeSquareCutoffHeight q y*periodize (cuspHeightSeed (lowCuspPower P.s)) (ofComplex (⟨x,y⟩:ℂ)) := by
    rw [nativeCutoffUpperPair,point_im x y hy0]
  simp_rw [he]
  rw [integral_const_mul]
  have hm := lowCuspPower_completed_mean P y hy.le
  rw [integral_const_mul] at hm
  calc
    _ = (y^(2 : ℕ))⁻¹ • (nativeSquareCutoffHeight q y*(reflectedCompletedLambda (2*P.s)*
        ∫ x in Ico (0:ℝ) 1, periodize (cuspHeightSeed (lowCuspPower P.s)) (ofComplex (⟨x,y⟩:ℂ)))) := by
      simp only [Complex.real_smul]
      ring
    _ = (y^(2 : ℕ))⁻¹ • ((y:ℂ)^(1-P.s)*(reflectedCompletedLambda (2*P.s-1)*nativeSquareCutoffHeight q y)) := by
      rw [hm]
      congr 1
      ring
    _ = _ := by
      rw [density_power _ _ hy0,show (1-P.s)-2 = -P.s-1 by ring]
      ring

/-- The reverse original strip evaluates to the admitted reflected native height moment. -/
theorem nativeCutoffUpperPair_eq_reflected_mellin (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    reflectedCompletedLambda (2*s)*(∫ z : UpperHalfPlane in modularStrip, nativeCutoffUpperPair q s z) =
      reflectedCompletedLambda (2*s-1)*∫ y in Ioi (2:ℝ), (y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨s,by linarith⟩
  rw [setIntegral_modularStrip_eq_iterated _ (nativeCutoffUpperPair_integrable q s hs),← integral_const_mul]
  have he : (∫ y in Ioi (0:ℝ), reflectedCompletedLambda (2*s)*((y^(2 : ℕ))⁻¹ •
      ∫ x in Ico (0:ℝ) 1, nativeCutoffUpperPair q s (ofComplex (⟨x,y⟩:ℂ)))) =
      ∫ y in Ioi (0:ℝ), (Ioi (2:ℝ)).indicator
        (fun y : ℝ => reflectedCompletedLambda (2*s-1)*(y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y) y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    by_cases hh : 2 < y
    · rw [Set.indicator_of_mem (s := Ioi (2:ℝ)) hh]
      exact upper_density q P hh
    · rw [Set.indicator_of_notMem (s := Ioi (2:ℝ)) hh]
      have hz (x : ℝ) : nativeCutoffUpperPair q s (ofComplex (⟨x,y⟩:ℂ)) = 0 :=
        nativeCutoffUpperPair_zero q s _ (by rw [point_im x y hy]; exact le_of_not_gt hh)
      simp [hz]
  rw [he,setIntegral_indicator measurableSet_Ioi]
  have hset : Ioi (0:ℝ) ∩ Ioi (2:ℝ) = Ioi (2:ℝ) :=
    inter_eq_right.mpr (fun y hy => lt_trans (by norm_num : (0:ℝ)<2) hy)
  rw [hset]
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

/-- The full original cutoff orbit contribution has its derived reflected Mellin value for every Xi source. -/
theorem nativeCutoffOrbit_mellin_value (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    reflectedCompletedLambda (2*s)*
      (∫ y in Ioc (0:ℝ) (1/2:ℝ), (y:ℂ)^(s-2)*squareCutoffStripMean q y) =
      reflectedCompletedLambda (2*s-1)*
        ∫ y in Ioi (2:ℝ), (y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y := by
  rw [← nativeCutoffLowerPair_eq_mellin q s hs,nativeCutoffPairing_unfold_both q s hs]
  exact nativeCutoffUpperPair_eq_reflected_mellin q s hs

end
end RHTower.D4BMJointSource
