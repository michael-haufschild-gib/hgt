import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeFourierCompletedValue
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCutoffMellinValue

/-! The original native period retains its admitted principal and reflected cutoff moments. -/
open Complex MeasureTheory Set UpperHalfPlane
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMCuspProjection
noncomputable section

/-- The original principal subtraction is kept together before its height integral. -/
def nativePrincipalRemainder (q : XiZeroCopy) (y : ℝ) : ℂ :=
  (1-cutoff ![0,y])*principalSquare q ![0,y]

/-- The complete lower orbit correction, extended by zero on the original positive height ray. -/
def nativeLowCutoffMellin (q : XiZeroCopy) (s : ℂ) : ℝ → ℂ :=
  (Ioc (0:ℝ) (1/2:ℝ)).indicator (fun y => (y:ℂ)^(s-2)*squareCutoffStripMean q y)

/-- Absolute strip admission transfers to the actual weighted horizontal mean. -/
theorem residualStripMean_mellin_integrable (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    IntegrableOn (fun y : ℝ => (y:ℂ)^(P.s-2)*residualStripMean q y) (Ioi (0:ℝ)) := by
  have hc := (integrableOn_modularStrip_iff _).mp (residualMellinSeed_integrable q P)
  rw [Measure.volume_eq_prod,IntegrableOn,← Measure.prod_restrict] at hc
  have hm : IntegrableOn (fun y : ℝ => ∫ x in Ico (0:ℝ) 1,
      stripChartIntegrand (residualMellinSeed q P.s) (y,x)) (Ioi (0:ℝ)) := hc.integral_prod_left
  apply hm.congr_fun _ measurableSet_Ioi
  intro y hy
  have he (x : ℝ) : residualMellinSeed q P.s (ofComplex (⟨x,y⟩:ℂ)) =
      (y:ℂ)^P.s*globalSquareResidual q (ofComplex (⟨x,y⟩:ℂ)) := by
    unfold residualMellinSeed
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  simp only [stripChartIntegrand,he,integral_smul,integral_const_mul]
  change (y^(2 : ℕ))⁻¹ • ((y:ℂ)^P.s*residualStripMean q y) = _
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show 0<y from hy).ne'
  have ht : (y:ℂ)^(2:ℂ)=(y:ℂ)^(2 : ℕ) := by norm_cast
  rw [Complex.cpow_sub _ _ hn,ht]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  ring

/-- The original complete lower correction is integrable after extension by zero. -/
theorem nativeLowCutoffMellin_integrable (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (nativeLowCutoffMellin q s) (Ioi (0:ℝ)) :=
  ((nativeCutoffLowerMellin_integrable q s hs).integrable_indicator measurableSet_Ioc).integrableOn

/-- The extended correction has exactly the admitted original lower height integral. -/
theorem nativeLowCutoffMellin_integral (q : XiZeroCopy) (s : ℂ) :
    (∫ y in Ioi (0:ℝ), nativeLowCutoffMellin q s y) =
      ∫ y in Ioc (0:ℝ) (1/2:ℝ), (y:ℂ)^(s-2)*squareCutoffStripMean q y := by
  rw [nativeLowCutoffMellin,setIntegral_indicator measurableSet_Ioc]
  rw [show Ioi (0:ℝ) ∩ Ioc (0:ℝ) (1/2:ℝ) = Ioc (0:ℝ) (1/2:ℝ) from
    inter_eq_right.mpr (fun _ hy => hy.1)]

/-- The actual weighted principal remainder is reconstructed from the complete original source. -/
theorem nativePrincipalRemainder_weighted (q : XiZeroCopy) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^(s-2)*nativePrincipalRemainder q y =
      (y:ℂ)^(s-2)*residualStripMean q y-
        4*((y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ)))+nativeLowCutoffMellin q s y := by
  rw [residualStripMean_eq_fourier q hy]
  by_cases hh : y ≤ 1/2
  · rw [nativeLowCutoffMellin,Set.indicator_of_mem (show y ∈ Ioc (0:ℝ) (1/2:ℝ) from ⟨hy,hh⟩)]
    have hz : cutoff ![0,y] = 0 := by
      unfold cutoff
      rw [Real.smoothTransition.zero_of_nonpos (by change y-2≤0; linarith)]
      simp
    unfold nativePrincipalRemainder principalSquare
    rw [hz]
    ring
  · rw [nativeLowCutoffMellin,Set.indicator_of_notMem (show y ∉ Ioc (0:ℝ) (1/2:ℝ) from fun h => hh h.2),
      squareCutoffStripMean_eq_original_above_half q y (le_of_lt (lt_of_not_ge hh))]
    unfold nativePrincipalRemainder nativeSquareCutoffHeight principalSquare
    ring

/-- The combined original principal subtraction has its own admitted Mellin integral. -/
theorem nativePrincipalRemainder_integrable (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (fun y : ℝ => (y:ℂ)^(s-2)*nativePrincipalRemainder q y) (Ioi (0:ℝ)) := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨s,by linarith⟩
  have hi := ((residualStripMean_mellin_integrable q P).sub
    ((nativeFourierMellin_integrable q s hs).const_mul 4)).add (nativeLowCutoffMellin_integrable q s hs)
  exact hi.congr_fun (fun y hy => (nativePrincipalRemainder_weighted q s hy).symm) measurableSet_Ioi

/-- The original native period is exactly the diagonal plus both original admitted cutoff moments. -/
theorem scalarResidualPeriod_eq_three_moments (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    scalarResidualPeriod q (s-1/2) =
      4*reflectedCompletedLambda (2*s)*
        (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ)))+
      reflectedCompletedLambda (2*s)*(∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*nativePrincipalRemainder q y)-
      reflectedCompletedLambda (2*s-1)*(∫ y in Ioi (2:ℝ), (y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y) := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨s,by linarith⟩
  rw [scalarResidualPeriod_eq_mellin q P]
  change reflectedCompletedLambda (2*s)*(∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*residualStripMean q y) = _
  have he : (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*residualStripMean q y) =
      ∫ y in Ioi (0:ℝ), ((y:ℂ)^(s-2)*nativePrincipalRemainder q y+
        4*((y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ))))-nativeLowCutoffMellin q s y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [nativePrincipalRemainder_weighted q s hy]
    ring
  have hadd : IntegrableOn (fun y : ℝ => (y:ℂ)^(s-2)*nativePrincipalRemainder q y+
      4*((y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ)))) (Ioi (0:ℝ)) :=
    (nativePrincipalRemainder_integrable q s hs).add ((nativeFourierMellin_integrable q s hs).const_mul 4)
  rw [he,integral_sub hadd (nativeLowCutoffMellin_integrable q s hs),
    integral_add (nativePrincipalRemainder_integrable q s hs) ((nativeFourierMellin_integrable q s hs).const_mul 4),
    integral_const_mul,nativeLowCutoffMellin_integral,mul_sub,mul_add,nativeCutoffOrbit_mellin_value q s hs]
  ring

/-- The full original period has the half four-Lambda value with its exact surviving cutoff correction. -/
theorem scalarResidualPeriod_fourLambda_with_cutoff (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re)
    (s : ℂ) (hs : 2 < s.re) :
    scalarResidualPeriod q (s-1/2) =
      (reflectedCompletedLambda (s+2*center q)*reflectedCompletedLambda s^(2 : ℕ)*
        reflectedCompletedLambda (s-2*center q))/2+
      reflectedCompletedLambda (2*s)*(∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*nativePrincipalRemainder q y)-
      reflectedCompletedLambda (2*s-1)*(∫ y in Ioi (2:ℝ), (y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y) := by
  rw [scalarResidualPeriod_eq_three_moments q s hs,nativeDiagonalPeriod_fourLambda q hq s hs]

end
end RHTower.D4BMJointSource
