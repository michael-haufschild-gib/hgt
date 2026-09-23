import GaloisForLFunctions.HTGeometry.FirstEndpointMellinLimit
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceMomentSpatial
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalForcedBoundaryPairing

/-! The original native radial source pairing has a source-determined horizon finite part. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric MeasureTheory GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The left horizon mode paired with the literal forcing in the original radial equation. -/
def continuedHorizonSourcePairing (s chi a J K w : ℂ) (b : ℝ) : ℂ :=
  radialPairingWeight b*horizon w chi b*((Real.sqrt (1-b):ℂ)*continuedSourceProfile s a J K w b/2)

/-- The source-determined finite part, with the original fixed onset and radial normalization. -/
def continuedHorizonSourcePhase (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  firstEndpointMellin (horizonMellinCore s chi a J K) b w*
    (1/(w-2*s)+onsetCorrection (2*s) w)/2

/-- The exact horizon endpoint term of the actual source, retained before taking a cutoff limit. -/
def continuedHorizonSourceCounterterm (s chi a J K w : ℂ) (b : ℝ) : ℂ :=
  horizonMellinCore s chi a J K w 0*(b:ℂ)^(w+1)/(w+1)*
    (1/(w-2*s)+onsetCorrection (2*s) w)/2

/-- The original Green weight cancels exactly the square root in its actual forcing. -/
theorem continuedHorizonSourcePairing_eq_mellin (s chi a J K w : ℂ)
    {b : ℝ} (hb : b ∈ Ioo 0 1) :
    continuedHorizonSourcePairing s chi a J K w b =
      (b:ℂ)^w*horizonMellinCore s chi a J K w b*(1/(w-2*s)+onsetCorrection (2*s) w)/2 := by
  have hs : (Real.sqrt (1-b):ℂ)^(2 : ℕ)=1-(b:ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hb.2.le)
  have hn : 1-(b:ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hb.2).ne'
  calc
    _ = horizon w chi b*continuedSourceProfile s a J K w b/2 := by
      unfold continuedHorizonSourcePairing radialPairingWeight
      rw [power_half_eq_sqrt (sub_nonneg.mpr hb.2.le)]
      field_simp [hn]
      linear_combination horizon w chi b*continuedSourceProfile s a J K w b*hs
    _ = _ := by rw [horizon_continuedSource_eq_mellin s chi a J K w hb.1]

private theorem core_continuous (s chi a J K w : ℂ) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    ContinuousAt (horizonMellinCore s chi a J K w) b := by
  have hg := (gaussFactor_derivatives_continued (w := w) (chi := chi) false
    (enorm_ofReal_lt_one hb.1 hb.2)).1.comp_ofReal.continuousAt
  exact hg.mul (sourceRemainder_continuous s w a J K 1).continuousAt

/-- Every original cutoff pairing has an exact remainder formula, including its endpoint term. -/
theorem continuedHorizonSource_cutoff_eq (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) {e b : ℝ} (he : 0 < e) (heb : e ≤ b) (hb : b < 1) :
    (∫ t in e..b, continuedHorizonSourcePairing s chi a J K w t)+
      continuedHorizonSourceCounterterm s chi a J K w e =
      continuedHorizonSourcePhase s chi a J K b w-
        firstEndpointMellinRemainder (horizonMellinCore s chi a J K) e w*
          (1/(w-2*s)+onsetCorrection (2*s) w)/2 := by
  obtain ⟨R,C,hR,-,-,hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw (he.trans_le heb) hb
  have hw1 : w+1 ≠ 0 := by intro h; apply hw; have hi := congrArg Complex.im h; simpa using hi
  have h := firstEndpointMellin_cutoff_eq he heb hwre hw1
    (horizonMellinCore_measurable s chi a J K w)
    (fun t ht => core_continuous s chi a J K w ⟨ht.1,ht.2.trans_lt hb⟩)
    (fun t ht => hbound w (mem_ball_self hR) t ⟨ht.1.le,ht.2⟩)
  have hi : (∫ t in e..b, continuedHorizonSourcePairing s chi a J K w t) =
      (∫ t in e..b, (t:ℂ)^w*horizonMellinCore s chi a J K w t)*
        (1/(w-2*s)+onsetCorrection (2*s) w)/2 := by
    rw [← intervalIntegral.integral_mul_const,← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le heb] at ht
    exact continuedHorizonSourcePairing_eq_mellin s chi a J K w ⟨he.trans_le ht.1,ht.2.trans_lt hb⟩
  rw [hi]
  dsimp [continuedHorizonSourceCounterterm,continuedHorizonSourcePhase]
  linear_combination ((1/(w-2*s)+onsetCorrection (2*s) w)/2)*h

/-- The actual cutoff source pairing converges after its forced endpoint restoration. -/
theorem continuedHorizonSource_cutoff_tendsto (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    Tendsto (fun e : ℝ => (∫ t in e..b, continuedHorizonSourcePairing s chi a J K w t)+
      continuedHorizonSourceCounterterm s chi a J K w e)
      (𝓝[>] (0:ℝ)) (𝓝 (continuedHorizonSourcePhase s chi a J K b w)) := by
  obtain ⟨R,C,hR,-,-,hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw hb.1 hb.2
  have hr := firstEndpointMellinRemainder_tendsto_zero hb.1 hwre
    (fun t ht => hbound w (mem_ball_self hR) t ⟨ht.1.le,ht.2⟩)
  have h := (tendsto_const_nhds (x := continuedHorizonSourcePhase s chi a J K b w)).sub
    ((hr.mul_const (1/(w-2*s)+onsetCorrection (2*s) w)).div_const 2)
  simp only [zero_mul,zero_div,sub_zero] at h
  apply h.congr'
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
  exact (continuedHorizonSource_cutoff_eq s chi a J K w hw hwre he0 heb.le hb.2).symm

/-- Horizon finite-part continuation is meromorphic without division by the radial connection. -/
theorem continuedHorizonSourcePhase_meromorphicAt (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    MeromorphicAt (continuedHorizonSourcePhase s chi a J K b) w := by
  have hm := (horizonFirstMellin_analyticAt s chi a J K w hw hwre hb.1 hb.2).meromorphicAt
  have hi : MeromorphicAt (fun u : ℂ => 1/(u-2*s)) w :=
    (show AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) w from analyticAt_const).meromorphicAt.div
      (show AnalyticAt ℂ (fun u : ℂ => u-2*s) w by fun_prop).meromorphicAt
  have hc := ((onsetCorrection_entire (2*s)).analyticAt w).meromorphicAt
  exact (hm.mul (hi.add hc)).div (analyticAt_const.meromorphicAt (f := fun _ : ℂ => (2:ℂ)))

end
end RHTower.D4BMLaplaceRadial
