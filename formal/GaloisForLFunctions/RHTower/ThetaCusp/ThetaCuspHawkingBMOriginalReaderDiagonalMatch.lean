import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalReaderRegularization
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNormalizableHorizonPairing

/-! Identification of the subtracted reader diagonal with the complete original
horizon metric finite part, using the original power and logarithmic counterterms. -/
open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

private theorem cutoff_integral_tendsto {f : ℝ→ℂ} {b : ℝ} (hb : 0<b)
    (hi : IntervalIntegrable f volume 0 b) :
    Tendsto (fun e : ℝ => ∫ z in e..b,f z) (𝓝[>] (0:ℝ)) (𝓝 (∫ z in (0:ℝ)..b,f z)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (show b∈uIcc (0:ℝ) b from right_mem_uIcc)
  have h0 := hc 0 (show (0:ℝ)∈uIcc 0 b from left_mem_uIcc)
  rw [uIcc_of_le hb.le] at h0
  have h := h0.mono Ioo_subset_Icc_self
  rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsGT hb] at h
  have heq : (fun e : ℝ => ∫ z in e..b,f z)=(fun e : ℝ => -(∫ z in b..e,f z)) := by
    funext e
    exact intervalIntegral.integral_symm (f:=f) (μ:=volume) b e
  have hzero : (∫ z in (0:ℝ)..b,f z)= -(∫ z in b..(0:ℝ),f z) :=
    intervalIntegral.integral_symm (f:=f) (μ:=volume) b 0
  rw [heq,hzero]
  exact h.neg

/-- In the right chamber, the subtracted incoming expression is precisely the
original incoming finite part; the additional original power counterterms vanish. -/
theorem readerIncomingPart_original_below (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : 0<w.re) (hs : w-2*s≠0) (hconn : connection w chi≠0) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      readerIncomingPart s chi amp J K w b w=incomingPairingFinitePart s chi amp J K b w := by
  obtain ⟨BS,hBS,hBShalf,hS⟩ := readerResponseCore_common_data s chi amp J K w hw (by linarith) hs
  obtain ⟨RI,BI,hRI,hBI,hBIhalf,hI⟩ := incomingPairingFinitePart_horizon_restoration_below s chi amp J K w hw (by linarith) hs
  refine ⟨min BS BI,lt_min hBS hBI,(min_le_left _ _).trans hBShalf,?_⟩
  intro b hb hbB
  have hbS : b≤BS := hbB.trans (min_le_left _ _)
  have hbI : b≤BI := hbB.trans (min_le_right _ _)
  obtain ⟨R,C,hR,_,hcore⟩ := hS b hb hbS w hw
  obtain ⟨hc,hbound,he⟩ := hcore w (mem_ball_self hR)
  have hmap : 2*(w-1+1)-w=w := by ring
  have hwreal : -1<(w-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  let F := readerMellinCore s chi amp J K w b
  let G := fun z : ℝ => power (w-1) z*readerResponseCore s chi amp J K w b w z
  have hm : Measurable (F (w-1)) := by
    dsimp only [F,readerMellinCore]
    rw [hmap]
    have hm := hc.measurable_piecewise
      (show ContinuousOn (fun _ : ℝ => (0:ℂ)) (Icc (0:ℝ) b)ᶜ from continuousOn_const) measurableSet_Icc
    convert hm using 1
    ext z
    by_cases hz : z∈Icc (0:ℝ) b <;> simp [hz]
  have hF0 : F (w-1) 0=incomingResponseEndpoint s chi amp J K w b/2 := by
    simp only [F,readerMellinCore,Set.indicator_of_mem (show (0:ℝ)∈Icc 0 b from ⟨le_rfl,hb.le⟩),readerResponseCore_zero]
  have hM := firstEndpointMellin_eq_integral (F:=F) (w:=w-1) hb.le hwreal hm (fun z hz => by
    simp only [F,readerMellinCore,
      Set.indicator_of_mem (show z∈Icc (0:ℝ) b from ⟨hz.1.le,hz.2⟩),
      Set.indicator_of_mem (show (0:ℝ)∈Icc 0 b from ⟨le_rfl,hb.le⟩),readerResponseCore_zero,hmap]
    exact hbound z ⟨hz.1.le,hz.2⟩)
  have hreader : readerIncomingPart s chi amp J K w b w=∫ z in (0:ℝ)..b,G z := by
    have hsame : readerIncomingPart s chi amp J K w b w=firstEndpointMellin F b (w-1) := by
      simp only [readerIncomingPart,firstEndpointMellin,readerMellinRemainder,
        show (w+w)/2=w by ring,sub_add_cancel,hF0,power]
      rfl
    rw [hsame,hM,← intervalIntegral.integral_of_le hb.le]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hb.le] at hz
    simp only [F,readerMellinCore,Set.indicator_of_mem hz,hmap,G,power]
  have hi : IntervalIntegrable G volume 0 b :=
    (intervalIntegral.intervalIntegrable_cpow' hwreal).mul_continuousOn
      (hc.mono (by rw [uIcc_of_le hb.le]))
  have hlim := cutoff_integral_tendsto hb hi
  have hpow := (power_tendsto_zero hwr).mono_left
    (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  have hpow1 := (power_tendsto_zero (show 0<(w+1).re by simp only [Complex.add_re,Complex.one_re]; linarith)).mono_left
    (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  have hfull := (hlim.add ((hpow.const_mul (incomingResponseEndpoint s chi amp J K w b/2)).div_const w)).add
    ((hpow1.const_mul ((horizonGaussFirstCoefficient w chi+1/4)*incomingResponseEndpoint s chi amp J K w b+
      incomingResponseSlope s amp J K w/2)).div_const (w+1))
  simp only [mul_zero,zero_div,add_zero] at hfull
  have hold := (hI b hb hbI).2.2.2 w (mem_ball_self hRI) hconn
  rw [hreader]
  apply tendsto_nhds_unique ?_ hold
  apply hfull.congr'
  filter_upwards [Ioo_mem_nhdsGT hb] with e heps
  have hreplace : (∫ z in e..b,continuedResponse s chi amp J K z w*horizon w chi z/
      (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))=∫ z in e..b,G z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le heps.2.le] at hz
    dsimp only
    rw [he hconn z ⟨heps.1.trans_le hz.1,hz.2⟩,
      show (w+w)/2-1=w-1 by ring]
  rw [hreplace]
  rfl

/-- The continuous reader diagonal equals the complete original horizon finite
part. Both branches use one physical cutoff and the original counterterms. -/
theorem readerHorizonRegularPart_original_below (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : 0<w.re) (hs : w-2*s≠0) (hconn : connection w chi≠0) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      ContinuousAt (readerHorizonRegularPart s chi amp J K w b) w ∧
      readerHorizonRegularPart s chi amp J K w b w=normalizableHorizonPairingFinitePart s chi amp J K b w := by
  obtain ⟨BI,hBI,hBIhalf,hI⟩ := readerIncomingPart_original_below s chi amp J K w hw hwr hs hconn
  obtain ⟨BO,hBO,_,hO⟩ := readerOppositeRegularPart_original_below s chi amp J K w hw (by linarith) hs hconn
  obtain ⟨BC,hBC,_,hC⟩ := readerHorizonRegularPart_continuousAt_below s chi amp J K w hw hwr hs
  let B := min BI (min BO BC)
  refine ⟨B,lt_min hBI (lt_min hBO hBC),(min_le_left _ _).trans hBIhalf,?_⟩
  intro b hb hbB
  have hbI : b≤BI := hbB.trans (min_le_left _ _)
  have hbO : b≤BO := hbB.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbC : b≤BC := hbB.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hC b hb hbC,?_⟩
  rw [readerHorizonRegularPart,hI b hb hbI,hO b hb hbO,normalizableHorizonPairingFinitePart]

end
end RHTower.D4BMOriginalSourceResolvent
