import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalReaderDiagonalMatch
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalWholeSourceResolvent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalHorizonGreenMatch

/-! The full original source identity after subtracting its precise reader pole. -/
open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial GaloisForLFunctions.HTGeometry D4BMOriginalHorizonGreenMatch D4BMModularCore
noncomputable section
set_option autoImplicit false

private theorem interval_congr_Ioo {f g : ℝ→ℂ} {a b : ℝ} (hab : a≤b)
    (hf : IntervalIntegrable f volume a b) (he : ∀ z∈Ioo a b, f z=g z) :
    IntervalIntegrable g volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hf).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact he z hz

/-- Independent incoming readers are admitted on one source-derived family
of cutoffs, and their integral is the actual subtracted Mellin expression. -/
theorem readerIncomingPart_integral_below (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) (hconn : connection w chi≠0) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      ∀ v : ℂ, v.im≠0 → 0<(w+v).re →
      IntervalIntegrable (fun z : ℝ => continuedResponse s chi amp J K z w*horizon v chi z/
        (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))) volume 0 b ∧
      (∫ z in (0:ℝ)..b,continuedResponse s chi amp J K z w*horizon v chi z/
        (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))=readerIncomingPart s chi amp J K w b v := by
  obtain ⟨B,hB,hBhalf,hS⟩ := readerResponseCore_common_data s chi amp J K w hw hwr hs
  refine ⟨B,hB,hBhalf,?_⟩
  intro b hb hbB v hv hplus
  obtain ⟨R,C,hR,_,hcore⟩ := hS b hb hbB v hv
  obtain ⟨hc,hbound,he⟩ := hcore v (mem_ball_self hR)
  let a : ℂ := (w+v)/2-1
  have hmap : 2*(a+1)-w=v := by dsimp [a]; ring
  have ha : -1<a.re := by
    have hh : 0<((w+v)/2).re := by simpa using half_pos hplus
    dsimp only [a]
    simp only [Complex.sub_re,Complex.one_re]
    linarith
  let F := readerMellinCore s chi amp J K w b
  let G := fun z : ℝ => power a z*readerResponseCore s chi amp J K w b v z
  have hm : Measurable (F a) := by
    dsimp only [F,readerMellinCore]
    rw [hmap]
    have hm := hc.measurable_piecewise
      (show ContinuousOn (fun _ : ℝ => (0:ℂ)) (Icc (0:ℝ) b)ᶜ from continuousOn_const) measurableSet_Icc
    convert hm using 1
    ext z
    by_cases hz : z∈Icc (0:ℝ) b <;> simp [hz]
  have hF0 : F a 0=incomingResponseEndpoint s chi amp J K w b/2 := by
    simp only [F,readerMellinCore,Set.indicator_of_mem (show (0:ℝ)∈Icc 0 b from ⟨le_rfl,hb.le⟩),readerResponseCore_zero]
  have hM := firstEndpointMellin_eq_integral (F:=F) (w:=a) hb.le ha hm (fun z hz => by
    simp only [F,readerMellinCore,
      Set.indicator_of_mem (show z∈Icc (0:ℝ) b from ⟨hz.1.le,hz.2⟩),
      Set.indicator_of_mem (show (0:ℝ)∈Icc 0 b from ⟨le_rfl,hb.le⟩),readerResponseCore_zero,hmap]
    exact hbound z ⟨hz.1.le,hz.2⟩)
  have hreader : readerIncomingPart s chi amp J K w b v=∫ z in (0:ℝ)..b,G z := by
    have hsame : readerIncomingPart s chi amp J K w b v=firstEndpointMellin F b a := by
      simp only [readerIncomingPart,firstEndpointMellin,readerMellinRemainder,hF0,a,sub_add_cancel,power]
      rfl
    rw [hsame,hM,← intervalIntegral.integral_of_le hb.le]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hb.le] at hz
    simp only [F,readerMellinCore,Set.indicator_of_mem hz,hmap,G,power]
  have hi : IntervalIntegrable G volume 0 b :=
    (intervalIntegral.intervalIntegrable_cpow' ha).mul_continuousOn
      (hc.mono (by rw [uIcc_of_le hb.le]))
  have heq (z : ℝ) (hz : z∈Ioo (0:ℝ) b) :
      G z=continuedResponse s chi amp J K z w*horizon v chi z/
        (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)) := (he hconn z ⟨hz.1,hz.2.le⟩).symm
  refine ⟨interval_congr_Ioo hb.le hi heq,?_⟩
  rw [hreader]
  exact intervalIntegral.integral_congr_Ioo_of_le hb.le (fun z hz => (heq z hz).symm)

/-- Exact pole, including its coefficient, before taking the reader diagonal. -/
theorem readerIncomingPart_neg_eq (s chi amp J K w v : ℂ) (b : ℝ) (h : w-v≠0) :
    readerIncomingPart s chi amp J K w b (-v)=
      readerOppositeRegularPart s chi amp J K w b v+
        incomingResponseEndpoint s chi amp J K w b/(w-v) := by
  have hd : (w-v)/2≠0 := div_ne_zero h (by norm_num)
  rw [readerIncomingPart,readerOppositeRegularPart,show w+-v=w-v by ring,
    dslope_of_ne _ hd,slope_def_field]
  simp only [power,Complex.cpow_zero,sub_zero]
  field_simp
  ring

/-- Full physical pairing with its prescribed horizon pole removed. -/
def readerFullRegularPart (s chi amp J K w : ℂ) (b : ℝ) (v : ℂ) : ℂ :=
  readerHorizonRegularPart s chi amp J K w b v+
    ∫ z in b..1,mixedDensity s chi amp J K w v z

/-- Full exterior source identity after exact pole subtraction. Integrability,
the pole coefficient, and both physical endpoint contributions are derived. -/
theorem readerFullRegularPart_source_identity_below (s chi amp J K w : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hs : (2*s).re<w.re) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      ∀ v : ℂ, Chamber v chi → v.im≠0 → 0<(w+v).re → 0<(w-v).re →
      (v^(2 : ℕ)-w^(2 : ℕ))*readerFullRegularPart s chi amp J K w b v=
        (∫ z in (0:ℝ)..1,sourceDensity s chi amp J K w v z)+
          (v+w)*incomingResponseEndpoint s chi amp J K w b*(connection v chi/(2*v)) := by
  have hwr : -2<w.re := by linarith [chamber_re_pos hw]
  have hsp : w-2*s≠0 := sub_ne_zero.mpr (fun he => by rw [he] at hs; exact (lt_irrefl _ hs))
  obtain ⟨B,hB,hBhalf,hI⟩ := readerIncomingPart_integral_below s chi amp J K w hwi hwr hsp (connection_ne_zero hw)
  refine ⟨B,hB,hBhalf,?_⟩
  intro b hb hbB v hv hvi hplus hminus
  have hb1 : b<1 := lt_of_le_of_lt (hbB.trans hBhalf) (by norm_num)
  have hvni : (-v).im≠0 := by simpa using hvi
  obtain ⟨hiP,heP⟩ := hI b hb hbB v hvi hplus
  obtain ⟨hiM,heM⟩ := hI b hb hbB (-v) hvni (by simpa only [sub_eq_add_neg] using hminus)
  let A := horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)
  let beta := connection v chi/(2*v)
  have hsplit (z : ℝ) (hz : z∈Ioo (0:ℝ) b) :
      mixedDensity s chi amp J K w v z=
      A*(continuedResponse s chi amp J K z w*horizon v chi z/(2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))+
      beta*(continuedResponse s chi amp J K z w*horizon (-v) chi z/(2*(z:ℂ)*(Real.sqrt (1-z):ℂ))) := by
    have hn := (original_homogeneous_horizon_representation v chi hvi
      (fun z hz => (normalizable_derivatives_continued hz).1)
      (fun z hz => (normalizable_derivatives_continued hz).2)
      (fun z hz => normalizable_equation_continued hz) ⟨hz.1,hz.2.trans hb1⟩).1
    rw [normalizable_opposite_coefficient v chi hvi] at hn
    rw [mixedDensity,hn]
    dsimp only [A,beta]
    ring
  have hleft : (∫ z in (0:ℝ)..b,mixedDensity s chi amp J K w v z)=
      A*readerIncomingPart s chi amp J K w b v+beta*readerIncomingPart s chi amp J K w b (-v) := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hb.le hsplit,
      intervalIntegral.integral_add (hiP.const_mul A) (hiM.const_mul beta),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,heP,heM]
  have hdiff : w-v≠0 := by intro he; rw [he] at hminus; simp at hminus
  rw [readerIncomingPart_neg_eq s chi amp J K w v b hdiff] at hleft
  obtain ⟨hi,_,hwhole⟩ := whole_source_resolvent s chi amp J K w v hw hv hwi hvi hs hplus hminus
  have hi0b : IntervalIntegrable (mixedDensity s chi amp J K w v) volume 0 b :=
    hi.mono_set (by rw [uIcc_of_le hb.le,uIcc_of_le (by norm_num : (0:ℝ)≤1)]; exact Icc_subset_Icc le_rfl hb1.le)
  have hib1 : IntervalIntegrable (mixedDensity s chi amp J K w v) volume b 1 :=
    hi.mono_set (by rw [uIcc_of_le hb1.le,uIcc_of_le (by norm_num : (0:ℝ)≤1)]; exact Icc_subset_Icc hb.le le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0b hib1
  have htotal : (∫ z in (0:ℝ)..1,mixedDensity s chi amp J K w v z)=
      readerFullRegularPart s chi amp J K w b v+beta*incomingResponseEndpoint s chi amp J K w b/(w-v) := by
    rw [← hadd,hleft,readerFullRegularPart,readerHorizonRegularPart]
    dsimp only [A,beta]
    ring
  rw [htotal] at hwhole
  have hpole : (v^(2 : ℕ)-w^(2 : ℕ))*(beta*incomingResponseEndpoint s chi amp J K w b/(w-v))=
      -(v+w)*incomingResponseEndpoint s chi amp J K w b*beta := by
    field_simp
    ring
  rw [mul_add,hpole] at hwhole
  dsimp only [beta] at hwhole
  linear_combination hwhole

/-- Every smaller physical cutoff extracts the same actual horizon amplitude,
uniformly on a source-frequency neighborhood. -/
theorem incomingResponseEndpoint_eq_amplitude_below (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    ∃ R B : ℝ, 0<R ∧ 0<B ∧ B≤1/2 ∧
      ∀ u∈ball w R, connection u chi≠0 → ∀ b : ℝ, 0<b → b≤B →
        incomingResponseEndpoint s chi amp J K u b=greenHorizonAmplitude s chi amp J K u := by
  obtain ⟨R,B,C,M,hR,hB,hBhalf,_,_,hdata⟩ := incomingSourcePrimitive_common_data s chi amp J K w hw hwr hs
  refine ⟨R,B,hR,hB,hBhalf,?_⟩
  intro u hu hc b hb hbB
  obtain ⟨_,_,_,hp,he⟩ := hdata u hu
  have hP := (hp 0 ⟨le_rfl,hB.le⟩).mono Ioo_subset_Icc_self
  rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsGT hB] at hP
  simp only [incomingSourcePrimitive,intervalIntegral.integral_same] at hP
  have ht := hP.const_add (incomingResponseEndpoint s chi amp J K u B)
  simp only [add_zero] at ht
  have hlim : Tendsto (fun z : ℝ => continuedResponse s chi amp J K z u/horizon u chi z)
      (𝓝[>] (0:ℝ)) (𝓝 (incomingResponseEndpoint s chi amp J K u B)) := by
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsGT hB] with z hz
    exact ((he z ⟨hz.1,hz.2.le⟩).2.2.2 hc).symm
  have hEb : incomingResponseEndpoint s chi amp J K u b=incomingResponseEndpoint s chi amp J K u B := by
    change continuedResponse s chi amp J K b u/horizon u chi b-incomingSourcePrimitive s chi amp J K u b=_
    rw [(he b ⟨hb,hbB⟩).2.2.2 hc]
    ring
  exact hEb.trans hlim.limUnder_eq.symm

/-- The diagonal source overlap is the literal horizon Green amplitude;
source admission and normalization are derived from the original Green integral. -/
theorem sourceDensity_diagonal_amplitude (s chi amp J K v : ℂ)
    (hv : Chamber v chi) (hvi : v.im≠0) (hs : (2*s).re<v.re) :
    IntervalIntegrable (sourceDensity s chi amp J K v v) volume 0 1 ∧
    (∫ z in (0:ℝ)..1,sourceDensity s chi amp J K v v z)=
      -connection v chi*greenHorizonAmplitude s chi amp J K v := by
  let f := fun z : ℝ => normalizable v chi z*sourceProfile s v amp J K (onsetTransform (2*s) v) z/(-connection v chi)
  have hi : IntervalIntegrable f volume 0 1 := (greenIntegrands_intervalIntegrable hv s amp J K (onsetTransform (2*s) v)).2
  have he (z : ℝ) : sourceDensity s chi amp J K v v z=(-connection v chi)*f z := by
    rw [sourceDensity,continuedSourceProfile_eq s amp J K v hs]
    dsimp only [f]
    field_simp [connection_ne_zero hv]
  refine ⟨?_,?_⟩
  · exact (hi.const_mul (-connection v chi)).congr (fun z _ => (he z).symm)
  · rw [greenHorizonAmplitude_eq_original hv s amp J K hvi (by linarith [chamber_re_pos hv]) hs,outerMoment]
    rw [intervalIntegral.integral_congr (fun z _ => he z),intervalIntegral.integral_const_mul]

/-- The actual temporal-corner difference cancels the diagonal source overlap
before taking any singular limit. The right side contains only literal sources. -/
theorem readerFullRegularPart_source_difference_below (s chi amp J K w : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hs : (2*s).re<w.re) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      ∀ v : ℂ, Chamber v chi → v.im≠0 → (2*s).re<v.re →
      0<(w+v).re → 0<(w-v).re →
      (v+w)*readerFullRegularPart s chi amp J K w b v+
        connection v chi*(greenHorizonAmplitude s chi amp J K v-
          (v+w)*greenHorizonAmplitude s chi amp J K w/(2*v))/(v-w)=
        -(∫ z in (0:ℝ)..1,normalizable v chi z*
          (continuedSourceProfile s amp J K v z-continuedSourceProfile s amp J K w z)/(v-w)) := by
  have hwr : -2<w.re := by linarith [chamber_re_pos hw]
  have hsp : w-2*s≠0 := sub_ne_zero.mpr (fun he => by rw [he] at hs; exact (lt_irrefl _ hs))
  obtain ⟨BI,hBI,hBIhalf,hI⟩ := readerFullRegularPart_source_identity_below s chi amp J K w hw hwi hs
  obtain ⟨R,BE,hR,hBE,_,hE⟩ := incomingResponseEndpoint_eq_amplitude_below s chi amp J K w hwi hwr hsp
  refine ⟨min BI BE,lt_min hBI hBE,(min_le_left _ _).trans hBIhalf,?_⟩
  intro b hb hbB v hv hvi hsv hplus hminus
  have hid := hI b hb (hbB.trans (min_le_left _ _)) v hv hvi hplus hminus
  rw [hE w (mem_ball_self hR) (connection_ne_zero hw) b hb (hbB.trans (min_le_right _ _))] at hid
  obtain ⟨hiD,hD⟩ := sourceDensity_diagonal_amplitude s chi amp J K v hv hvi hsv
  have hiW := sourceDensity_whole_integrable s chi amp J K w v hv hvi hplus hminus
  have heq : (∫ z in (0:ℝ)..1,normalizable v chi z*
      (continuedSourceProfile s amp J K v z-continuedSourceProfile s amp J K w z)/(v-w))=
      ((∫ z in (0:ℝ)..1,sourceDensity s chi amp J K v v z)-
        (∫ z in (0:ℝ)..1,sourceDensity s chi amp J K w v z))/(v-w) := by
    rw [← intervalIntegral.integral_sub hiD hiW,← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro z _
    dsimp only [sourceDensity]
    ring
  rw [heq,hD]
  have hv0 : v≠0 := by intro he; exact hvi (by simp [he])
  have hvw : v-w≠0 := by
    intro he
    have hsame : w=v := (sub_eq_zero.mp he).symm
    rw [hsame,sub_self] at hminus
    simp at hminus
  have hJ : (∫ z in (0:ℝ)..1,sourceDensity s chi amp J K w v z)=
      (v^(2 : ℕ)-w^(2 : ℕ))*readerFullRegularPart s chi amp J K w b v-
        (v+w)*greenHorizonAmplitude s chi amp J K w*(connection v chi/(2*v)) := by
    linear_combination -hid
  rw [hJ]
  field_simp [hvw,hv0]
  ring


end
end RHTower.D4BMOriginalSourceResolvent
