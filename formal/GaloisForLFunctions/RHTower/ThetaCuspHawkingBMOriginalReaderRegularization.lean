import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOppositePairingFactor
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingHorizonExpansion
import GaloisForLFunctions.HTGeometry.FirstEndpointMellin
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceResolventEndpoints
import Mathlib.Analysis.Calculus.DSlope
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOppositePairingFinitePart

/-! The actual forced response paired with an independent reader has a uniformly
linear horizon remainder after its original endpoint coefficient is removed. -/
open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

def mixedGaussPairingFactor (w v chi : ℂ) (z : ℝ) : ℂ :=
  gaussFactor w chi false (z:ℂ)*gaussFactor v chi false (z:ℂ)/(2*(Real.sqrt (1-z):ℂ))

/-- The actual incoming/opposite product has one common linear bound at its logarithmic endpoint. -/
theorem mixedGaussPairingFactor_uniform_first_bound (w v chi : ℂ) (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    ∃ R C M : ℝ, 0 < R ∧ 0 ≤ C ∧ 0 ≤ M ∧
      ∀ u ∈ ball v R, ∀ z ∈ Icc (0:ℝ) (1/2),
        ‖mixedGaussPairingFactor w u chi z-(1/2:ℂ)‖ ≤ C*z ∧
        ‖mixedGaussPairingFactor w u chi z‖ ≤ M := by
  obtain ⟨Rp,Cp,hRp,hCp,hp⟩ := horizonGauss_uniform_first_bound w chi hw
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨Rm,Cm,hRm,hCm,hm⟩ := horizonGauss_uniform_first_bound v chi hv
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  let S := Cp*(Cm+1)+Cm
  let C := 2*S+9/4
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨Rm,C,C+1,hRm,hC,by positivity,?_⟩
  intro u hu z hz
  have hep := hp w (mem_ball_self hRp) z hz
  have hem := hm u hu z hz
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ 1 := by linarith [hz.2]
  let gp := gaussFactor w chi false (z:ℂ)
  let gm := gaussFactor u chi false (z:ℂ)
  let j : ℂ := 1/(2*(Real.sqrt (1-z):ℂ))
  have hgm : ‖gm‖ ≤ Cm+1 := by
    have hn := norm_sub_norm_le gm (1:ℂ)
    rw [norm_one] at hn
    dsimp only [gm] at hn ⊢
    linarith [mul_le_mul_of_nonneg_left hz1 hCm]
  have hprod : ‖gp*gm-1‖ ≤ S*z := by
    rw [show gp*gm-1=(gp-1)*gm+(gm-1) by ring]
    calc
      _ ≤ ‖(gp-1)*gm‖+‖gm-1‖ := norm_add_le _ _
      _ = ‖gp-1‖*‖gm‖+‖gm-1‖ := by rw [norm_mul]
      _ ≤ (Cp*z)*(Cm+1)+Cm*z := by gcongr
      _ = S*z := by dsimp [S]; ring
  have hj : ‖j-(1/2:ℂ)‖ ≤ (9/4:ℝ)*z := by
    have he := inverse_sqrt_jacobian_second_bound hz
    have hn := norm_sub_norm_le (j-(1/2:ℂ)) ((1/4:ℂ)*(z:ℂ))
    rw [norm_mul,show ‖(1/4:ℂ)‖=(1/4:ℝ) by norm_num,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1] at hn
    change ‖j-(1/2:ℂ)-(1/4:ℂ)*(z:ℂ)‖ ≤ 2*z^2 at he
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  have hjb : ‖j‖ ≤ 2 := by
    have hn := norm_sub_norm_le j (1/2:ℂ)
    rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num] at hn
    nlinarith [hz.2]
  have hV : ‖mixedGaussPairingFactor w u chi z-(1/2:ℂ)‖ ≤ C*z := by
    calc
      _ = ‖(gp*gm-1)*j+(j-(1/2:ℂ))‖ := by
        congr 1
        dsimp [mixedGaussPairingFactor,gp,gm,j]
        ring
      _ ≤ ‖(gp*gm-1)*j‖+‖j-(1/2:ℂ)‖ := norm_add_le _ _
      _ = ‖gp*gm-1‖*‖j‖+‖j-(1/2:ℂ)‖ := by rw [norm_mul]
      _ ≤ (S*z)*2+(9/4:ℝ)*z := by gcongr
      _ = C*z := by dsimp [C]; ring
  refine ⟨hV,?_⟩
  have hn := norm_sub_norm_le (mixedGaussPairingFactor w u chi z) (1/2:ℂ)
  rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num] at hn
  linarith [mul_le_mul_of_nonneg_left hz1 hC]

/-- Fixed-source core; the reader is the sole varying frequency. -/
def readerResponseCore (s chi amp J K w : ℂ) (b : ℝ) (v : ℂ) (z : ℝ) : ℂ :=
  (incomingResponseEndpoint s chi amp J K w b+incomingSourcePrimitive s chi amp J K w z)*
    mixedGaussPairingFactor w v chi z

@[simp] theorem readerResponseCore_zero (s chi amp J K w : ℂ) (b : ℝ) (v : ℂ) :
    readerResponseCore s chi amp J K w b v 0=incomingResponseEndpoint s chi amp J K w b/2 := by
  simp [readerResponseCore,mixedGaussPairingFactor,incomingSourcePrimitive,gaussFactor_zero,div_eq_mul_inv]

private theorem mixedGaussPairingFactor_cont (w v chi : ℂ) {b : ℝ} (hb : b<1) :
    ContinuousOn (mixedGaussPairingFactor w v chi) (Icc (0:ℝ) b) := by
  intro z hz
  have hn : ‖(z:ℂ)‖ₑ<1 := by
    rw [← ofReal_norm,Complex.norm_real,Real.norm_of_nonneg hz.1]
    exact ENNReal.ofReal_lt_one.mpr (hz.2.trans_lt hb)
  exact (((gaussFactor_derivatives_continued (w:=w) (chi:=chi) false hn).1.comp_ofReal.continuousAt.mul
    (gaussFactor_derivatives_continued (w:=v) (chi:=chi) false hn).1.comp_ofReal.continuousAt).div
    (show ContinuousAt (fun t : ℝ => 2*(Real.sqrt (1-t):ℂ)) z by fun_prop)
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by linarith [hz.2])).ne'))).continuousWithinAt

/-- Source-derived, uniform reader control of the precise core of the original
mixed radial pairing. No asymptotic coefficient or remainder bound is assumed. -/
theorem readerResponseCore_common_data (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧
      ∀ b : ℝ, 0<b → b≤B → ∀ v : ℂ, v.im≠0 →
      ∃ R C : ℝ, 0<R ∧ 0≤C ∧ ∀ u∈ball v R,
        ContinuousOn (readerResponseCore s chi amp J K w b u) (Icc (0:ℝ) b) ∧
        (∀ z∈Icc (0:ℝ) b,
          ‖readerResponseCore s chi amp J K w b u z-incomingResponseEndpoint s chi amp J K w b/2‖≤C*z) ∧
        (connection w chi≠0 → ∀ z∈Ioc (0:ℝ) b,
          continuedResponse s chi amp J K z w*horizon u chi z/(2*(z:ℂ)*(Real.sqrt (1-z):ℂ))=
            power ((w+u)/2-1) z*readerResponseCore s chi amp J K w b u z) := by
  obtain ⟨RP,bP,CP,MP,hRP,hbP,hbPhalf,_,hMP,hP⟩ := incomingSourcePrimitive_common_data s chi amp J K w hw hwr hs
  obtain ⟨RG,bG,CG,hRG,hbG,_,_,hG⟩ := horizonGauss_uniform_nonzero w chi hw
  let B := min bP bG
  refine ⟨B,lt_min hbP hbG,(min_le_left _ _).trans hbPhalf,?_⟩
  intro b hb hbB v hv
  obtain ⟨R,CF,MF,hR,hCF,hMF,hF⟩ := mixedGaussPairingFactor_uniform_first_bound w v chi hw hv
  have hbp : b≤bP := hbB.trans (min_le_left _ _)
  have hbg : b≤bG := hbB.trans (min_le_right _ _)
  have hbhalf : b≤1/2 := hbp.trans hbPhalf
  have hb1 : b<1 := lt_of_le_of_lt hbhalf (by norm_num)
  let E := incomingResponseEndpoint s chi amp J K w b
  let C := ‖E‖*CF+MP*MF
  have hC : 0≤C := by dsimp [C]; positivity
  obtain ⟨_,_,_,hPc,hPd⟩ := hP w (mem_ball_self hRP)
  have hQ (z : ℝ) (hz : z∈Ioc (0:ℝ) b) (hc : connection w chi≠0) :
      continuedResponse s chi amp J K z w/horizon w chi z=
        E+incomingSourcePrimitive s chi amp J K w z := by
    have hqz := (hPd z ⟨hz.1,hz.2.trans hbp⟩).2.2.2 hc
    have hqb := (hPd b ⟨hb,hbp⟩).2.2.2 hc
    dsimp only [E,incomingResponseEndpoint]
    rw [hqz,hqb]
    dsimp only [incomingSourcePrimitive]
    ring
  refine ⟨R,C,hR,hC,?_⟩
  intro u hu
  refine ⟨?_,?_,?_⟩
  · exact (continuousOn_const.add (hPc.mono (Icc_subset_Icc le_rfl hbp))).mul
      (mixedGaussPairingFactor_cont w u chi hb1)
  · intro z hz
    by_cases hz0 : z=0
    · subst z
      simp
    have hzpos : 0<z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
    have hPn := (hPd z ⟨hzpos,hz.2.trans hbp⟩).2.1
    obtain ⟨hFe,hFn⟩ := hF u hu z ⟨hz.1,hz.2.trans hbhalf⟩
    calc
      _ = ‖E*(mixedGaussPairingFactor w u chi z-1/2)+
          incomingSourcePrimitive s chi amp J K w z*mixedGaussPairingFactor w u chi z‖ := by
        congr 1
        dsimp [readerResponseCore,E]
        ring
      _ ≤ ‖E*(mixedGaussPairingFactor w u chi z-1/2)‖+
          ‖incomingSourcePrimitive s chi amp J K w z*mixedGaussPairingFactor w u chi z‖ := norm_add_le _ _
      _ = ‖E‖*‖mixedGaussPairingFactor w u chi z-1/2‖+
          ‖incomingSourcePrimitive s chi amp J K w z‖*‖mixedGaussPairingFactor w u chi z‖ := by rw [norm_mul,norm_mul]
      _ ≤ ‖E‖*(CF*z)+(MP*z)*MF := by gcongr
      _ = C*z := by dsimp [C]; ring
  · intro hc z hz
    have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
    have hgne : gaussFactor w chi false (z:ℂ)≠0 := by
      have hn := (hG w (mem_ball_self hRG) z ⟨hz.1.le,hz.2.trans hbg⟩).2.1
      exact norm_pos_iff.mp (by linarith)
    have hh : horizon w chi z≠0 := mul_ne_zero (power_ne_zero _ hz.1) hgne
    have hy := (div_eq_iff hh).mp (hQ z hz hc)
    have hp : power ((w+u)/2-1) z=power (w/2) z*power (u/2) z/(z:ℂ) := by
      dsimp only [power]
      rw [Complex.cpow_sub _ _ hz0,Complex.cpow_one,← Complex.cpow_add _ _ hz0]
      congr 1
      ring
    rw [hy,hp]
    dsimp only [readerResponseCore,mixedGaussPairingFactor,horizon,dress,E]
    ring

/-- Holomorphy varies only the reader; the full forced-response source is fixed. -/
theorem readerResponseCore_frequency_differentiableAt (s chi amp J K w : ℂ) (b : ℝ)
    (v : ℂ) (hv : v.im≠0) {z : ℝ} (hz : z∈Icc (0:ℝ) b) (hb : b<1) :
    DifferentiableAt ℂ (fun u => readerResponseCore s chi amp J K w b u z) v := by
  have hn : ‖(z:ℂ)‖<1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg hz.1]
    exact hz.2.trans_lt hb
  have hG := horizonGauss_frequency_differentiableAt v chi (z:ℂ) hv hn
  exact ((hG.const_mul (gaussFactor w chi false (z:ℂ))).div_const
    (2*(Real.sqrt (1-z):ℂ))).const_mul
    (incomingResponseEndpoint s chi amp J K w b+incomingSourcePrimitive s chi amp J K w z)

/-- An auxiliary extension outside the integration interval; on `[0,b]` it
is exactly the original fixed-source, independent-reader core. -/
def readerMellinCore (s chi amp J K w : ℂ) (b : ℝ) (u : ℂ) : ℝ→ℂ :=
  (Icc (0:ℝ) b).indicator (readerResponseCore s chi amp J K w b (2*(u+1)-w))

def readerMellinRemainder (s chi amp J K w : ℂ) (b : ℝ) : ℂ→ℂ :=
  firstEndpointMellinRemainder (readerMellinCore s chi amp J K w b) b

/-- The subtracted original pairing is holomorphic at the diagonal exponent
`-1`, as well as everywhere in its one-power-larger convergence region.
The frequency neighborhood and integrable domination come from the source. -/
theorem readerMellinRemainder_differentiableAt_below (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      ∀ a : ℂ, -2<a.re → (2*(a+1)-w).im≠0 →
      DifferentiableAt ℂ (readerMellinRemainder s chi amp J K w b) a := by
  obtain ⟨B,hB,hBhalf,hdata⟩ := readerResponseCore_common_data s chi amp J K w hw hwr hs
  refine ⟨B,hB,hBhalf,?_⟩
  intro b hb hbB a ha hv
  have hbhalf : b≤1/2 := hbB.trans hBhalf
  have hb1 : b<1 := lt_of_le_of_lt hbhalf (by norm_num)
  obtain ⟨R,C,hR,hC,hcore⟩ := hdata b hb hbB (2*(a+1)-w) hv
  let beta := (a.re-2)/2
  have hbeta : -2<beta := by dsimp [beta]; linarith
  have hmap : ContinuousAt (fun u : ℂ => 2*(u+1)-w) a := by fun_prop
  have hnear : ∀ᶠ u : ℂ in 𝓝 a, 2*(u+1)-w∈ball (2*(a+1)-w) R :=
    hmap.eventually (ball_mem_nhds _ hR)
  have him : ∀ᶠ u : ℂ in 𝓝 a, (2*(u+1)-w).im≠0 :=
    (Complex.continuous_im.continuousAt.comp hmap).eventually_ne hv
  have hre : ∀ᶠ u : ℂ in 𝓝 a, beta<u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (by dsimp [beta]; linarith)
  obtain ⟨r,hr,hall⟩ := Metric.eventually_nhds_iff.mp (hnear.and (him.and hre))
  apply firstEndpointMellinRemainder_differentiableAt hb.le hb1.le hr hC hbeta
  · intro u hu
    exact (hall (mem_ball.mp hu)).2.2.le
  · intro u hu
    have hc := (hcore (2*(u+1)-w) (hall (mem_ball.mp hu)).1).1
    have hm := hc.measurable_piecewise
      (show ContinuousOn (fun _ : ℝ => (0:ℂ)) (Icc (0:ℝ) b)ᶜ from continuousOn_const) measurableSet_Icc
    convert hm using 1
    ext z
    by_cases hz : z∈Icc (0:ℝ) b
    · simp [readerMellinCore,hz]
    · simp [readerMellinCore,hz]
  · intro z hz u hu
    have hd := (readerResponseCore_frequency_differentiableAt s chi amp J K w b
      (2*(u+1)-w) (hall (mem_ball.mp hu)).2.1 hz hb1).comp u
      (show DifferentiableAt ℂ (fun v : ℂ => 2*(v+1)-w) u by fun_prop)
    simpa only [readerMellinCore,Set.indicator_of_mem hz,Function.comp_def] using! hd
  · intro u hu z hz
    simp only [readerMellinCore,Set.indicator_of_mem (show z∈Icc (0:ℝ) b from ⟨hz.1.le,hz.2⟩),
      Set.indicator_of_mem (show (0:ℝ)∈Icc 0 b from ⟨le_rfl,hb.le⟩),readerResponseCore_zero]
    exact (hcore (2*(u+1)-w) (hall (mem_ball.mp hu)).1).2.1 z ⟨hz.1.le,hz.2⟩

/-- Incoming part of the original two-frequency horizon pairing. -/
def readerIncomingPart (s chi amp J K w : ℂ) (b : ℝ) (v : ℂ) : ℂ :=
  (incomingResponseEndpoint s chi amp J K w b/2)*power ((w+v)/2) b/((w+v)/2)+
    readerMellinRemainder s chi amp J K w b ((w+v)/2-1)

/-- The opposite branch with precisely its simple diagonal pole removed. -/
def readerOppositeRegularPart (s chi amp J K w : ℂ) (b : ℝ) (v : ℂ) : ℂ :=
  (incomingResponseEndpoint s chi amp J K w b/2)*
      dslope (fun a : ℂ => power a b) 0 ((w-v)/2)+
    readerMellinRemainder s chi amp J K w b ((w-v)/2-1)

/-- Both original horizon coefficients, with the fixed-source diagonal pole removed. -/
def readerHorizonRegularPart (s chi amp J K w : ℂ) (b : ℝ) (v : ℂ) : ℂ :=
  horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)*
      readerIncomingPart s chi amp J K w b v+
    (connection v chi/(2*v))*readerOppositeRegularPart s chi amp J K w b v

/-- The actual source-derived horizon regularization is continuous across its
reader/source diagonal. This discharges the limit step; identification with
the original cutoff finite part is a separate theorem. -/
theorem readerHorizonRegularPart_continuousAt_below (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : 0<w.re) (hs : w-2*s≠0) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      ContinuousAt (readerHorizonRegularPart s chi amp J K w b) w := by
  obtain ⟨B,hB,hBhalf,hM⟩ := readerMellinRemainder_differentiableAt_below s chi amp J K w hw
    (by linarith) hs
  refine ⟨B,hB,hBhalf,?_⟩
  intro b hb hbB
  have hb0 : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hw0 : w≠0 := by intro he; exact hw (by simp [he])
  have hI := hM b hb hbB ((w+w)/2-1)
    (by rw [show (w+w)/2-1=w-1 by ring]; simp only [Complex.sub_re,Complex.one_re]; linarith)
    (by rw [show 2*((w+w)/2-1+1)-w=w by ring]; exact hw)
  have hO := hM b hb hbB ((w-w)/2-1)
    (by norm_num)
    (by rw [show 2*((w-w)/2-1+1)-w= -w by ring]; simpa only [Complex.neg_im,neg_ne_zero] using hw)
  have hiR : ContinuousAt (fun v : ℂ => readerMellinRemainder s chi amp J K w b ((w+v)/2-1)) w := by
    simpa only [Function.comp_def] using! (hI.comp w
      (show DifferentiableAt ℂ (fun v : ℂ => (w+v)/2-1) w by fun_prop)).continuousAt
  have hoR : ContinuousAt (fun v : ℂ => readerMellinRemainder s chi amp J K w b ((w-v)/2-1)) w := by
    simpa only [Function.comp_def] using! (hO.comp w
      (show DifferentiableAt ℂ (fun v : ℂ => (w-v)/2-1) w by fun_prop)).continuousAt
  have hp : ContinuousAt (fun v : ℂ => power ((w+v)/2) b) w :=
    ((show DifferentiableAt ℂ (fun v : ℂ => (w+v)/2) w by fun_prop).const_cpow (Or.inl hb0)).continuousAt
  have hden : (w+w)/2≠0 := by rw [show (w+w)/2=w by ring]; exact hw0
  have hi : ContinuousAt (readerIncomingPart s chi amp J K w b) w :=
    ((hp.const_mul (incomingResponseEndpoint s chi amp J K w b/2)).div
      (by fun_prop) hden).add hiR
  have hd0 : ContinuousAt (dslope (fun a : ℂ => power a b) 0) 0 :=
    continuousAt_dslope_same.mpr (differentiableAt_id.const_cpow (Or.inl hb0))
  have hdc : ContinuousAt (dslope (fun a : ℂ => power a b) 0) ((w-w)/2) := by simpa using hd0
  have hd : ContinuousAt (fun v : ℂ => dslope (fun a : ℂ => power a b) 0 ((w-v)/2)) w :=
    hdc.comp (f:=fun v : ℂ => (w-v)/2) (x:=w)
      (show ContinuousAt (fun v : ℂ => (w-v)/2) w by fun_prop)
  have ho : ContinuousAt (readerOppositeRegularPart s chi amp J K w b) w :=
    (hd.const_mul (incomingResponseEndpoint s chi amp J K w b/2)).add hoR
  have hA : ContinuousAt (fun v => horizonRegularCoefficient v chi
      (normalizable v chi) (normalizableFirst v chi)) w := by
    have hz : (1/2:ℝ)∈Ioo (0:ℝ) 1 := by constructor <;> norm_num
    have hm : (-w).im≠0 := by simpa only [Complex.neg_im,neg_ne_zero] using hw
    have hH := ((horizon_frequency_analyticAt (-w) chi hm hz).comp analyticAt_id.neg).continuousAt
    have hD := ((horizonFirst_frequency_analyticAt (-w) chi hm hz).comp analyticAt_id.neg).continuousAt
    have hN := (normalizable_frequency_entire chi hz w).continuousAt
    have hN1 := (normalizableFirst_frequency_entire chi hz w).continuousAt
    simpa only [horizonRegularCoefficient,radialBracket,Function.comp_def] using!
      (((hN.mul hD).sub (hN1.mul hH)).const_mul (integratingFactor (1/2))).div
        (show ContinuousAt (fun v : ℂ => -v) w by fun_prop) (neg_ne_zero.mpr hw0)
  have hBeta := (connection_frequency_analyticAt w chi hw).continuousAt.div
    (show ContinuousAt (fun v : ℂ => 2*v) w by fun_prop) (mul_ne_zero (by norm_num) hw0)
  exact (hA.mul hi).add (hBeta.mul ho)

private theorem readerOppositeRegularPart_eq_logarithmic (s chi amp J K w : ℂ)
    {b : ℝ} (hb : 0<b) :
    readerOppositeRegularPart s chi amp J K w b w=
      LogarithmicEndpoint.finitePart
        (fun _ : ℂ => readerResponseCore s chi amp J K w b (-w))
        (fun _ => incomingResponseEndpoint s chi amp J K w b/2) b 0 := by
  have hb0 : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hd : deriv (fun a : ℂ => power a b) 0=(Real.log b:ℂ) := by
    have h := (Complex.hasStrictDerivAt_const_cpow (x:=(b:ℂ)) (y:=0) (Or.inl hb0)).hasDerivAt.deriv
    simpa only [power,Complex.cpow_zero,one_mul,← Complex.ofReal_log hb.le] using h
  rw [readerOppositeRegularPart,sub_self,zero_div,zero_sub,dslope_same,hd,
    readerMellinRemainder,firstEndpointMellinRemainder,LogarithmicEndpoint.finitePart,LogarithmicEndpoint.remainder]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  simp only [readerMellinCore,
    Set.indicator_of_mem (show z∈Icc (0:ℝ) b from ⟨hz.1.le,hz.2⟩),
    Set.indicator_of_mem (show (0:ℝ)∈Icc 0 b from ⟨le_rfl,hb.le⟩),
    readerResponseCore_zero,show 2*((-1:ℂ)+1)-w= -w by ring,Complex.cpow_neg_one]
  ring

/-- The removed diagonal pole leaves exactly the original opposite-mode finite
part, including its prescribed logarithmic counterterm and finite constant. -/
theorem readerOppositeRegularPart_original_below (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) (hconn : connection w chi≠0) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      (connection w chi/(2*w))*readerOppositeRegularPart s chi amp J K w b w=
        oppositePairingFinitePart s chi amp J K b w := by
  obtain ⟨BS,hBS,hBShalf,hS⟩ := readerResponseCore_common_data s chi amp J K w hw hwr hs
  obtain ⟨RO,BO,hRO,hBO,hBOhalf,hO⟩ := oppositePairingFinitePart_horizon_restoration_below s chi amp J K w hw hwr hs
  refine ⟨min BS BO,lt_min hBS hBO,(min_le_left _ _).trans hBShalf,?_⟩
  intro b hb hbB
  have hbS : b≤BS := hbB.trans (min_le_left _ _)
  have hbO : b≤BO := hbB.trans (min_le_right _ _)
  obtain ⟨R,C,hR,_,hcore⟩ := hS b hb hbS (-w) (by simpa only [Complex.neg_im,neg_ne_zero] using hw)
  obtain ⟨hc,hbound,he⟩ := hcore (-w) (mem_ball_self hR)
  have hlog := LogarithmicEndpoint.cutoff_tendsto
    (F:=fun _ : ℂ => readerResponseCore s chi amp J K w b (-w))
    (a₀:=fun _ => incomingResponseEndpoint s chi amp J K w b/2) (w:=0)
    hb (hc.mono Ioc_subset_Icc_self) (fun z hz => hbound z ⟨hz.1.le,hz.2⟩)
  rw [← readerOppositeRegularPart_eq_logarithmic s chi amp J K w hb] at hlog
  have hlim := hlog.const_mul (connection w chi/(2*w))
  have hold := (hO b hb hbO).2.2.2 w (mem_ball_self hRO) hconn
  apply tendsto_nhds_unique ?_ hold
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hb] with e heps
  have hreplace : (∫ z in e..b,continuedResponse s chi amp J K z w*horizon (-w) chi z/
      (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))=
    ∫ z in e..b,readerResponseCore s chi amp J K w b (-w) z/(z:ℂ) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le heps.2.le] at hz
    dsimp only
    rw [he hconn z ⟨heps.1.trans_le hz.1,hz.2⟩,
      show (w+-w)/2-1=(-1:ℂ) by ring]
    simp only [power,Complex.cpow_neg_one]
    ring
  rw [intervalIntegral.integral_const_mul,hreplace]
  ring

end
end RHTower.D4BMOriginalSourceResolvent
