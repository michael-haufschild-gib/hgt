import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalRadialBracket
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceContinuedForcedODE
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedOuterPairing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Two-frequency source identity for the actual original radial response. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false

def mixedBracket (s chi amp J K w v : ℂ) (z : ℝ) : ℂ :=
  radialBracket (fun t => continuedResponse s chi amp J K t w)
    (fun t => continuedResponseFirst s chi amp J K t w)
    (normalizable v chi) (normalizableFirst v chi) z

def mixedDensity (s chi amp J K w v : ℂ) (z : ℝ) : ℂ :=
  continuedResponse s chi amp J K z w*normalizable v chi z/
    (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))

def sourceDensity (s chi amp J K w v : ℂ) (z : ℝ) : ℂ :=
  normalizable v chi z*continuedSourceProfile s amp J K w z

/-- The frequency difference is taken in the unchanged left reader. The
actual forced response and all of its source data stay fixed. -/
theorem mixedBracket_hasDerivAt (s chi amp J K w v : ℂ)
    (hwi : w.im≠0) (hwr : -2<w.re) (hc : connection w chi≠0)
    {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    HasDerivAt (mixedBracket s chi amp J K w v)
      (((v^(2 : ℕ)-w^(2 : ℕ))*mixedDensity s chi amp J K w v z-
        sourceDensity s chi amp J K w v z)/2) z := by
  obtain ⟨hU,hD⟩ := continuedResponse_hasDerivAt s chi amp J K w hwi hwr hz
  obtain ⟨hN,hE⟩ := normalizable_derivatives_continued (w:=v) (chi:=chi) hz
  have h := radialBracket_hasDerivAt w chi
    (U:=fun t => continuedResponse s chi amp J K t w)
    (D:=fun t => continuedResponseFirst s chi amp J K t w)
    (DD:=fun t => continuedResponseSecond s chi amp J K t w)
    (V:=normalizable v chi) (E:=normalizableFirst v chi) (EE:=normalizableSecond v chi)
    hz (by convert! hU using 1) (by convert! hD using 1)
      (by convert! hN using 1) (by convert! hE using 1)
  have hS := continuedResponse_original_equation s chi amp J K w hwi hwr hc hz
  obtain ⟨hd,hdd⟩ := continuedResponse_deriv_eq s chi amp J K w hwi hwr hz
  rw [hd,hdd] at hS
  have hNv := normalizable_equation_continued (w:=v) (chi:=chi) hz
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have ht0 : (Real.sqrt (1-z):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)).ne'
  have hsq : (Real.sqrt (1-z):ℂ)^(2 : ℕ)=1-(z:ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hz.2.le)
  have hNw : D4BMPhysicalMaster.radialJet (Complex.I*w) chi z
      (normalizable v chi z) (normalizableFirst v chi z) (normalizableSecond v chi z)=
      (v^(2 : ℕ)-w^(2 : ℕ))/(4*(z:ℂ))*normalizable v chi z := by
    dsimp only [D4BMPhysicalMaster.radialJet] at hNv ⊢
    simp only [mul_pow,Complex.I_sq] at hNv ⊢
    linear_combination hNv
  apply h.congr_deriv
  rw [hNw,hS]
  unfold radialPairingWeight mixedDensity sourceDensity
  rw [power_half_eq_sqrt (sub_nonneg.mpr hz.2.le)]
  rw [← hsq]
  field_simp [hz0,ht0]
  ring

private theorem mixedDensity_continuousOn (s chi amp J K w v : ℂ)
    (hwi : w.im≠0) (hwr : -2<w.re) :
    ContinuousOn (mixedDensity s chi amp J K w v) (Ioo (0:ℝ) 1) := by
  intro z hz
  have hU := (continuedResponse_hasDerivAt s chi amp J K w hwi hwr hz).1.continuousAt
  have hN := (normalizable_derivatives_continued (w:=v) (chi:=chi) hz).1.continuousAt
  have hden : ContinuousAt (fun z : ℝ => 2*(z:ℂ)*(Real.sqrt (1-z):ℂ)) z := by fun_prop
  exact ((hU.mul hN).div hden
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hz.1.ne'))
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)).ne'))).continuousWithinAt

private theorem sourceDensity_continuousOn (s chi amp J K w v : ℂ) :
    ContinuousOn (sourceDensity s chi amp J K w v) (Ioo (0:ℝ) 1) := by
  intro z hz
  exact ((normalizable_derivatives_continued (w:=v) (chi:=chi) hz).1.continuousAt.mul
    (continuedSourceProfile_continuousAt s amp J K w hz.1)).continuousWithinAt

/-- Exact compact resolvent identity. Both integrals are separately admitted
from their actual profiles; no source or boundary matching is assumed. -/
theorem mixed_source_integral (s chi amp J K w v : ℂ)
    (hwi : w.im≠0) (hwr : -2<w.re) (hc : connection w chi≠0)
    {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    IntervalIntegrable (mixedDensity s chi amp J K w v) volume e b ∧
    IntervalIntegrable (sourceDensity s chi amp J K w v) volume e b ∧
    (v^(2 : ℕ)-w^(2 : ℕ))*(∫ z in e..b,mixedDensity s chi amp J K w v z)=
      2*(mixedBracket s chi amp J K w v b-mixedBracket s chi amp J K w v e)+
        ∫ z in e..b,sourceDensity s chi amp J K w v z := by
  have hsub : uIcc e b⊆Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le heb]
    exact fun _ hz => ⟨he.trans_le hz.1,hz.2.trans_lt hb⟩
  have hI : IntervalIntegrable (mixedDensity s chi amp J K w v) volume e b :=
    ((mixedDensity_continuousOn s chi amp J K w v hwi hwr).mono hsub).intervalIntegrable
  have hS : IntervalIntegrable (sourceDensity s chi amp J K w v) volume e b :=
    ((sourceDensity_continuousOn s chi amp J K w v).mono hsub).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z hz => mixedBracket_hasDerivAt s chi amp J K w v hwi hwr hc (hsub hz))
    (((hI.const_mul (v^(2 : ℕ)-w^(2 : ℕ))).sub hS).div_const 2)
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub (hI.const_mul _) hS,
    intervalIntegral.integral_const_mul] at h
  refine ⟨hI,hS,?_⟩
  linear_combination 2*h

def mixedIntegral (s chi amp J K w v : ℂ) (e b : ℝ) : ℂ :=
  ∫ z in e..b,mixedDensity s chi amp J K w v z

def sourceIntegral (s chi amp J K w v : ℂ) (e b : ℝ) : ℂ :=
  ∫ z in e..b,sourceDensity s chi amp J K w v z

private theorem mixedIntegral_continuousAt (s chi amp J K w v : ℂ)
    (hwi : w.im≠0) (hwr : -2<w.re)
    {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    ContinuousAt (fun u => mixedIntegral s chi amp J K w u e b) v := by
  let base := fun z : ℝ => continuedResponse s chi amp J K z w/
    (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))
  have hbase : ContinuousOn base (uIcc e b) := by
    intro z hz
    rw [uIcc_of_le heb] at hz
    have hzI : z∈Ioo (0:ℝ) 1 := ⟨he.trans_le hz.1,hz.2.trans_lt hb⟩
    exact ((continuedResponse_hasDerivAt s chi amp J K w hwi hwr hzI).1.continuousAt.div
      (show ContinuousAt (fun z : ℝ => 2*(z:ℂ)*(Real.sqrt (1-z):ℂ)) z by fun_prop)
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hzI.1.ne'))
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hzI.2)).ne'))).continuousWithinAt
  obtain ⟨C,hC,hbound⟩ := normalizable_outer_uniform_bound v chi he (heb.trans_lt hb)
  have hmajor : IntegrableOn (fun z => ‖base z‖*C) (Ioc e b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le heb).mp (hbase.norm.intervalIntegrable.mul_const C)
  have hfactor (u : ℂ) (z : ℝ) : mixedDensity s chi amp J K w u z=base z*normalizable u chi z := by
    dsimp [mixedDensity,base]
    ring
  have ht : Tendsto (fun u : ℂ => ∫ z in Ioc e b,mixedDensity s chi amp J K w u z)
      (𝓝 v) (𝓝 (∫ z in Ioc e b,mixedDensity s chi amp J K w v z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖base z‖*C)
    · exact Eventually.of_forall (fun u =>
        ((mixedDensity_continuousOn s chi amp J K w u hwi hwr).mono
          (fun _ hz => ⟨he.trans hz.1,hz.2.trans_lt hb⟩)).aestronglyMeasurable measurableSet_Ioc)
    · filter_upwards [Metric.ball_mem_nhds v (by norm_num : (0:ℝ)<1)] with u hu
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      rw [hfactor,norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound u hu z ⟨hz.1.le,hz.2.trans hb.le⟩) (norm_nonneg _)
    · exact hmajor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      have hzI : z∈Ioo (0:ℝ) 1 := ⟨he.trans hz.1,hz.2.trans_lt hb⟩
      have hN := ((normalizable_frequency_entire chi hzI) v).continuousAt
      simpa only [hfactor] using! hN.tendsto.const_mul (base z)
  simpa only [ContinuousAt,mixedIntegral,intervalIntegral.integral_of_le heb] using! ht

private theorem mixedBracket_reader_hasDerivAt (s chi amp J K w v : ℂ)
    {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u => mixedBracket s chi amp J K w u z)
      (integratingFactor z*(continuedResponse s chi amp J K z w*
        deriv (fun u => normalizableFirst u chi z) v-
        continuedResponseFirst s chi amp J K z w*deriv (fun u => normalizable u chi z) v)) v := by
  exact (((normalizableFirst_frequency_entire chi hz).differentiableAt.hasDerivAt.const_mul
    (continuedResponse s chi amp J K z w)).sub
      ((normalizable_frequency_entire chi hz).differentiableAt.hasDerivAt.const_mul
        (continuedResponseFirst s chi amp J K z w))).const_mul (integratingFactor z)

/-- Diagonal source reduction without differentiating the evolved response.
The derivative varies only the original reader frequency, keeping the
angular parameter, source frequency, onset and source profile fixed. -/
theorem diagonal_source_identity (s chi amp J K w : ℂ)
    (hwi : w.im≠0) (hwr : -2<w.re) (hc : connection w chi≠0)
    {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    DifferentiableAt ℂ (fun v => sourceIntegral s chi amp J K w v e b) w ∧
    2*w*mixedIntegral s chi amp J K w w e b=
      2*(deriv (fun v => mixedBracket s chi amp J K w v b) w-
        deriv (fun v => mixedBracket s chi amp J K w v e) w)+
        deriv (fun v => sourceIntegral s chi amp J K w v e b) w := by
  let I := fun v => mixedIntegral s chi amp J K w v e b
  let B := fun v => 2*(mixedBracket s chi amp J K w v b-mixedBracket s chi amp J K w v e)
  let D := fun v => B v+sourceIntegral s chi amp J K w v e b
  have hEq (v : ℂ) : D v=(v^(2 : ℕ)-w^(2 : ℕ))*I v :=
    (mixed_source_integral s chi amp J K w v hwi hwr hc he heb hb).2.2.symm
  have hD0 : D w=0 := by rw [hEq];ring
  have hcont := mixedIntegral_continuousAt s chi amp J K w w hwi hwr he heb hb
  have hlim := ((continuousAt_id.add_const w).tendsto.mul hcont.tendsto).mono_left (show 𝓝[≠] w ≤ 𝓝 w from nhdsWithin_le_nhds)
  have hD : HasDerivAt D (2*w*I w) w := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have hv : (w+w)*mixedIntegral s chi amp J K w w e b=2*w*I w := by dsimp only [I];ring
    dsimp only [id_eq] at hlim
    rw [hv] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with v hvw
    rw [slope_def_field,hD0,hEq,sub_zero]
    field_simp [sub_ne_zero.mpr hvw]
    ring
  have hB := ((mixedBracket_reader_hasDerivAt s chi amp J K w w
    (show b∈Ioo (0:ℝ) 1 from ⟨he.trans_le heb,hb⟩)).sub
      (mixedBracket_reader_hasDerivAt s chi amp J K w w
        (show e∈Ioo (0:ℝ) 1 from ⟨he,heb.trans_lt hb⟩))).const_mul (2:ℂ)
  have hB' : HasDerivAt B (2*(deriv (fun v => mixedBracket s chi amp J K w v b) w-
      deriv (fun v => mixedBracket s chi amp J K w v e) w)) w := by
    simpa only [(mixedBracket_reader_hasDerivAt s chi amp J K w w
      (show b∈Ioo (0:ℝ) 1 from ⟨he.trans_le heb,hb⟩)).deriv,
      (mixedBracket_reader_hasDerivAt s chi amp J K w w
        (show e∈Ioo (0:ℝ) 1 from ⟨he,heb.trans_lt hb⟩)).deriv] using! hB
  have hS := hD.sub hB'
  have hfun : D-B=(fun v => sourceIntegral s chi amp J K w v e b) := by
    funext v
    change D v-B v=_
    dsimp only [D]
    ring
  rw [hfun] at hS
  refine ⟨hS.differentiableAt,?_⟩
  rw [hS.deriv]
  dsimp only [I]
  ring

end
end RHTower.D4BMOriginalSourceResolvent
