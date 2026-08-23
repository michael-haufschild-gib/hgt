import GaloisForLFunctions.HTGeometry.CompactUniformDilation
import GaloisForLFunctions.RHTower.WoldDepthXiEssentialAmplification
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compact-uniform Wold-depth--Xi essential amplification

The literal Xi depth-successor reporter converges in the sup norm on every compact divisor-free
set. Its Wold-shell realization has exact essential action log 2 / 2, and no finite Rees power
absorbs any realizing operator family.
-/

open Complex Filter Set Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

theorem tendstoUniformlyOn_xiDepthMomentReporter
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0) :
    TendstoUniformlyOn
      (fun M : ℕ => fun u : ℂ => xiDepthMomentReporter u M)
      (fun u : ℂ => -u * logDeriv xi u) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  let ε : ℕ → ℂ := fun M => (((M + 1 : ℕ) : ℂ)⁻¹)
  have hεne : Tendsto ε atTop (𝓝[≠] 0) := by
    exact GaloisForLFunctions.tendsto_natCast_inv_complex_nhdsNE.comp
      (tendsto_add_atTop_nat 1)
  have hε : Tendsto ε atTop (𝓝 0) := hεne.mono_right inf_le_left
  have hxiC1 : ContDiff ℂ 1 xi :=
    xi_analyticOnNhd_univ.contDiff
  have hxiCont : Continuous xi := hxiC1.continuous
  let qseq : ℕ → ℂ → ℂ := fun M u =>
    (ε M)⁻¹ * (xi ((1 + ε M) * u) - xi u)
  let dseq : ℕ → ℂ → ℂ := fun M u => xi ((1 + ε M) * u)
  let q : ℂ → ℂ := fun u => u * deriv xi u
  have hq : TendstoUniformlyOn qseq q atTop K := by
    exact (tendstoUniformlyOn_dilation_differenceQuotient hxiC1 hK).comp_tendsto_index hεne
  have hd : TendstoUniformlyOn dseq xi atTop K := by
    exact (tendstoUniformlyOn_dilation hxiCont hK).comp_tendsto_index hε
  have hqcont : ContinuousOn q K := by
    have hdxi : Continuous (deriv xi) := hxiC1.continuous_deriv (by norm_num)
    exact (continuous_id.mul hdxi).continuousOn
  have hratio : TendstoUniformlyOn
      (fun M u => qseq M u / dseq M u)
      (fun u => q u / xi u) atTop K :=
    TendstoUniformlyOn.div_of_isCompact_of_ne_zero hK hq hd hqcont
      hxiCont.continuousOn hxi
  obtain ⟨u₀, hu₀K, hu₀min⟩ :=
    hK.exists_isMinOn hKne hxiCont.norm.continuousOn
  have hcpos : 0 < ‖xi u₀‖ := norm_pos_iff.mpr (hxi u₀ hu₀K)
  rw [Metric.tendstoUniformlyOn_iff] at hd hratio ⊢
  have hden : ∀ᶠ M : ℕ in atTop, ∀ u ∈ K, dseq M u ≠ 0 := by
    filter_upwards [hd (‖xi u₀‖ / 2) (half_pos hcpos)] with M hM
    intro u hu hzero
    have herr := hM u hu
    rw [hzero, dist_zero_right] at herr
    have hlo : ‖xi u₀‖ ≤ ‖xi u‖ := hu₀min hu
    linarith
  intro η hη
  filter_upwards [hratio η hη, hden] with M hM hMden
  intro u hu
  have hdist := hM u hu
  have hactual :
      xiDepthMomentReporter u M = -(qseq M u / dseq M u) := by
    have hnat : (((M + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show M + 1 ≠ 0 by omega)
    have heps : ε M ≠ 0 := inv_ne_zero hnat
    have hdu : dseq M u ≠ 0 := hMden u hu
    have hdil : xi ((1 + ε M) * u) ≠ 0 := by
      simpa [dseq] using hdu
    have hdil' :
        xi ((1 + ((((M + 1 : ℕ) : ℂ))⁻¹)) * u) ≠ 0 := by
      simpa [ε] using hdil
    have hdil'' :
        xi (((((M + 1 : ℕ) : ℂ)) * u) *
            ((((M + 1 : ℕ) : ℂ))⁻¹) +
          u * ((((M + 1 : ℕ) : ℂ))⁻¹)) ≠ 0 := by
      convert hdil' using 1
      field_simp [hnat]
    have hdil''' :
        xi (((((1 + M : ℕ) : ℂ)) * u) *
            ((((1 + M : ℕ) : ℂ))⁻¹) +
          u * ((((1 + M : ℕ) : ℂ))⁻¹)) ≠ 0 := by
      simpa [Nat.add_comm] using hdil''
    have hdilnorm :
        xi (((((M + 1 : ℕ) : ℂ)) + 1) * u /
          (((M + 1 : ℕ) : ℂ))) ≠ 0 := by
      convert hdil' using 1
      field_simp [hnat]
    have hzero : depthSuccessorTransport xi 0 u = 1 := by
      simp [depthSuccessorTransport, hxi u hu]
    dsimp [qseq, dseq]
    rw [xiDepthMomentReporter, xiDepthSuccessorTransport,
      depthSuccessorTransport]
    rw [hzero]
    have hinv : (ε M)⁻¹ = (((M + 1 : ℕ) : ℂ)) := by
      simp [ε]
    rw [hinv]
    dsimp [ε]
    field_simp [hdil', hdil'', hdil''', hdilnorm]
    ring
  have htarget : q u / xi u = u * logDeriv xi u := by
    simp [q, logDeriv, mul_div_assoc]
  rw [htarget] at hdist
  rw [hactual]
  simpa only [neg_mul, dist_neg_neg] using hdist

/-- On a compact set avoiding the Xi divisor, actual moment reporters are continuous for all
sufficiently large depths. -/
theorem eventually_continuousOn_xiDepthMomentReporter
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0) :
    ∀ᶠ M : ℕ in atTop,
      ContinuousOn (fun u : ℂ => xiDepthMomentReporter u M) K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact Eventually.of_forall fun _ => continuousOn_empty _
  let ε : ℕ → ℂ := fun M => (((M + 1 : ℕ) : ℂ)⁻¹)
  have hε : Tendsto ε atTop (𝓝 0) :=
    (GaloisForLFunctions.tendsto_natCast_inv_complex_nhdsNE.comp
      (tendsto_add_atTop_nat 1)).mono_right inf_le_left
  have hxiC1 : ContDiff ℂ 1 xi := xi_analyticOnNhd_univ.contDiff
  have hxiCont : Continuous xi := hxiC1.continuous
  have hd : TendstoUniformlyOn
      (fun M u => xi ((1 + ε M) * u)) xi atTop K :=
    (tendstoUniformlyOn_dilation hxiCont hK).comp_tendsto_index hε
  obtain ⟨u₀, hu₀K, hu₀min⟩ :=
    hK.exists_isMinOn hKne hxiCont.norm.continuousOn
  have hcpos : 0 < ‖xi u₀‖ := norm_pos_iff.mpr (hxi u₀ hu₀K)
  rw [Metric.tendstoUniformlyOn_iff] at hd
  have hden : ∀ᶠ M : ℕ in atTop,
      ∀ u ∈ K, xi ((1 + ε M) * u) ≠ 0 := by
    filter_upwards [hd (‖xi u₀‖ / 2) (half_pos hcpos)] with M hM
    intro u hu hzero
    have herr := hM u hu
    rw [hzero, dist_zero_right] at herr
    have hlo : ‖xi u₀‖ ≤ ‖xi u‖ := hu₀min hu
    linarith
  filter_upwards [hden] with M hMden
  have hdilCont : Continuous (fun u : ℂ => xi ((1 + ε M) * u)) :=
    hxiCont.comp (continuous_const.mul continuous_id)
  have htransport : ContinuousOn
      (fun u : ℂ => xiDepthSuccessorTransport (ε M) u) K := by
    change ContinuousOn (xi / fun u : ℂ => xi ((1 + ε M) * u)) K
    exact hxiCont.continuousOn.div hdilCont.continuousOn hMden
  have htransportZero : ContinuousOn
      (fun u : ℂ => xiDepthSuccessorTransport 0 u) K := by
    change ContinuousOn (xi / fun u : ℂ => xi ((1 + 0) * u)) K
    exact hxiCont.continuousOn.div
      (hxiCont.comp (continuous_const.mul continuous_id)).continuousOn
      (by simpa using hxi)
  have hmul :=
    (continuousOn_const : ContinuousOn
      (fun _ : ℂ => (((M + 1 : ℕ) : ℂ))) K).mul
        (htransport.sub htransportZero)
  change ContinuousOn
    (fun u : ℂ => (((M + 1 : ℕ) : ℂ)) *
      (xiDepthSuccessorTransport (ε M) u -
        xiDepthSuccessorTransport 0 u)) K at hmul
  simpa [xiDepthMomentReporter, ε] using hmul

/-- The actual Xi reporter restricted to `K`; the irrelevant finite discontinuous prefix is
canonically patched by zero. -/
def xiDepthMomentReporterOn (K : Set ℂ) (hK : IsCompact K) (M : ℕ) :
    BoundedContinuousFunction K ℂ := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : C(K, ℂ) :=
    if h : ContinuousOn (fun u : ℂ => xiDepthMomentReporter u M) K then
      ⟨fun u : K => xiDepthMomentReporter u M,
        continuousOn_iff_continuous_restrict.mp h⟩
    else 0
  exact BoundedContinuousFunction.mkOfCompact F

@[simp] theorem xiDepthMomentReporterOn_apply_of_continuousOn
    {K : Set ℂ} {M : ℕ}
    (hK : IsCompact K)
    (h : ContinuousOn (fun u : ℂ => xiDepthMomentReporter u M) K)
    (u : K) :
    xiDepthMomentReporterOn K hK M u = xiDepthMomentReporter u M := by
  simp [xiDepthMomentReporterOn, h]

/-- Xi logarithmic connection as an element of `C(K)`. -/
def xiLogConnectionOn (K : Set ℂ) (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0) : BoundedContinuousFunction K ℂ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hxiC1 : ContDiff ℂ 1 xi := xi_analyticOnNhd_univ.contDiff
  have hderiv : Continuous (deriv xi) :=
    hxiC1.continuous_deriv (by norm_num)
  have hcont : ContinuousOn (fun u : ℂ => -u * logDeriv xi u) K := by
    have hprod := continuous_id.continuousOn.mul
      (hderiv.continuousOn.div hxiC1.continuous.continuousOn hxi)
    change ContinuousOn (fun u : ℂ => u * (deriv xi u / xi u)) K at hprod
    have hneg := hprod.neg
    change ContinuousOn (fun u : ℂ => -(u * (deriv xi u / xi u))) K at hneg
    exact hneg.congr fun u _ => by simp [logDeriv]
  let F : C(K, ℂ) :=
    ⟨fun u : K => -u.1 * logDeriv xi u.1,
      continuousOn_iff_continuous_restrict.mp hcont⟩
  exact BoundedContinuousFunction.mkOfCompact F

@[simp] theorem xiLogConnectionOn_apply
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0) (u : K) :
    xiLogConnectionOn K hK hxi u = -(u : ℂ) * logDeriv xi u := rfl

/-- Compact-uniform reporter convergence is norm convergence in `C(K)`. -/
theorem tendsto_xiDepthMomentReporterOn
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0) :
    Tendsto (xiDepthMomentReporterOn K hK) atTop
      (𝓝 (xiLogConnectionOn K hK hxi)) := by
  have hunif := tendstoUniformlyOn_xiDepthMomentReporter hK hxi
  have hcont := eventually_continuousOn_xiDepthMomentReporter hK hxi
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [hunif (η / 2) (half_pos hη), hcont] with M hM hMc
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ (half_lt_self hη)
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro u
  have hu := hM u u.property
  change ‖xiDepthMomentReporterOn K hK M u -
    xiLogConnectionOn K hK hxi u‖ ≤ η / 2
  rw [xiDepthMomentReporterOn_apply_of_continuousOn hK hMc]
  rw [xiLogConnectionOn_apply]
  rw [dist_eq_norm] at hu
  calc
    ‖xiDepthMomentReporter (u : ℂ) M -
        (-(u : ℂ) * logDeriv xi u)‖ =
        ‖(-(u : ℂ) * logDeriv xi u) -
          xiDepthMomentReporter u M‖ := norm_sub_rev _ _
    _ ≤ η / 2 := hu.le

/-- Sup norms of the compact reporter converge to the compact Xi-connection norm. -/
theorem tendsto_norm_xiDepthMomentReporterOn
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0) :
    Tendsto (fun M => ‖xiDepthMomentReporterOn K hK M‖) atTop
      (𝓝 ‖xiLogConnectionOn K hK hxi‖) :=
  continuous_norm.tendsto _ |>.comp
    (tendsto_xiDepthMomentReporterOn hK hxi)

/-- Unrenormalized compact Xi successor packet. -/
def xiDepthSuccessorDefectOn (K : Set ℂ) (hK : IsCompact K) (M : ℕ) :
    BoundedContinuousFunction K ℂ :=
  xiHarmonicDepthWeight M • xiDepthMomentReporterOn K hK M

/-- Beyond the patched finite prefix, the compact packet is the literal Xi depth successor at
every point of `K`. -/
theorem eventually_xiDepthSuccessorDefectOn_apply
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0) :
    ∀ᶠ M : ℕ in atTop, ∀ u : K,
      xiDepthSuccessorDefectOn K hK M u = xiDepthSuccessorDefect u M := by
  filter_upwards [eventually_continuousOn_xiDepthMomentReporter hK hxi]
    with M hM
  intro u
  rw [xiDepthSuccessorDefectOn, xiDepthSuccessorDefect]
  change xiHarmonicDepthWeight M • xiDepthMomentReporterOn K hK M u =
    xiHarmonicDepthWeight M • xiDepthMomentReporter (u : ℂ) M
  rw [xiDepthMomentReporterOn_apply_of_continuousOn hK hM]

/-- Exact source-linked lower bound for a `C(K)`-valued operator realizing the compact Xi
successor packet. -/
theorem norm_ge_xiDepthSuccessorDefectOn_div_woldShell
    {K : Set ℂ} (hK : IsCompact K) {M : ℕ} (hM : 1 ≤ M)
    (T : WoldDepthShellHilbert →L[ℂ] BoundedContinuousFunction K ℂ)
    (hT : T (woldDepthShellVector M) = xiDepthSuccessorDefectOn K hK M) :
    ‖xiDepthSuccessorDefectOn K hK M‖ /
        Real.sqrt (shellSourceMass (M + 1)) ≤ ‖T‖ := by
  have hmass : 0 < shellSourceMass (M + 1) :=
    shellSourceMass_pos (by omega)
  have hsqrt : 0 < Real.sqrt (shellSourceMass (M + 1)) :=
    Real.sqrt_pos.2 hmass
  apply (div_le_iff₀ hsqrt).2
  have hop := T.le_opNorm (woldDepthShellVector M)
  rw [hT, norm_woldDepthShellVector] at hop
  simpa [mul_comm] using hop

/-- Exact least norm forced by one compact Wold-shell/Xi-successor pair. -/
def woldXiDepthCompactMinimalAmplification
    (K : Set ℂ) (hK : IsCompact K) (M : ℕ) : ℝ :=
  ‖xiDepthSuccessorDefectOn K hK M‖ /
    Real.sqrt (shellSourceMass (M + 1))

/-- Source-rescaled compact minimal amplification converges to the `C(K)` norm of the Xi
connection. -/
theorem tendsto_woldXiDepthCompactMinimalAmplification_rescaled
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0) :
    Tendsto
      (fun M : ℕ =>
        ((M + 1 : ℕ) : ℝ) *
          Real.sqrt (shellSourceMass (M + 1)) *
            woldXiDepthCompactMinimalAmplification K hK M)
      atTop (𝓝 ‖xiLogConnectionOn K hK hxi‖) := by
  refine (tendsto_norm_xiDepthMomentReporterOn hK hxi).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hmass : 0 < shellSourceMass (M + 1) :=
    shellSourceMass_pos (by omega)
  have hsqrt : 0 < Real.sqrt (shellSourceMass (M + 1)) :=
    Real.sqrt_pos.2 hmass
  have hdepth : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  rw [woldXiDepthCompactMinimalAmplification,
    xiDepthSuccessorDefectOn, xiHarmonicDepthWeight,
    norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hdepth)]
  field_simp [hsqrt.ne', hdepth.ne']

/-- Exact compact-uniform essential action forced by the literal Wold shell and Xi successor. -/
theorem tendsto_log_woldXiDepthCompactMinimalAmplification_div_depth
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0)
    (hconnection : xiLogConnectionOn K hK hxi ≠ 0) :
    Tendsto
      (fun M : ℕ =>
        Real.log (woldXiDepthCompactMinimalAmplification K hK M) /
          ((M + 1 : ℕ) : ℝ))
      atTop (𝓝 (Real.log 2 / 2)) := by
  let B : ℕ → ℝ := fun M =>
    ((M + 1 : ℕ) : ℝ) *
      Real.sqrt (shellSourceMass (M + 1)) *
        woldXiDepthCompactMinimalAmplification K hK M
  have hLpos : 0 < ‖xiLogConnectionOn K hK hxi‖ :=
    norm_pos_iff.mpr hconnection
  have hB : Tendsto B atTop (𝓝 ‖xiLogConnectionOn K hK hxi‖) := by
    simpa only [B] using
      tendsto_woldXiDepthCompactMinimalAmplification_rescaled hK hxi
  have hlogB :
      Tendsto (fun M : ℕ => Real.log (B M)) atTop
        (𝓝 (Real.log ‖xiLogConnectionOn K hK hxi‖)) :=
    (Real.continuousAt_log hLpos.ne').tendsto.comp hB
  have hdepth :
      Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv :
      Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hdepth
  have hlogBdiv :
      Tendsto
        (fun M : ℕ => Real.log (B M) / ((M + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hlogB.mul hinv
  have hlogdepth :
      Tendsto
        (fun M : ℕ => Real.log (((M + 1 : ℕ) : ℝ)) /
          ((M + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hdepth
  have hsource := tendsto_log_shellSourceMass_div_depth
  have hlimit := (hlogBdiv.sub hlogdepth).sub
    (hsource.const_mul (1 / 2 : ℝ))
  have hBne : ∀ᶠ M : ℕ in atTop, B M ≠ 0 :=
    hB.eventually_ne hLpos.ne'
  have heq :
      (fun M : ℕ =>
        Real.log (B M) / ((M + 1 : ℕ) : ℝ) -
            Real.log (((M + 1 : ℕ) : ℝ)) / ((M + 1 : ℕ) : ℝ) -
          (1 / 2 : ℝ) *
            (Real.log (shellSourceMass (M + 1)) /
              ((M + 1 : ℕ) : ℝ))) =ᶠ[atTop]
        (fun M : ℕ =>
          Real.log (woldXiDepthCompactMinimalAmplification K hK M) /
            ((M + 1 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1, hBne] with M hM hBM
    have hmass : 0 < shellSourceMass (M + 1) :=
      shellSourceMass_pos (by omega)
    have hsqrt : 0 < Real.sqrt (shellSourceMass (M + 1)) :=
      Real.sqrt_pos.2 hmass
    have hdepth_pos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    have hamp : woldXiDepthCompactMinimalAmplification K hK M ≠ 0 := by
      intro hamp
      apply hBM
      simp [B, hamp]
    dsimp only [B]
    rw [Real.log_mul (mul_ne_zero hdepth_pos.ne' hsqrt.ne') hamp,
      Real.log_mul hdepth_pos.ne' hsqrt.ne', Real.log_sqrt hmass.le]
    field_simp [hdepth_pos.ne']
    ring
  have hfinal :
      Tendsto
        (fun M : ℕ =>
          Real.log (woldXiDepthCompactMinimalAmplification K hK M) /
            ((M + 1 : ℕ) : ℝ))
        atTop
          (𝓝 (((0 : ℝ) - 0) - (1 / 2 : ℝ) * (-Real.log 2))) :=
    hlimit.congr' heq
  have hlimEq :
      ((0 : ℝ) - 0) - (1 / 2 : ℝ) * (-Real.log 2) =
        Real.log 2 / 2 := by
    ring
  rw [hlimEq] at hfinal
  exact hfinal

/-- Every `C(K)`-valued realizing operator family eventually dominates every exponential below
the compact-uniform forced action `log 2 / 2`. -/
theorem eventually_exp_depth_le_norm_of_realizes_xiDepthSuccessorOn
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0)
    (hconnection : xiLogConnectionOn K hK hxi ≠ 0)
    (T : ℕ → WoldDepthShellHilbert →L[ℂ] BoundedContinuousFunction K ℂ)
    (hT : ∀ M, T M (woldDepthShellVector M) =
      xiDepthSuccessorDefectOn K hK M)
    {c : ℝ} (hc : c < Real.log 2 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.exp (c * ((M + 1 : ℕ) : ℝ)) ≤ ‖T M‖ := by
  have hrate :=
    tendsto_log_woldXiDepthCompactMinimalAmplification_div_depth
      hK hxi hconnection
  have hrateLower :
      ∀ᶠ M : ℕ in atTop,
        c < Real.log (woldXiDepthCompactMinimalAmplification K hK M) /
          ((M + 1 : ℕ) : ℝ) :=
    (tendsto_order.1 hrate).1 c hc
  have hrescaled :=
    tendsto_woldXiDepthCompactMinimalAmplification_rescaled hK hxi
  have hLpos : 0 < ‖xiLogConnectionOn K hK hxi‖ :=
    norm_pos_iff.mpr hconnection
  have hrescaledPos :
      ∀ᶠ M : ℕ in atTop,
        0 < ((M + 1 : ℕ) : ℝ) *
          Real.sqrt (shellSourceMass (M + 1)) *
            woldXiDepthCompactMinimalAmplification K hK M :=
    (tendsto_order.1 hrescaled).1 0 hLpos
  filter_upwards [eventually_ge_atTop 1, hrateLower, hrescaledPos]
    with M hM hrateM hrescaledM
  have hmass : 0 < shellSourceMass (M + 1) :=
    shellSourceMass_pos (by omega)
  have hsqrt : 0 < Real.sqrt (shellSourceMass (M + 1)) :=
    Real.sqrt_pos.2 hmass
  have hdepth : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hfactor :
      0 < ((M + 1 : ℕ) : ℝ) * Real.sqrt (shellSourceMass (M + 1)) :=
    mul_pos hdepth hsqrt
  have hamp : 0 < woldXiDepthCompactMinimalAmplification K hK M := by
    rcases mul_pos_iff.mp hrescaledM with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hfactor.le hneg.1).elim
  have hlog :
      c * ((M + 1 : ℕ) : ℝ) <
        Real.log (woldXiDepthCompactMinimalAmplification K hK M) :=
    (lt_div_iff₀ hdepth).mp hrateM
  have hexp :
      Real.exp (c * ((M + 1 : ℕ) : ℝ)) ≤
        woldXiDepthCompactMinimalAmplification K hK M := by
    rw [← Real.exp_log hamp]
    exact Real.exp_le_exp.mpr hlog.le
  exact hexp.trans
    (norm_ge_xiDepthSuccessorDefectOn_div_woldShell hK hM (T M) (hT M))

/-- A positive real exponential dominates every fixed power of the shifted natural depth. -/
theorem tendsto_exp_mul_depth_div_depth_pow_atTop
    {c : ℝ} (N : ℕ) (hc : 0 < c) :
    Tendsto
      (fun M : ℕ =>
        Real.exp (c * ((M + 1 : ℕ) : ℝ)) /
          ((M + 1 : ℕ) : ℝ) ^ N)
      atTop atTop := by
  let rho : ℝ := Real.exp c
  have hrho : 1 < rho := by
    exact Real.one_lt_exp_iff.mpr hc
  have hbase := tendsto_pow_const_div_const_pow_of_one_lt N hrho
  have hshift : Tendsto
      (fun M : ℕ => ((M + 1 : ℕ) : ℝ) ^ N / rho ^ (M + 1))
      atTop (𝓝 0) := by
    exact (tendsto_add_atTop_iff_nat 1).2 hbase
  have hpos : ∀ᶠ M : ℕ in atTop,
      0 < ((M + 1 : ℕ) : ℝ) ^ N / rho ^ (M + 1) :=
    Eventually.of_forall fun M => div_pos (pow_pos (by positivity) N)
      (pow_pos (lt_trans zero_lt_one hrho) (M + 1))
  have hright : Tendsto
      (fun M : ℕ => ((M + 1 : ℕ) : ℝ) ^ N / rho ^ (M + 1))
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hshift, hpos⟩
  have hinv := hright.inv_tendsto_nhdsGT_zero
  convert hinv using 1
  funext M
  change Real.exp (c * ((M + 1 : ℕ) : ℝ)) /
      ((M + 1 : ℕ) : ℝ) ^ N =
    (((M + 1 : ℕ) : ℝ) ^ N / rho ^ (M + 1))⁻¹
  rw [inv_div]
  congr 2
  dsimp [rho]
  rw [mul_comm, Real.exp_nat_mul]

/-- Equation `(15)`: no finite Rees power can absorb a compact-uniform realizing family. -/
theorem tendsto_harmonicDepthWeight_pow_mul_norm_atTop_of_realizes_xiDepthSuccessorOn
    {K : Set ℂ} (hK : IsCompact K)
    (hxi : ∀ u ∈ K, xi u ≠ 0)
    (hconnection : xiLogConnectionOn K hK hxi ≠ 0)
    (T : ℕ → WoldDepthShellHilbert →L[ℂ] BoundedContinuousFunction K ℂ)
    (hT : ∀ M, T M (woldDepthShellVector M) =
      xiDepthSuccessorDefectOn K hK M)
    (N : ℕ) :
    Tendsto
      (fun M : ℕ => xiHarmonicDepthWeight M ^ N * ‖T M‖)
      atTop atTop := by
  let c : ℝ := Real.log 2 / 4
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcpos : 0 < c := by dsimp [c]; linarith
  have hcaction : c < Real.log 2 / 2 := by dsimp [c]; linarith
  have hexp := eventually_exp_depth_le_norm_of_realizes_xiDepthSuccessorOn
    hK hxi hconnection T hT hcaction
  have hgrowth := tendsto_exp_mul_depth_div_depth_pow_atTop N hcpos
  refine tendsto_atTop_mono' atTop ?_ hgrowth
  filter_upwards [hexp] with M hM
  have hdepth : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  rw [xiHarmonicDepthWeight, inv_pow]
  simpa [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hM
      (inv_nonneg.mpr (pow_nonneg hdepth.le N))

end RHTower
