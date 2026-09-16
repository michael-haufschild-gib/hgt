import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCanonicalMatchingNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalSourceSurvival
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalMoment
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMClearedOnsetPulseTransform

/-! Genuine original Green-response poles survive at relative density one among simple
critical Xi sources. The unchanged complementary unit-source clock cannot match their
residues or their zero loci. A regular full canonical action can coexist with these poles;
no obstruction for arbitrary metric observables or nonlocal receivers is asserted. -/

open Complex Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore D4BMOriginalCanonicalAction
noncomputable section
set_option autoImplicit false

private theorem onsetCorrection_norm (w : ℂ) : ‖onsetCorrection 0 w‖ ≤ Real.exp ‖w‖ := by
  have hb (t : ℝ) (ht : t∈Ioc (0:ℝ) 1) :
      ‖((Real.smoothTransition t:ℂ)-1)*Complex.exp ((0-w)*(t:ℂ))‖ ≤ Real.exp ‖w‖ := by
    have hc : ‖(Real.smoothTransition t:ℂ)-1‖ ≤ 1 := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (Real.smoothTransition.le_one t))]
      linarith [Real.smoothTransition.nonneg t]
    have he : ‖Complex.exp ((0-w)*(t:ℂ))‖ ≤ Real.exp ‖w‖ := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have h := Complex.re_le_norm ((0-w)*(t:ℂ))
      simp only [zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos ht.1] at h
      simpa only [zero_sub] using h.trans (mul_le_of_le_one_right (norm_nonneg w) ht.2)
    rw [norm_mul]
    exact (mul_le_mul hc he (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  unfold onsetCorrection
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (C:=Real.exp ‖w‖)
    (f:=fun t => ((Real.smoothTransition t:ℂ)-1)*Complex.exp ((0-w)*(t:ℂ)))
    (fun t ht => hb t (by simpa only [uIoc_of_le zero_le_one] using ht))
  simpa only [sub_zero,abs_one,mul_one,one_mul] using h

/-- The unchanged compact onset pulse has a global finite-exponential-type bound. -/
theorem onsetPulseTransform_exponential_bound (z : ℂ) :
    ‖onsetPulseTransform z‖ ≤ 2*Real.exp (2*‖z‖) := by
  rw [onsetPulseTransform_eq_one_sub]
  have h := norm_sub_le (1:ℂ) (z*onsetCorrection 0 (-z))
  rw [norm_one,norm_mul] at h
  have hc : ‖onsetCorrection 0 (-z)‖ ≤ Real.exp ‖z‖ := by
    simpa only [norm_neg] using onsetCorrection_norm (-z)
  have h1 : 1 ≤ Real.exp ‖z‖ := Real.one_le_exp (norm_nonneg z)
  have hz : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
  have hm := mul_le_mul_of_nonneg_left hc (norm_nonneg z)
  have hm' := mul_le_mul_of_nonneg_right hz (Real.exp_pos ‖z‖).le
  rw [show 2*‖z‖=‖z‖+‖z‖ by ring,Real.exp_add]
  nlinarith

def fundamentalOnsetExceptionFinset (N : ℕ) : Finset ℂ := by
  classical
  exact (xiSimpleCriticalZeroFinset ((N:ℝ)/3)).filter
    (fun z => onsetPulseTransform (5*z/2-3)=0)

theorem fundamentalOnsetExceptionFinset_card_linear :
    ∃ K : ℝ, 0<K ∧ ∀ N : ℕ, 2≤N →
      ((fundamentalOnsetExceptionFinset N).card:ℝ) ≤ K*(1+(N:ℝ)) := by
  classical
  have h0 : onsetPulseTransform 0 ≠ 0 := by rw [onsetPulseTransform_zero];norm_num
  obtain ⟨K,hK,hB⟩ := exponentialType_zeroCount_linear differentiable_onsetPulseTransform
    h0 (by norm_num : (0:ℝ)≤2) (by norm_num : (1:ℝ)≤2) onsetPulseTransform_exponential_bound
  refine ⟨4*K,by positivity,?_⟩
  intro N hN
  have hNr : (2:ℝ)≤N := by exact_mod_cast hN
  have hd : ((fundamentalOnsetExceptionFinset N).card:ℤ) ≤
      ∑ᶠ u, (MeromorphicOn.divisor onsetPulseTransform (closedBall 0 (4*(N:ℝ)))) u := by
    apply card_le_sum_divisor_of_finite_zeros differentiable_onsetPulseTransform h0
      (fundamentalOnsetExceptionFinset N) (fun z : ℂ => 5*z/2-3)
    · intro z _ u _ h
      linear_combination (2/5:ℂ)*h
    · intro z hz
      have hh := mem_xiSimpleCriticalZeroFinset.mp (Finset.mem_filter.mp hz).1
      have hn := Complex.norm_le_abs_re_add_abs_im z
      rw [hh.2.2.2.2.2.1,abs_of_pos hh.2.2.1] at hn
      norm_num at hn
      have hb := norm_sub_le (5*z/2) (3:ℂ)
      norm_num [norm_div,norm_mul] at hb
      rw [mem_closedBall,dist_zero_right]
      linarith [hh.2.2.2.1]
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  have hdr : ((fundamentalOnsetExceptionFinset N).card:ℝ) ≤
      (↑(∑ᶠ u, (MeromorphicOn.divisor onsetPulseTransform (closedBall 0 (4*(N:ℝ)))) u):ℝ) := by
    exact_mod_cast hd
  have hb := hB (4*(N:ℝ)) (by linarith)
  nlinarith

/-- The actual fixed onset is evaluated on this affine Xi argument; no duration is changed. -/
theorem trueFundamental_clearedOnset (q : XiZeroCopy) :
    clearedOnset (physicalRate q true) (physicalFundamentalFrequency q true)=
      onsetPulseTransform (5*(q.1:ℂ)/2-3) := by
  rw [clearedOnset_eq_onsetPulseTransform,physicalFundamentalFrequency_eq]
  congr 1
  simp only [physicalRate,↓reduceIte]
  ring

/-- Actual simple critical zeros with vanishing full physical fundamental Laurent coefficient. -/
def fundamentalPoleExceptionFinset (N : ℕ) : Finset ℂ := by
  classical
  exact (xiSimpleCriticalZeroFinset ((N:ℝ)/3)).filter
    (fun z => ∃ q : XiZeroCopy, (q.1:ℂ)=z ∧ physicalSelfResidueCoefficient q true true 1 (-1)=0)

private theorem pole_exceptions_subset (H : ℝ)
    (hH : ∀ q : XiZeroCopy, H≤|(q.1:ℂ).im| →
      fundamentalSourceMoment (physicalFundamentalFrequency q true) (physicalRate q true) 1 ≠ 0)
    (N : ℕ) :
    fundamentalPoleExceptionFinset N ⊆
      fundamentalCanonicalCriticalZeroFinset N ∪ fundamentalOnsetExceptionFinset N ∪
        xiSimpleCriticalZeroFinset H := by
  classical
  intro z hz
  obtain ⟨hzset,q,hq,hv⟩ := Finset.mem_filter.mp hz
  have hd := mem_xiSimpleCriticalZeroFinset.mp hzset
  by_cases hlow : z.im≤H
  · exact Finset.mem_union_right _ (mem_xiSimpleCriticalZeroFinset.mpr
      ⟨hd.1,hd.2.1,hd.2.2.1,hlow,hd.2.2.2.2⟩)
  have hM := hH q (by rw [hq,abs_of_pos hd.2.2.1];linarith)
  rw [physicalSelfResidueCoefficient_zero_iff,physicalFundamentalGreen_zero_iff q true true 1 (-1)
    (by norm_num)] at hv
  rcases hv with hC|hM0|hO
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    refine Finset.mem_filter.mpr ⟨hzset,q,hq,?_⟩
    rw [D4BMOriginalSourceResolvent.canonicalQNMValue_eq_source_periods]
    rw [hC,mul_zero,zero_mul]
  · exact (hM hM0).elim
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    refine Finset.mem_filter.mpr ⟨hzset,?_⟩
    rw [trueFundamental_clearedOnset,hq] at hO
    exact hO

/-- Only linearly many actual simple critical sources lose the original physical fundamental pole. -/
theorem fundamentalPoleExceptionFinset_card_linear :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ((fundamentalPoleExceptionFinset N).card:ℝ) ≤ K*(1+(N:ℝ)) := by
  obtain ⟨H,hH,hM⟩ := physicalFundamentalSourceMoment_high_height_ne_zero
  obtain ⟨K,hK,hC⟩ := fundamentalCanonicalCriticalZeroFinset_card_linear
  obtain ⟨L,hL,hO⟩ := fundamentalOnsetExceptionFinset_card_linear
  let E := (xiSimpleCriticalZeroFinset H).card
  refine ⟨K+L+E,by positivity,?_⟩
  filter_upwards [hC,eventually_ge_atTop (2:ℕ)] with N hCN hN
  have hON := hO N hN
  have hs := pole_exceptions_subset H (fun q hq => hM q hq 1 one_ne_zero) N
  have h0 := Finset.card_le_card hs
  have h1 := Finset.card_union_le
    (fundamentalCanonicalCriticalZeroFinset N ∪ fundamentalOnsetExceptionFinset N)
    (xiSimpleCriticalZeroFinset H)
  have h2 := Finset.card_union_le
    (fundamentalCanonicalCriticalZeroFinset N) (fundamentalOnsetExceptionFinset N)
  have hc : (fundamentalPoleExceptionFinset N).card ≤
      (fundamentalCanonicalCriticalZeroFinset N).card+(fundamentalOnsetExceptionFinset N).card+E := by
    dsimp only [E]
    omega
  have hcr : ((fundamentalPoleExceptionFinset N).card:ℝ) ≤
      (fundamentalCanonicalCriticalZeroFinset N).card+(fundamentalOnsetExceptionFinset N).card+E := by
    exact_mod_cast hc
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) E) (Nat.cast_nonneg (α:=ℝ) N)]

/-- The original physical pole survives on a relative density-one subset of simple critical Xi sources. -/
theorem fundamentalPoleExceptionFinset_relative_density_zero (eps : ℝ) (heps : 0<eps) :
    ∀ᶠ N : ℕ in atTop,
      ((fundamentalPoleExceptionFinset N).card:ℝ) ≤
        eps*(xiSimpleCriticalZeroCount ((N:ℝ)/3):ℝ) := by
  obtain ⟨K,hK,hbound⟩ := fundamentalPoleExceptionFinset_card_linear
  have hscale : Tendsto (fun N : ℕ => (N:ℝ)/3) atTop atTop :=
    (show Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have hlower := hscale.eventually eventually_superlinear_xiSimpleCriticalZeroCount
  have hlog := (Real.tendsto_log_atTop.comp hscale).eventually_ge_atTop (216*Real.pi*(2*K/eps))
  filter_upwards [hbound,hlower,hlog,eventually_ge_atTop (12:ℕ)] with N hB hL hlogN hN
  have hNr : (12:ℝ)≤N := by exact_mod_cast hN
  have hlarge : (2*K/eps)*(N:ℝ) ≤ (xiSimpleCriticalZeroCount ((N:ℝ)/3):ℝ) := by
    calc
      _ = (1/(72*Real.pi))*((N:ℝ)/3)*(216*Real.pi*(2*K/eps)) := by
        field_simp [Real.pi_pos.ne',heps.ne']; ring
      _ ≤ (1/(72*Real.pi))*((N:ℝ)/3)*Real.log ((N:ℝ)/3) := by
        apply mul_le_mul_of_nonneg_left hlogN
        positivity
      _ ≤ _ := hL
  calc
    _ ≤ K*(1+(N:ℝ)) := hB
    _ ≤ 2*K*(N:ℝ) := by nlinarith
    _ = eps*((2*K/eps)*(N:ℝ)) := by field_simp [heps.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hlarge heps.le

/-- Surviving unit-source poles persist for every nonzero original amplitude and every interior detector. -/
theorem physicalPole_all_amplitudes_all_detectors (q : XiZeroCopy)
    (hR : physicalSelfResidueCoefficient q true true 1 (-1)≠0)
    (a : ℂ) (ha : a≠0) (t : ℝ) (ht : t<0) :
    ¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q true w a t)
      (𝓝[≠] physicalFundamentalFrequency q true) (𝓝 c) := by
  have hu : ¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q true w 1 (-1))
      (𝓝[≠] physicalFundamentalFrequency q true) (𝓝 c) := by
    rw [continuedPhysicalSelfResponse_finite_limit_iff q true true 1 (-1) (by norm_num)]
    exact hR
  obtain ⟨hC,hM,hO⟩ := (continuedPhysicalSelfResponse_nonremovable_iff_moment q true true 1 (-1)
    (by norm_num)).mp hu
  apply (continuedPhysicalSelfResponse_nonremovable_iff_moment q true true a t ht).mpr
  refine ⟨hC,?_,hO⟩
  rw [physicalFundamentalSourceMoment_amplitude q a]
  exact mul_ne_zero (pow_ne_zero 2 ha) hM

end
end RHTower.D4BMJointSource

open Complex Set Filter Topology
namespace RHTower
open D4BMJointSource D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- An actual critical Xi source has a genuine original Green-response fundamental pole. -/
theorem exists_critical_physicalPole_ne_zero :
    ∃ q : XiZeroCopy, (q.1:ℂ).re=1/2 ∧ physicalSelfResidueCoefficient q true true 1 (-1)≠0 := by
  classical
  by_contra h
  have hall : ∀ q : XiZeroCopy, (q.1:ℂ).re=1/2 → physicalSelfResidueCoefficient q true true 1 (-1)=0 := by
    simpa only [not_exists,not_and,not_not] using h
  have hbound := fundamentalPoleExceptionFinset_relative_density_zero (1/2) (by norm_num)
  have hscale : Tendsto (fun N : ℕ => (N:ℝ)/3) atTop atTop :=
    (show Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have hlower := hscale.eventually eventually_superlinear_xiSimpleCriticalZeroCount
  have hfalse : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hbound,hlower,eventually_ge_atTop (12:ℕ)] with N hB hL hN
    have hNr : (12:ℝ)≤N := by exact_mod_cast hN
    have heq : fundamentalPoleExceptionFinset N=xiSimpleCriticalZeroFinset ((N:ℝ)/3) := by
      apply Finset.Subset.antisymm (Finset.filter_subset _ _)
      intro z hz
      have hd := mem_xiSimpleCriticalZeroFinset.mp hz
      refine Finset.mem_filter.mpr ⟨hz,?_⟩
      let rho : XiDivisorSupport := ⟨z,mem_xi_divisor_support_of_eq_zero hd.2.2.2.2.1⟩
      have hp := xi_divisor_pos_on_support rho
      let q : XiZeroCopy := ⟨rho,⟨0,by omega⟩⟩
      exact ⟨q,rfl,hall q hd.2.2.2.2.2.1⟩
    rw [heq,card_xiSimpleCriticalZeroFinset] at hB
    have hlogpos : 0<Real.log ((N:ℝ)/3) := Real.log_pos (by linarith)
    have hpos : 0<(1/(72*Real.pi))*((N:ℝ)/3)*Real.log ((N:ℝ)/3) := by positivity
    nlinarith
  obtain ⟨N,hN⟩ := hfalse.exists
  exact hN

/-- A regular full canonical action can coexist with an actual Green pole at every
interior detector and every nonzero amplitude, on an actual critical Xi source. -/
theorem exists_critical_regular_action_with_physical_pole :
    ∃ q : XiZeroCopy, (q.1:ℂ).re=1/2 ∧
      AnalyticAt ℂ (D4BMOriginalCanonicalAction.canonicalQNMAction q true true 1)
        (physicalFundamentalFrequency q true) ∧
      ∀ (a : ℂ), a≠0 → ∀ (t : ℝ), t<0 →
        ¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q true w a t)
          (𝓝[≠] physicalFundamentalFrequency q true) (𝓝 c) := by
  obtain ⟨q,hq,hR⟩ := exists_critical_physicalPole_ne_zero
  exact ⟨q,hq,(D4BMOriginalCanonicalAction.canonical_action_QNM q true true 1).1,
    physicalPole_all_amplitudes_all_detectors q hR⟩

/-- Switching from the regular canonical value to the genuine physical pole does not
restore matching with the unchanged complementary unit-source clock. -/
theorem not_exists_hbXiPeierls_physicalPole_matching :
    ¬ ∃ returned : XiZeroCopy → HBXiPeierlsCarrier,
      ∀ q : XiZeroCopy, hbXiPeierlsSourceProbeProfile returned q=
        physicalSelfResidueCoefficient q true true 1 (-1) := by
  rintro ⟨returned,hmatch⟩
  obtain ⟨q,hline,hne⟩ := exists_critical_physicalPole_ne_zero
  exact hne ((hmatch q).symm.trans (hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine returned q hline))

/-- Even the extinction locus of the actual original fundamental pole differs from the unit clock. -/
theorem not_exists_hbXiPeierls_physicalPole_extinction_matching :
    ¬ ∃ returned : XiZeroCopy → HBXiPeierlsCarrier,
      ∀ q : XiZeroCopy, (physicalSelfResidueCoefficient q true true 1 (-1)=0 ↔
        hbXiPeierlsSourceProbeProfile returned q=0) := by
  rintro ⟨returned,hmatch⟩
  obtain ⟨q,hline,hne⟩ := exists_critical_physicalPole_ne_zero
  exact hne ((hmatch q).mpr (hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine returned q hline))

end
end RHTower
