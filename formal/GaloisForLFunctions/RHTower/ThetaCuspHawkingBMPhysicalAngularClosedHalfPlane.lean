import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinRamanujanProductDirichletSeries
import Mathlib.Analysis.Normed.Group.Tannery
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularSourceXi

/-! Closed-half-plane evaluation of the original physical angular source, including critical Xi copies. -/

open Complex Filter Topology
namespace RHTower
noncomputable section
set_option autoImplicit false

private theorem divisor_shift_sum (a : ℂ) (n : ℕ) :
    d4BMGeneralizedDivisorArithmetic a n=∑ d∈n.divisors,(d:ℂ)^a := by
  rw [d4BMGeneralizedDivisorArithmetic,ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d≠0 := by intro h;subst d;simp at hd
  simp only [d4BMPowerArithmetic_apply,ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply,if_neg hd0,Nat.cast_one,one_mul]

private theorem divisor_shift_continuous (n : ℕ) :
    Continuous (fun a : ℂ => d4BMGeneralizedDivisorArithmetic a n) := by
  simp_rw [divisor_shift_sum]
  apply continuous_finsetSum
  intro d hd
  have hd0 : (d:ℂ)≠0 := by
    apply Nat.cast_ne_zero.mpr
    intro h
    subst d
    simp at hd
  exact continuous_id.const_cpow (Or.inl hd0)

/-- The four-zeta divisor-product identity reaches purely imaginary shifts
 by an actual uniformly dominated Dirichlet-series limit. -/
theorem LSeries_d4BMDivisorProductArithmetic_eq_fourZetaQuotient_closed
    (a b w : ℂ) (ha : a.re≤0) (hb : b.re≤0) (hw : 1<w.re) :
    LSeries (d4BMDivisorProductArithmetic a b) w=
      riemannZeta w*riemannZeta (w-a)*riemannZeta (w-b)*riemannZeta (w-a-b)/
        riemannZeta (2*w-a-b) := by
  let f : ℝ→ℕ→ℂ := fun e => LSeries.term
    (d4BMDivisorProductArithmetic (a-(e:ℂ)) (b-(e:ℂ))) w
  let g : ℕ→ℂ := LSeries.term (d4BMDivisorProductArithmetic a b) w
  let bound : ℕ→ℝ := fun n => ‖LSeries.term (fun k : ℕ => ((k.divisors.card^(2 : ℕ):ℕ):ℂ)) w n‖
  have hsum : Summable bound := (Sieve.divisorSquareLSeriesSummable hw).norm
  have hterm (n : ℕ) : Tendsto (fun e => f e n) (𝓝[>] (0:ℝ)) (𝓝 (g n)) := by
    have hcoef : Continuous (fun e : ℝ =>
        d4BMDivisorProductArithmetic (a-(e:ℂ)) (b-(e:ℂ)) n) := by
      simp only [d4BMDivisorProductArithmetic_apply]
      exact ((divisor_shift_continuous n).comp (by fun_prop)).mul
        ((divisor_shift_continuous n).comp (by fun_prop))
    have hc : Continuous (fun e => f e n) := by
      by_cases hn : n=0
      · subst n
        simp only [f,LSeries.term_zero]
        exact continuous_const
      · simp only [f,LSeries.term_of_ne_zero hn]
        exact hcoef.div_const _
    simpa only [f,g,Complex.ofReal_zero,sub_zero] using
      hc.continuousAt.tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  have hbound : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ),∀ n,‖f e n‖≤bound n := by
    filter_upwards [self_mem_nhdsWithin] with e he
    change 0 < e at he
    let A : D4BMNegativeDivisorShift := ⟨a-(e:ℂ),by simp only [Complex.sub_re,Complex.ofReal_re];linarith⟩
    let B : D4BMNegativeDivisorShift := ⟨b-(e:ℂ),by simp only [Complex.sub_re,Complex.ofReal_re];linarith⟩
    intro n
    exact LSeries.norm_term_le w (norm_d4BMDivisorProductArithmetic_le_divisorSquare A B n)
  have hlim := tendsto_tsum_of_dominated_convergence hsum hterm hbound
  have hL : Tendsto (fun e : ℝ => LSeries (d4BMDivisorProductArithmetic (a-(e:ℂ)) (b-(e:ℂ))) w)
      (𝓝[>] (0:ℝ)) (𝓝 (LSeries (d4BMDivisorProductArithmetic a b) w)) := hlim
  let rhs : ℝ→ℂ := fun e => riemannZeta w*riemannZeta (w-(a-(e:ℂ)))*
    riemannZeta (w-(b-(e:ℂ)))*riemannZeta (w-(a-(e:ℂ))-(b-(e:ℂ)))/
      riemannZeta (2*w-(a-(e:ℂ))-(b-(e:ℂ)))
  have hz (z : ℂ) (hr : 1<z.re) : ContinuousAt riemannZeta z := by
    apply (analyticOn_riemannZeta z ?_).continuousAt
    intro he
    subst z
    norm_num at hr
  have ha' : 1<(w-a).re := by simp only [Complex.sub_re];linarith
  have hb' : 1<(w-b).re := by simp only [Complex.sub_re];linarith
  have hab : 1<(w-a-b).re := by simp only [Complex.sub_re];linarith
  have hden : 1<(2*w-a-b).re := by simp only [Complex.sub_re,Complex.mul_re];norm_num;linarith
  have hca : ContinuousAt (fun e : ℝ => riemannZeta (w-(a-(e:ℂ)))) 0 := by
    exact (hz _ ha').comp_of_eq (by fun_prop) (by simp)
  have hcb : ContinuousAt (fun e : ℝ => riemannZeta (w-(b-(e:ℂ)))) 0 := by
    exact (hz _ hb').comp_of_eq (by fun_prop) (by simp)
  have hcab : ContinuousAt (fun e : ℝ => riemannZeta (w-(a-(e:ℂ))-(b-(e:ℂ)))) 0 := by
    exact (hz _ hab).comp_of_eq (by fun_prop) (by simp)
  have hcd : ContinuousAt (fun e : ℝ => riemannZeta (2*w-(a-(e:ℂ))-(b-(e:ℂ)))) 0 := by
    exact (hz _ hden).comp_of_eq (by fun_prop) (by simp)
  have hc : ContinuousAt rhs 0 := by
    apply (((continuousAt_const.mul hca).mul hcb).mul hcab).div hcd
    simpa using riemannZeta_ne_zero_of_one_lt_re hden
  have hR := hc.tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  have he : (fun e : ℝ => LSeries (d4BMDivisorProductArithmetic (a-(e:ℂ)) (b-(e:ℂ))) w)
      =ᶠ[𝓝[>] (0:ℝ)] rhs := by
    filter_upwards [self_mem_nhdsWithin] with e he
    change 0 < e at he
    let A : D4BMNegativeDivisorShift := ⟨a-(e:ℂ),by simp only [Complex.sub_re,Complex.ofReal_re];linarith⟩
    let B : D4BMNegativeDivisorShift := ⟨b-(e:ℂ),by simp only [Complex.sub_re,Complex.ofReal_re];linarith⟩
    let P : D4BMRamanujanProductChamber := ⟨A,B,w,hw⟩
    have h := LSeries_d4BMDivisorProductArithmetic_eq_fourZetaQuotient P
    simpa only [P,A,B,d4BMRamanujanFourZetaValue,d4BMRamanujanPolarZetaValue,rhs,sub_add_eq_sub_sub] using h
  have hv := tendsto_nhds_unique hL (hR.congr' he.symm)
  simpa only [rhs,Complex.ofReal_zero,sub_zero] using hv

end
end RHTower

open MeasureTheory Set
namespace RHTower.D4BMCuspProjection
open D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- The actual divisor identity includes critical Xi copies. -/
theorem nativeRamanujan_value_closedHalfPlane (q : XiZeroCopy)
    (hq : 1/2 ≤ (q.1:ℂ).re) (s : ℂ) (hs : 2 < s.re) :
    LSeries (d4BMDivisorProductArithmetic (-2*center q) (-2*center q)) (s-2*center q) =
      riemannZeta (s-2*center q)*riemannZeta s^(2 : ℕ)*riemannZeta (s+2*center q)/riemannZeta (2*s) := by
  have ha : (-2*center q).re ≤ 0 := by
    simp [D4BMGlobalAngularResponse.center]
    linarith
  have hw : 1 < (s-2*center q).re := by
    have hu := (xi_divisor_support_re_mem_open_unit q.1).2
    simp [D4BMGlobalAngularResponse.center]
    linarith
  have h := LSeries_d4BMDivisorProductArithmetic_eq_fourZetaQuotient_closed
    (-2*center q) (-2*center q) (s-2*center q) ha ha hw
  rw [show (s-2*center q)-(-2*center q)=s by ring,
    show s-(-2*center q)=s+2*center q by ring,
    show 2*(s-2*center q)-(-2*center q)-(-2*center q)=2*s by ring] at h
  simpa only [pow_two,mul_assoc] using h

private theorem native_archimedean_value (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    8*Complex.Gammaℝ (2*s)*(((2*Real.pi:ℝ):ℂ)^(-s))*nativeBesselMellinFactor q s =
      Complex.Gammaℝ (s+2*center q)*Complex.Gammaℝ s^(2 : ℕ)*Complex.Gammaℝ (s-2*center q) := by
  have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2pi : ((2:ℂ)*(Real.pi:ℂ))^(-s) = (2:ℂ)^(-s)*(Real.pi:ℂ)^(-s) := by
    simpa using Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) Real.pi_pos.le (-s)
  have h2 : (2:ℂ)^(-s)*(2:ℂ)^(s-3) = 1/8 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),show -s+(s-3)=(-3:ℂ) by ring]
    have h := Complex.cpow_neg_eq_inv_pow_ofReal_pos (a := 2) (by norm_num : (0:ℝ)<2) (3:ℂ)
    norm_num at h ⊢
    exact h
  have hp : (Real.pi:ℂ)^(-s)*(Real.pi:ℂ)^(-s) =
      (Real.pi:ℂ)^(-(s+2*center q)/2)*((Real.pi:ℂ)^(-s/2))^(2 : ℕ)*(Real.pi:ℂ)^(-(s-2*center q)/2) := by
    rw [pow_two]
    repeat' rw [← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  unfold nativeBesselMellinFactor
  rw [Complex.Gammaℝ,Complex.Gammaℝ,Complex.Gammaℝ,Complex.Gammaℝ]
  norm_num
  rw [show -(2*s)/2=-s by ring,show (s+2*center q)/2=s/2+center q by ring,
    show (s-2*center q)/2=s/2-center q by ring,h2pi]
  calc
    _ = (8*((2:ℂ)^(-s)*(2:ℂ)^(s-3)))*
        (((Real.pi:ℂ)^(-s)*(Real.pi:ℂ)^(-s))*
          (Complex.Gamma (s/2+center q)*Complex.Gamma (s/2)^(2 : ℕ)*Complex.Gamma (s/2-center q))) := by
      field_simp [hg]
    _ = ((Real.pi:ℂ)^(-s)*(Real.pi:ℂ)^(-s))*
          (Complex.Gamma (s/2+center q)*Complex.Gamma (s/2)^(2 : ℕ)*Complex.Gamma (s/2-center q)) := by
      rw [h2]
      ring
    _ = _ := by rw [hp]; ring

/-- The original half-square's diagonal Fourier contribution has the derived half four-Lambda value. -/
theorem nativeDiagonalPeriod_fourLambda_closedHalfPlane (q : XiZeroCopy) (hq : 1/2 ≤ (q.1:ℂ).re)
    (s : ℂ) (hs : 2 < s.re) :
    4*reflectedCompletedLambda (2*s)*
      (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ))) =
        (reflectedCompletedLambda (s+2*center q)*reflectedCompletedLambda s^(2 : ℕ)*
          reflectedCompletedLambda (s-2*center q))/2 := by
  rw [nativeFourierMellin_lseries q s hs,nativeRamanujan_value_closedHalfPlane q hq s hs]
  have hz : riemannZeta (2*s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  change 4*(Complex.Gammaℝ (2*s)*riemannZeta (2*s))*
    ((((2*Real.pi:ℝ):ℂ)^(-s)*nativeBesselMellinFactor q s)*
      (riemannZeta (s-2*center q)*riemannZeta s^(2 : ℕ)*riemannZeta (s+2*center q)/riemannZeta (2*s))) = _
  calc
    _ = (8*Complex.Gammaℝ (2*s)*(((2*Real.pi:ℝ):ℂ)^(-s))*nativeBesselMellinFactor q s)*
      (riemannZeta (s+2*center q)*riemannZeta s^(2 : ℕ)*riemannZeta (s-2*center q))/2 := by
      field_simp [hz]
      ring
    _ = _ := by
      rw [native_archimedean_value q s hs]
      unfold reflectedCompletedLambda
      ring

end
end RHTower.D4BMCuspProjection
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMCuspProjection
noncomputable section
set_option autoImplicit false

/-- The full original period has the half four-Lambda value with its exact surviving cutoff correction. -/
theorem scalarResidualPeriod_fourLambda_with_cutoff_closedHalfPlane (q : XiZeroCopy) (hq : 1/2 ≤ (q.1:ℂ).re)
    (s : ℂ) (hs : 2 < s.re) :
    scalarResidualPeriod q (s-1/2) =
      (reflectedCompletedLambda (s+2*center q)*reflectedCompletedLambda s^(2 : ℕ)*
        reflectedCompletedLambda (s-2*center q))/2+
      reflectedCompletedLambda (2*s)*(∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*nativePrincipalRemainder q y)-
      reflectedCompletedLambda (2*s-1)*(∫ y in Ioi (2:ℝ), (y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y) := by
  rw [scalarResidualPeriod_eq_three_moments q s hs,nativeDiagonalPeriod_fourLambda_closedHalfPlane q hq s hs]
/-- The constructed continuation agrees with the actual original quotient integral in its proved chamber. -/
theorem nativePeriodContinuation_eq_original_closedHalfPlane (q : XiZeroCopy) (hq : 1/2 ≤ (q.1:ℂ).re)
    (s : ℂ) (hs : 2 < s.re) :
    nativePeriodContinuation q s = scalarResidualPeriod q (s-1/2) := by
  rw [scalarResidualPeriod_fourLambda_with_cutoff_closedHalfPlane q hq s hs,
    nativePrincipalRemainder_mellin_value q s hs,nativeSquareCutoffHeight_mellin_value q s hs]
  unfold nativePeriodContinuation
  ring

/-- The original cleared quotient integral and the derived continuation agree as germs everywhere. -/
theorem clearedResidualPeriod_eventuallyEq_continuation_closedHalfPlane (q : XiZeroCopy)
    (hq : 1/2 ≤ (q.1:ℂ).re) (u : ℂ) :
    clearedResidualPeriod q =ᶠ[𝓝[≠] u]
      (fun v => clearFactor v * nativePeriodContinuation q (v+1/2)) := by
  let d := fun v => clearedResidualPeriod q v - clearFactor v * nativePeriodContinuation q (v+1/2)
  have hd : MeromorphicOn d univ := by
    intro v _
    have hP : AnalyticAt ℂ clearFactor v := by unfold clearFactor; fun_prop
    have hJ : MeromorphicAt (fun w : ℂ => nativePeriodContinuation q (w+1/2)) v :=
      (nativePeriodContinuation_meromorphic q (v+1/2)).comp_analyticAt
        (g := fun w : ℂ => w+1/2) (x := v) (analyticAt_id.add analyticAt_const)
    exact ((clearedResidualPeriod_differentiable q).analyticAt v).meromorphicAt.sub
      (hP.meromorphicAt.mul hJ)
  have ha : meromorphicOrderAt d (3+I) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hr : ∀ᶠ v : ℂ in 𝓝 (3+I), 2 < (v+1/2).re :=
      (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by norm_num)
    have hi : ∀ᶠ v : ℂ in 𝓝 (3+I), v.im ≠ 0 :=
      ((show IsOpen {x : ℝ | x ≠ 0} from isOpen_ne).preimage
        Complex.continuous_im).mem_nhds (by norm_num)
    filter_upwards [hr.filter_mono nhdsWithin_le_nhds,hi.filter_mono nhdsWithin_le_nhds] with v hv hiv
    dsimp [d]
    rw [clearedResidualPeriod_eq q v hiv,nativePeriodContinuation_eq_original_closedHalfPlane q hq _ hv]
    simp
  have hu : meromorphicOrderAt d u = ⊤ := by
    by_contra h
    exact (hd.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ u) (mem_univ (3+I)) h) ha
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hu] with v hv
  exact sub_eq_zero.mp hv

private theorem physical_clearFactor_ne_zero (q : XiZeroCopy) :
    clearFactor (((q.1:ℂ)-1)/2) ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have h0 : ((q.1:ℂ)-1)/2 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hi (by linarith)
  have hm : 2*(((q.1:ℂ)-1)/2)-1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hi (by linarith)
  have hp : 2*(((q.1:ℂ)-1)/2)+1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hi (by linarith)
  exact mul_ne_zero (mul_ne_zero h0 hm) hp

/-- The actual absolutely convergent physical quotient integral equals the full continued value. -/
theorem scalarResidualPeriod_physical_eq_continuation_closedHalfPlane (q : XiZeroCopy)
    (hq : 1/2 ≤ (q.1:ℂ).re) :
    scalarResidualPeriod q (((q.1:ℂ)-1)/2) = nativePeriodContinuation q ((q.1:ℂ)/2) := by
  let u : ℂ := ((q.1:ℂ)-1)/2
  have he : u+1/2 = (q.1:ℂ)/2 := by dsimp [u]; ring
  have hJ : ContinuousAt (fun v : ℂ => nativePeriodContinuation q (v+1/2)) u := by
    have hc := (nativePeriodContinuation_physical_analytic q).continuousAt
    rw [← he] at hc
    exact hc.comp (f := fun v : ℂ => v+1/2) (by fun_prop)
  have hP : ContinuousAt clearFactor u := by unfold clearFactor; fun_prop
  have hvalue := tendsto_nhds_unique_of_eventuallyEq
    (((clearedResidualPeriod_differentiable q).continuous.continuousAt (x := u)).mono_left
      nhdsWithin_le_nhds)
    ((hP.mul hJ).mono_left nhdsWithin_le_nhds)
    (clearedResidualPeriod_eventuallyEq_continuation_closedHalfPlane q hq u)
  have hi : u.im ≠ 0 := by
    dsimp [u]
    simpa using div_ne_zero (xi_divisor_support_im_ne_zero q.1) (by norm_num : (2:ℝ) ≠ 0)
  simp only [Pi.mul_apply] at hvalue
  rw [clearedResidualPeriod_eq q u hi,he] at hvalue
  exact mul_left_cancel₀ (physical_clearFactor_ne_zero q) hvalue

/-- The complete physical angular source has the same formula on the closed right half-plane,
including all critical copies. All original principal corrections cancel after assembly. -/
theorem physicalSelfSourceCoefficient_fourLambda_closedHalfPlane (q : XiZeroCopy)
    (hq : 1/2 ≤ (q.1:ℂ).re) :
    physicalSelfSourceCoefficient q =
      (reflectedCompletedLambda (5*(q.1:ℂ)/2-1)*reflectedCompletedLambda ((q.1:ℂ)/2)^(2 : ℕ)*
        reflectedCompletedLambda (1-3*(q.1:ℂ)/2))/2 := by
  rw [physicalSelfSourceCoefficient,physicalPrincipalCorrection_eq_nativeMoment,
    physicalAngularParameter_eq,scalarResidualPeriod_physical_eq_continuation_closedHalfPlane q hq,
    nativePeriodContinuation_physical_value]
  ring

/-- The remaining angular cancellation is exactly a zero of one of the three displayed native completion factors. -/
theorem physicalSelfSourceCoefficient_zero_iff_Lambda_closedHalfPlane (q : XiZeroCopy) (hq : 1/2 ≤ (q.1:ℂ).re) :
    physicalSelfSourceCoefficient q = 0 ↔
      reflectedCompletedLambda (5*(q.1:ℂ)/2-1) = 0 ∨
      reflectedCompletedLambda ((q.1:ℂ)/2) = 0 ∨
      reflectedCompletedLambda (1-3*(q.1:ℂ)/2) = 0 := by
  rw [physicalSelfSourceCoefficient_fourLambda_closedHalfPlane q hq]
  simp only [div_eq_zero_iff,mul_eq_zero,pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)]
  norm_num [or_assoc]
/-- No cutoff or Gamma ambiguity remains: angular cancellation is exactly incidence at these three original Xi arguments. -/
theorem physicalSelfSourceCoefficient_zero_iff_xi_closedHalfPlane (q : XiZeroCopy) (hq : 1/2 ≤ (q.1:ℂ).re) :
    physicalSelfSourceCoefficient q = 0 ↔
      xi (5*(q.1:ℂ)/2-1) = 0 ∨ xi ((q.1:ℂ)/2) = 0 ∨ xi (3*(q.1:ℂ)/2) = 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have ha : (5*(q.1:ℂ)/2-1).im ≠ 0 := by
    simpa [Complex.mul_im] using div_ne_zero (mul_ne_zero (by norm_num : (5:ℝ) ≠ 0) hi)
      (by norm_num : (2:ℝ) ≠ 0)
  have hb : ((q.1:ℂ)/2).im ≠ 0 := by simpa using div_ne_zero hi (by norm_num : (2:ℝ) ≠ 0)
  have hc : (1-3*(q.1:ℂ)/2).im ≠ 0 := by
    simpa [Complex.mul_im] using neg_ne_zero.mpr
      (div_ne_zero (mul_ne_zero (by norm_num : (3:ℝ) ≠ 0) hi) (by norm_num : (2:ℝ) ≠ 0))
  rw [physicalSelfSourceCoefficient_zero_iff_Lambda_closedHalfPlane q hq,nativeCompletedLambda_zero_iff_xi ha,
    nativeCompletedLambda_zero_iff_xi hb,nativeCompletedLambda_zero_iff_xi hc,xi_one_sub]


end
end RHTower.D4BMJointSource
