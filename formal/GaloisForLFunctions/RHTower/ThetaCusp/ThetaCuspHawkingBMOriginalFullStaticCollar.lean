import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalStaticMetricCollar
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalStaticForcingRestoration

open Set Filter Topology MeasureTheory Complex
namespace RHTower.D4BMOriginalFullStaticCollar
open D4BMJointSource D4BMLaplaceRadial D4BMModularCore D4BMJointWave
open D4BMOriginalFullMetricCollar D4BMOriginalFullMetricDifference
open D4BMOriginalStaticMetricCollar D4BMOriginalStaticTracePrimitive
open D4BMOriginalStaticForcingTriangle D4BMOriginalStaticForcingRestoration
noncomputable section
set_option autoImplicit false
private abbrev mu (q : XiZeroCopy) := D4BMLeftModeRadialEquation.eigenvalue q

private theorem moving_forcing_moment (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a T L k : ℝ) :
    forcingMoment q br amp w a (max a (T-L/2)) L k=
      mu q*w*((∫ p in a..max a (T-L/2),onsetDensity q br w p)*
        forcingKernelDifference q br amp w k (-L/2)) := by
  unfold forcingMoment
  simp_rw [original_forcing_error_kernel]
  rw [intervalIntegral.integral_mul_const]
  rfl

/-- Separate admission of the literal forcing moment on the moving static
collar, before subtracting it from the full physical metric integral. -/
theorem static_forcing_moment_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a A B T k : ℝ) (hA : 0 < A) (hAB : A ≤ B) :
    IntervalIntegrable (fun L => forcingMoment q br amp w a (max a (T-L/2)) L k) volume A B := by
  have ht : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  have hf : Continuous (onsetDensity q br w) := by unfold onsetDensity;fun_prop
  have hI : Continuous (fun L : ℝ => ∫ p in a..max a (T-L/2),onsetDensity q br w p) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ:=volume) (a₀:=a) (f:=fun _ : ℝ => onsetDensity q br w)
      (hf.comp continuous_snd) (show Continuous (fun L : ℝ => max a (T-L/2)) by fun_prop)
  have hmap : MapsTo (fun L : ℝ => -L/2) (Icc A B) (Iio (0:ℝ)) := by
    intro L hL
    change -L/2 < 0
    linarith [hL.1]
  have hK := (forcing_kernel_difference_continuous q br amp w k).comp
    (show ContinuousOn (fun L : ℝ => -L/2) (Icc A B) by fun_prop) hmap
  have hi : IntervalIntegrable (fun L => mu q*w*((∫ p in a..max a (T-L/2),onsetDensity q br w p)*
      forcingKernelDifference q br amp w k (-L/2))) volume A B :=
    ((hI.continuousOn.mul hK).const_mul (mu q*w)).intervalIntegrable_of_Icc hAB
  exact hi.congr (fun L _ => (moving_forcing_moment q br amp w a T L k).symm)

/-- The original radial one-half Jacobian gives the literal causal forcing
triangle, with its original moving time endpoint. -/
theorem static_forcing_moment_collar (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a A B T k : ℝ) :
    (∫ L in A..B,forcingMoment q br amp w a (max a (T-L/2)) L k)/2=
      mu q*w*staticForcingCut q br amp w a (-B/2) (-A/2) T k := by
  simp_rw [moving_forcing_moment]
  rw [intervalIntegral.integral_const_mul]
  let f := fun x : ℝ => forcingKernelDifference q br amp w k x*
    (∫ p in a..max a (T+x),onsetDensity q br w p)
  have he : (fun L : ℝ => (∫ p in a..max a (T-L/2),onsetDensity q br w p)*
      forcingKernelDifference q br amp w k (-L/2))=fun L => f (L*(-(1/2:ℝ))) := by
    funext L
    have hx : -L/2=L*(-(1/2:ℝ)) := by ring
    dsimp [f]
    rw [show T-L/2=T+L*(-(1/2:ℝ)) by ring,hx,mul_comm]
  rw [he,intervalIntegral.integral_comp_mul_right f (by norm_num : -(1/2:ℝ) ≠ 0)]
  rw [show A*(-(1/2:ℝ))=-A/2 by ring,show B*(-(1/2:ℝ))=-B/2 by ring]
  rw [show (∫ x in -A/2..-B/2,f x)=-(∫ x in -B/2..-A/2,f x) from intervalIntegral.integral_symm _ _]
  change _=mu q*w*(∫ x in -B/2..-A/2,f x)
  norm_num [smul_eq_mul]
  ring

/-- The complete original moving metric discrepancy, retaining its derived
source/boundary mass and the unchanged forcing counterterm transported along
the causal boundary. -/
def fullStaticDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a A B T k : ℝ) : ℂ :=
  (∫ L in A..B,metricDifference q br amp w a (max a (T-L/2)) L k)/2-
    (max a (T-A/2)-max a (T-B/2))•traceMass q br amp w k a-
    mu q*w*staticForcingCounterterm q br amp w a (-B/2) (-A/2) T k

private theorem horizon_depth_tendsto :
    Tendsto (fun L : ℝ => horizonCoordinate (-L/2)) atTop (𝓝[>] (0:ℝ)) := by
  have hx : Tendsto (fun L : ℝ => -L/2) atTop atBot := by
    apply tendsto_atBot.mpr
    intro x
    filter_upwards [eventually_ge_atTop (-2*x)] with L hL
    linarith
  exact D4BMFundamentalNorm.horizonCoordinate_tendsto_positive.comp hx

/-- Complete finite-cusp restoration on the actual static-time metric collar.
The original metric and forcing integrals are separately admitted. At every
sufficiently deep fixed interface, one error tending to zero with cusp
removal controls all positive onset, terminal and lower radial cutoffs at
arbitrary relative rates. The stated source-derived contacts are retained;
the outer region and identification with prescribed full temporal contacts
and the canonical QNM action remain separate. -/
theorem full_static_metric_collar_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∃ A0 : ℝ, 0 < A0 ∧ ∀ A : ℝ, A0 ≤ A →
        ∃ η : ℝ → ℝ, (∀ k, 0 ≤ η k) ∧ Tendsto η atTop (𝓝 0) ∧
          ∀ a B T k : ℝ, 0 < a → A ≤ B → 0 ≤ k → 4 ≤ Real.exp k →
            IntervalIntegrable (fun L => metricDifference q br amp w a (max a (T-L/2)) L k) volume A B ∧
            ‖fullStaticDifference q br amp w a A B T k‖ ≤ η k := by
  obtain ⟨G1,hG1,h1⟩ := static_metric_source_boundary_bound q br amp 1
  obtain ⟨G2,_,h2⟩ := static_metric_source_boundary_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1 ≤ w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1 ≤ w.re := by linarith [le_max_right G1 G2]
  have hwr : -2 < w.re := by linarith [le_max_left G1 G2]
  obtain ⟨C,L1,hC,hL1,hbound⟩ := h1 w hwi hw1
  obtain ⟨L2,hL2,hadmit⟩ := h2 w hwi hw2
  obtain ⟨β,hβ,_,hforce⟩ := static_forcing_uniform_restoration q br amp w hwi hwr
  have hsmall : ∀ᶠ L : ℝ in atTop,horizonCoordinate (-L/2)<β :=
    (horizon_depth_tendsto.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hβ)
  obtain ⟨D,hD⟩ := eventually_atTop.mp hsmall
  let A0 := max L1 (max L2 D)
  have hA0 : 0 < A0 := hL1.trans_le (le_max_left _ _)
  refine ⟨A0,hA0,?_⟩
  intro A hA
  have hAp : 0 < A := hA0.trans_le hA
  have hA1 : L1 ≤ A := (le_max_left _ _).trans hA
  have hA2 : L2 ≤ A := ((le_max_left L2 D).trans (le_max_right L1 (max L2 D))).trans hA
  have hAD : D ≤ A := ((le_max_right L2 D).trans (le_max_right L1 (max L2 D))).trans hA
  have hAr : -A/2 < 0 := by linarith
  obtain ⟨η,hη,hηlim,hηbound⟩ := hforce (-A/2) hAr (hD A hAD).le
  refine ⟨fun k => C*Real.exp (-k)+‖mu q*w‖*η k,
    fun k => add_nonneg (mul_nonneg hC (Real.exp_nonneg _)) (mul_nonneg (norm_nonneg _) (hη k)),?_,?_⟩
  · simpa only [mul_zero,zero_add] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).add (hηlim.const_mul ‖mu q*w‖)
  · intro a B T k ha hAB hk hk4
    have hIF := static_forcing_moment_integrable q br amp w a A B T k hAp hAB
    have hIS := hadmit a A B T k ha hA2 hAB hk hk4
    have hID : IntervalIntegrable (fun L => metricDifference q br amp w a (max a (T-L/2)) L k) volume A B := by
      simpa only [Pi.add_apply,sub_add_cancel] using hIS.add hIF
    refine ⟨hID,?_⟩
    have hsplit : fullStaticDifference q br amp w a A B T k=
        staticMetricDifference q br amp w a A B T k+
          mu q*w*(staticForcingCut q br amp w a (-B/2) (-A/2) T k-
            staticForcingCounterterm q br amp w a (-B/2) (-A/2) T k) := by
      unfold fullStaticDifference staticMetricDifference
      rw [intervalIntegral.integral_sub hID hIF,sub_div,
        static_forcing_moment_collar q br amp w a A B T k]
      ring
    rw [hsplit]
    apply (norm_add_le _ _).trans
    have hbnd : ‖staticMetricDifference q br amp w a A B T k‖ ≤ C*Real.exp (-k) := by
      simpa only [Nat.cast_one,neg_mul,one_mul] using hbound a A B T k ha hA1 hAB hk hk4
    rw [norm_mul]
    exact add_le_add hbnd (mul_le_mul_of_nonneg_left
      (hηbound a (-B/2) T k ha.le (by linarith)) (norm_nonneg _))

end
end RHTower.D4BMOriginalFullStaticCollar
