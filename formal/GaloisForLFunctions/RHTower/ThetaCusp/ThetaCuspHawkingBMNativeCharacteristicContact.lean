import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCircleRiemannKernel
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! The actual theta-source characteristic contact from the native radial Darboux equation. -/
namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private def laplaceMean (q : XiZeroCopy) (d X k : ℝ) : ℂ :=
  average (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle d theta X k))

private theorem laplace_circle_smooth (q : XiZeroCopy) (X k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k)) := by
  have hp (p : ℝ × ℝ) : 0 < logCircle p.1 p.2 X k 1 :=
    mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have he : (fun p : ℝ × ℝ => scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k))=
      fun p => (logCircle p.1 p.2 X k 1:ℂ)^(2 : ℕ)*
        (coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) (logCircle p.1 p.2 X k)+
         coordDeriv 1 (coordDeriv 1 (fullSquarePotential q)) (logCircle p.1 p.2 X k)) := by
    funext p
    exact scalarLaplacian_eq _ _ (hp p)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle p.1 p.2 X k) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ (hp p) n)
  have hj (i : Fin 2) : ContDiffAt ℝ ∞ (coordDeriv i (coordDeriv i (fullSquarePotential q)))
      (logCircle p.1 p.2 X k) :=
    coordDeriv_contDiffAt (m := ∞)
      (by simpa using coordDeriv_contDiffAt (m := ∞) (by simpa using hs) i) i
  have hc : ContDiffAt ℝ ∞ (fun r : ℝ × ℝ => logCircle r.1 r.2 X k) p := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
    all_goals fun_prop (disch := exact (denominator_pos _ _).ne')
  have hy : ContDiffAt ℝ ∞ (fun r : ℝ × ℝ => (logCircle r.1 r.2 X k 1:ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_pi.mp hc 1)
  exact (hy.pow 2).mul (((hj 0).comp p hc).add ((hj 1).comp p hc))

private theorem average_continuous {F : ℝ × ℝ → ℂ} (hf : Continuous F) (t : ℝ) :
    ContinuousAt (fun r => average (fun theta => F (r,theta))) t := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn F (Icc (t-1) (t+1) ×ˢ Icc 0 (2*Real.pi)))
  have hn : Ioo (t-1) (t+1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hs (r : ℝ) : Continuous (fun theta => F (r,theta)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have h := continuousAt_of_dominated
    (μ := volume.restrict (Ioc 0 (2*Real.pi))) (F := fun r theta => F (r,theta))
    (bound := fun _ => C)
    (Filter.Eventually.of_forall (fun r => (hs r).aestronglyMeasurable.restrict))
    (by filter_upwards [hn] with r hr
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
        exact hC (r,theta) ⟨⟨hr.1.le,hr.2.le⟩,⟨htheta.1.le,htheta.2⟩⟩)
    (integrable_const C)
    (by filter_upwards with theta
        exact (hf.comp (continuous_id.prodMk continuous_const)).continuousAt)
  exact h.const_mul (1/(2*Real.pi:ℂ))

private theorem laplaceMean_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (fun d => laplaceMean q d X k) :=
  continuous_iff_continuousAt.mpr (fun d => average_continuous (laplace_circle_smooth q X k).continuous d)

private theorem laplaceMean_zero (q : XiZeroCopy) (X k : ℝ) :
    laplaceMean q 0 X k=scalarLaplacian (fullSquarePotential q) ![X,Real.exp k] := by
  have he : (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle 0 theta X k))=
      fun _ => scalarLaplacian (fullSquarePotential q) ![X,Real.exp k] := by
    funext theta
    simp [logCircle,circle,offset,height,denominator]
  rw [laplaceMean,he]
  have hT : 0 ≤ 2*Real.pi := by positivity
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp [average]
  rw [← intervalIntegral.integral_of_le hT]
  simp only [intervalIntegral.integral_const,sub_zero,Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp [hpi]

private theorem regular_radial_equation (q : XiZeroCopy) (X k d : ℝ) (hd : d ≠ 0) :
    (Real.sinh d:ℂ)*deriv (deriv (fun r => mean q r X k)) d+
      (Real.cosh d:ℂ)*deriv (fun r => mean q r X k) d-
      (Real.sinh d:ℂ)*laplaceMean q d X k=0 := by
  have hn : (Real.sinh d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using hd)
  have h := mean_radial_action q d X k
  change _=(Real.sinh d:ℂ)^(2 : ℕ)*laplaceMean q d X k at h
  apply (mul_left_cancel₀ hn)
  linear_combination h

private theorem mean_first_zero (q : XiZeroCopy) (X k : ℝ) :
    deriv (fun r => mean q r X k) 0=0 := by
  have hs := mean_radial_smooth q X k
  have hs1 := (contDiff_infty_iff_deriv.mp hs).2
  have hs2 := (contDiff_infty_iff_deriv.mp hs1).2
  have hS : Continuous (fun d : ℝ => (Real.sinh d:ℂ)) := by fun_prop
  have hC : Continuous (fun d : ℝ => (Real.cosh d:ℂ)) := by fun_prop
  have hc := ((hS.mul hs2.continuous).add (hC.mul hs1.continuous)).sub
    (hS.mul (laplaceMean_continuous q X k))
  have he : (fun d => (Real.sinh d:ℂ)*deriv (deriv (fun r => mean q r X k)) d+
      (Real.cosh d:ℂ)*deriv (fun r => mean q r X k) d-
      (Real.sinh d:ℂ)*laplaceMean q d X k)=ᶠ[𝓝[≠] 0] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact regular_radial_equation q X k d hd
  have heq := tendsto_nhds_unique (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' he.symm)
  simpa using heq

private theorem sinh_ratio_limit {f : ℝ → ℂ} {a : ℂ} (hf : HasDerivAt f a 0) (h0 : f 0=0) :
    Tendsto (fun d => f d/(Real.sinh d:ℂ)) (𝓝[≠] 0) (𝓝 a) := by
  have h1 : Tendsto (fun d : ℝ => f d/(d:ℂ)) (𝓝[≠] 0) (𝓝 a) := by
    simpa only [zero_add,h0,sub_zero,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]
      using hf.tendsto_slope_zero
  have h2 : Tendsto (fun d : ℝ => (Real.sinh d:ℂ)/(d:ℂ)) (𝓝[≠] 0) (𝓝 (1:ℂ)) := by
    have h := ((Real.hasDerivAt_sinh 0).ofReal_comp).tendsto_slope_zero
    simpa only [Real.cosh_zero,Real.sinh_zero,Complex.ofReal_one,Complex.ofReal_zero,
      zero_add,sub_zero,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using h
  have h := h1.div h2 (by simp)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hn : (d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  change (f d/(d:ℂ))/((Real.sinh d:ℂ)/(d:ℂ))=f d/(Real.sinh d:ℂ)
  field_simp [hn]

/-- The second radial jet of the original circle mean is half its full source Laplacian. -/
theorem mean_second_at_zero (q : XiZeroCopy) (X k : ℝ) :
    deriv (deriv (fun r => mean q r X k)) 0=
      scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2 := by
  have hs1 := (contDiff_infty_iff_deriv.mp (mean_radial_smooth q X k)).2
  have hs2 := (contDiff_infty_iff_deriv.mp hs1).2
  have hm := ((hs1.contDiffAt (x := 0)).differentiableAt (by simp)).hasDerivAt
  have hr := sinh_ratio_limit hm (mean_first_zero q X k)
  have hC : Tendsto (fun d : ℝ => (Real.cosh d:ℂ)) (𝓝[≠] 0) (𝓝 (1:ℂ)) := by
    simpa using ((show Continuous (fun d : ℝ => (Real.cosh d:ℂ)) by fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto _ (𝓝[≠] (0:ℝ)) _)
  have hlim := (hs2.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add (hC.mul hr)
  have he : (fun d => deriv (deriv (fun r => mean q r X k)) d+
      (Real.cosh d:ℂ)*(deriv (fun r => mean q r X k) d/(Real.sinh d:ℂ)))=ᶠ[𝓝[≠] 0]
      fun d => laplaceMean q d X k := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hn : (Real.sinh d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using hd)
    have h := regular_radial_equation q X k d hd
    apply (mul_left_cancel₀ hn)
    field_simp [hn]
    linear_combination h
  have hh := tendsto_nhds_unique (hlim.congr' he)
    ((laplaceMean_continuous q X k).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [laplaceMean_zero] at hh
  linear_combination hh/2

private theorem angular_first_derivative (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    HasDerivAt (fun a => angularKernel q a X k) (argumentFirst q z X k) z := by
  have hm := (((mean_radial_smooth q X k).contDiffAt (x := Real.arcosh z)).differentiableAt
    (by simp)).hasDerivAt
  have hd : HasDerivAt Real.arcosh (1/Real.sinh (Real.arcosh z)) z := by
    simpa only [one_div,Real.sinh_arcosh hz.le] using Real.hasDerivAt_arcosh hz
  apply (hm.scomp z hd).congr_deriv
  simp only [argumentFirst,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one]
  ring

/-- The actual interior first derivative tends to half the complete theta-source Laplacian. -/
theorem argumentFirst_tendsto_characteristic (q : XiZeroCopy) (X k : ℝ) :
    Tendsto (fun z => argumentFirst q z X k) (𝓝[>] 1)
      (𝓝 (scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)) := by
  have hs1 := (contDiff_infty_iff_deriv.mp (mean_radial_smooth q X k)).2
  have hm := ((hs1.contDiffAt (x := 0)).differentiableAt (by simp)).hasDerivAt
  have hl := sinh_ratio_limit hm (mean_first_zero q X k)
  rw [mean_second_at_zero] at hl
  have ha : Tendsto Real.arcosh (𝓝[>] 1) (𝓝 (0:ℝ)) := by
    simpa only [ContinuousWithinAt,Real.arcosh_zero] using
      ((Real.continuousOn_arcosh 1 (by simp)).mono Ioi_subset_Ici_self)
  have har : Tendsto Real.arcosh (𝓝[>] 1) (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within Real.arcosh ha
      (by filter_upwards [self_mem_nhdsWithin] with z hz
          exact (Real.arcosh_pos hz).ne')
  exact hl.comp har

/-- The native full-source angular kernel has the required right characteristic contact.
The derivative is within the physical chart; no extension below one is used. -/
theorem angularKernel_right_derivative (q : XiZeroCopy) (X k : ℝ) :
    HasDerivWithinAt (fun z => angularKernel q z X k)
      (scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2) (Ici 1) 1 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 1)
  · intro z hz
    exact (angular_first_derivative q X k hz).differentiableAt.differentiableWithinAt
  · exact ((mean_radial_smooth q X k).continuous.continuousAt.comp_continuousWithinAt
      ((Real.continuousOn_arcosh 1 (by simp)).mono Ioi_subset_Ici_self))
  · exact self_mem_nhdsWithin
  · apply (argumentFirst_tendsto_characteristic q X k).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (angular_first_derivative q X k hz).deriv.symm


set_option maxHeartbeats 600000

private theorem argumentFirst_derivative (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    HasDerivAt (fun y => argumentFirst q y X k) (argumentSecond q z X k) z := by
  have hs1 := (contDiff_infty_iff_deriv.mp (mean_radial_smooth q X k)).2
  have hm1 := ((hs1.contDiffAt (x := Real.arcosh z)).differentiableAt (by simp)).hasDerivAt
  have hd : HasDerivAt Real.arcosh (1/Real.sinh (Real.arcosh z)) z := by
    simpa only [one_div,Real.sinh_arcosh hz.le] using Real.hasDerivAt_arcosh hz
  have hn : (Real.sinh (Real.arcosh z):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr (Real.arcosh_pos hz)).ne'
  have hr := ((Real.hasDerivAt_sinh (Real.arcosh z)).comp z hd).ofReal_comp
  apply ((hm1.scomp z hd).div hr hn).congr_deriv
  dsimp [argumentSecond]
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one]
  field_simp [hn]

private theorem angularAction_equation (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    ((z:ℂ)^(2 : ℕ)-1)*argumentSecond q z X k+2*(z:ℂ)*argumentFirst q z X k=
      angularAction q z X k := by
  have hn : (Real.sinh (Real.arcosh z):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr (Real.arcosh_pos hz)).ne'
  have he : (z:ℂ)^(2 : ℕ)-1=(Real.sinh (Real.arcosh z):ℂ)^(2 : ℕ) := by
    have h := Real.cosh_sq_sub_sinh_sq (Real.arcosh z)
    rw [Real.cosh_arcosh hz.le] at h
    exact_mod_cast (by linarith : z^(2 : ℕ)-1=Real.sinh (Real.arcosh z)^(2 : ℕ))
  have h := mean_darboux q (Real.arcosh z) X k
  change _ = (Real.sinh (Real.arcosh z):ℂ)^(2 : ℕ)*angularAction q z X k at h
  rw [Real.cosh_arcosh hz.le] at h
  rw [he]
  dsimp [argumentSecond,argumentFirst]
  rw [Real.cosh_arcosh hz.le]
  linear_combination (norm := (field_simp [hn]; ring)) h/(Real.sinh (Real.arcosh z):ℂ)^(2 : ℕ)

private theorem angularAction_eq_mean (q : XiZeroCopy) (z X k : ℝ) :
    angularAction q z X k=laplaceMean q (Real.arcosh z) X k := by
  exact mean_laplacian_commutes q (Real.arcosh z) X k

private theorem angularAction_continuousOn (q : XiZeroCopy) (X k : ℝ) :
    ContinuousOn (fun z => angularAction q z X k) (Ici 1) := by
  simpa only [angularAction_eq_mean,Function.comp_def] using!
    (laplaceMean_continuous q X k).comp_continuousOn Real.continuousOn_arcosh

private def radialCurrent (q : XiZeroCopy) (X k z : ℝ) : ℂ :=
  ((z:ℂ)^(2 : ℕ)-1)*argumentFirst q z X k

private theorem radialCurrent_derivative (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    HasDerivAt (radialCurrent q X k) (angularAction q z X k) z := by
  have h := (((hasDerivAt_id z).ofReal_comp.pow 2).sub_const 1).mul
    (argumentFirst_derivative q X k hz)
  apply h.congr_deriv
  rw [← angularAction_equation q X k hz]
  simp only [id_eq,Pi.pow_apply,Complex.ofReal_one,mul_one]
  ring

/-- The original weighted native derivative is the integral of the full angular action.
The characteristic face contributes zero by the actual source contact. -/
theorem angularCurrent_integral (q : XiZeroCopy) (X k : ℝ) (z : Ici (1:ℝ)) :
    ((z.val:ℂ)^(2 : ℕ)-1)*argumentFirst q z X k=
      ∫ r in (1:ℝ)..z.val, angularAction q r X k := by
  rcases eq_or_lt_of_le (show (1:ℝ) ≤ z.val from z.property) with h0 | hz
  · simp [← h0]
  have hc := angularAction_continuousOn q X k
  have hi : IntervalIntegrable (fun r => angularAction q r X k) volume 1 z.val :=
    (hc.mono (Icc_subset_Ici_self)).intervalIntegrable_of_Icc hz.le
  have hl : Tendsto (radialCurrent q X k) (𝓝[>] 1) (𝓝 0) := by
    have hp : Tendsto (fun r : ℝ => (r:ℂ)^(2 : ℕ)-1) (𝓝[>] 1) (𝓝 (0:ℂ)) := by
      have h := ((show Continuous (fun r : ℝ => (r:ℂ)^(2 : ℕ)-1) by fun_prop).continuousAt
        (x := (1:ℝ))).tendsto.mono_left
          (show 𝓝[>] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
      simpa using h
    simpa only [radialCurrent,zero_mul] using! hp.mul (argumentFirst_tendsto_characteristic q X k)
  have hr := (radialCurrent_derivative q X k hz).continuousAt.tendsto.mono_left
    (show 𝓝[<] z.val ≤ 𝓝 z.val from nhdsWithin_le_nhds)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hz
    (fun r hr => radialCurrent_derivative q X k hr.1) hi hl hr
  simpa only [sub_zero,radialCurrent] using h.symm

/-- Nonsingular full-source derivative on the closed physical invariant chart. -/
def characteristicFirst (q : XiZeroCopy) (z X k : ℝ) : ℂ :=
  (∫ t in (0:ℝ)..1, angularAction q (1+t*(z-1)) X k)/(z+1:ℂ)

/-- The actual interior derivative equals its nonsingular original-source integral. -/
theorem argumentFirst_volterra (q : XiZeroCopy) (X k : ℝ) (z : Ioi (1:ℝ)) :
    argumentFirst q z X k=characteristicFirst q z X k := by
  have hz : (1:ℝ) < z.val := z.property
  have h := angularCurrent_integral q X k ⟨z.val,hz.le⟩
  have hs := intervalIntegral.smul_integral_comp_add_mul
    (fun r => angularAction q r X k) (a := 0) (b := 1) (z.val-1) 1
  simp only [mul_zero,add_zero,mul_one,Complex.real_smul] at hs
  have hn : (z.val:ℂ)-1 ≠ 0 := by exact_mod_cast (sub_pos.mpr hz).ne'
  have hn1 : (z.val+1:ℂ) ≠ 0 := by
    exact_mod_cast (show z.val+1 ≠ 0 by linarith)
  change argumentFirst q z.val X k = _
  unfold characteristicFirst
  apply (eq_div_iff hn1).mpr
  apply (mul_left_cancel₀ hn)
  have hzcast : ((z.val-1:ℝ):ℂ)=(z.val:ℂ)-1 := by push_cast; rfl
  rw [hzcast] at hs
  have hs' : ((z.val:ℂ)-1)*(∫ t in (0:ℝ)..1,
      angularAction q (1+t*(z.val-1)) X k)=∫ r in (1:ℝ)..z.val, angularAction q r X k := by
    simpa only [mul_comm,add_sub_cancel] using hs
  linear_combination h-hs' 

private def closedAction (q : XiZeroCopy) (X k z : ℝ) : ℂ :=
  angularAction q (max 1 z) X k

private theorem closedAction_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (closedAction q X k) :=
  (angularAction_continuousOn q X k).comp_continuous
    (continuous_const.max continuous_id) (fun z => (show max 1 z ∈ Ici (1:ℝ) from le_max_left 1 z))

/-- The actual derivative integral is continuous through the characteristic. -/
theorem characteristicFirst_continuousOn (q : XiZeroCopy) (X k : ℝ) :
    ContinuousOn (fun z => characteristicFirst q z X k) (Ici 1) := by
  have hc : Continuous (fun p : ℝ × ℝ => closedAction q X k (1+p.2*(p.1-1))) :=
    (closedAction_continuous q X k).comp (by fun_prop)
  have hi : Continuous (fun z => ∫ t in (0:ℝ)..1, closedAction q X k (1+t*(z-1))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun z t => closedAction q X k (1+t*(z-1))) hc continuous_const
  have he : EqOn (fun z => characteristicFirst q z X k)
      (fun z => (∫ t in (0:ℝ)..1, closedAction q X k (1+t*(z-1)))/(z+1:ℂ)) (Ici 1) := by
    intro z hz
    unfold characteristicFirst
    apply congrArg (fun v : ℂ => v/(z+1:ℂ))
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := (show t ∈ Icc (0:ℝ) 1 by simpa using ht).1
    have hz0 : 1 ≤ z := hz
    have hh : 1 ≤ 1+t*(z-1) := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hz0)]
    simp only [closedAction,max_eq_right hh]
  apply (hi.continuousOn.div (by fun_prop) ?_).congr he
  intro z hz
  have hz0 : 1 ≤ z := hz
  exact_mod_cast (by linarith : z+1 ≠ 0)

/-- The closed integral retains the complete characteristic source Laplacian. -/
theorem characteristicFirst_at_one (q : XiZeroCopy) (X k : ℝ) :
    characteristicFirst q 1 X k=scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2 := by
  simp only [characteristicFirst,sub_self,mul_zero,add_zero,angularAction_eq_mean,
    Real.arcosh_zero,laplaceMean_zero,intervalIntegral.integral_const,sub_zero,
    one_smul,Complex.ofReal_one]
  norm_num

/-- The source integral is the actual derivative throughout the closed physical chart. -/
theorem angularKernel_closed_derivative (q : XiZeroCopy) (X k : ℝ) (z : Ici (1:ℝ)) :
    HasDerivWithinAt (fun r => angularKernel q r X k)
      (characteristicFirst q z X k) (Ici 1) z.val := by
  rcases eq_or_lt_of_le (show (1:ℝ) ≤ z.val from z.property) with h0 | hz
  · simpa only [← h0,characteristicFirst_at_one] using angularKernel_right_derivative q X k
  · rw [← argumentFirst_volterra q X k ⟨z.val,hz⟩]
    exact (angular_first_derivative q X k hz).hasDerivWithinAt

/-- The full native kernel is reconstructed from its original source and admitted derivative. -/
theorem angularKernel_source_integral (q : XiZeroCopy) (X k : ℝ) (z : Ici (1:ℝ)) :
    angularKernel q z X k=fullSquarePotential q ![X,Real.exp k]+
      ∫ r in (1:ℝ)..z.val, characteristicFirst q r X k := by
  have hc : ContinuousOn (fun r => angularKernel q r X k) (Ici 1) :=
    (mean_radial_smooth q X k).continuous.comp_continuousOn Real.continuousOn_arcosh
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le z.property
    (hc.mono Icc_subset_Ici_self)
    (fun r hr => by
      rw [← argumentFirst_volterra q X k ⟨r,hr.1⟩]
      exact angular_first_derivative q X k hr.1)
    (((characteristicFirst_continuousOn q X k).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc z.property)
  simpa only [angularKernel,Real.arcosh_zero,mean_zero,add_comm] using (eq_add_of_sub_eq h.symm)

end
end RHTower.D4BMNativeCircle
