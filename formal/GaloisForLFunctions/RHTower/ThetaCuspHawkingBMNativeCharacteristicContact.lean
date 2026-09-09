import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleRiemannKernel
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
      fun p => (logCircle p.1 p.2 X k 1:ℂ)^2*
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
  change _=(Real.sinh d:ℂ)^2*laplaceMean q d X k at h
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

end
end RHTower.D4BMNativeCircle
