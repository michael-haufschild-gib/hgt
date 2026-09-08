import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic

/-! A fixed two-derivative right-boundary domain distinguishes nonintegral power branches. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- A genuine C² extension across the endpoint; the original function is tested only on the positive side. -/
def RightC2Extension (f : ℝ → ℂ) : Prop :=
  ∃ g : ℝ → ℂ, ContDiffAt ℝ 2 g 0 ∧ g =ᶠ[𝓝[>] (0:ℝ)] f

/-- Derivative germs on the open positive side preserve an eventual equality at its endpoint. -/
theorem rightGerm_deriv {f g : ℝ → ℂ} (h : f =ᶠ[𝓝[>] (0:ℝ)] g) :
    deriv f =ᶠ[𝓝[>] (0:ℝ)] deriv g := by
  have hd := h.derivWithin
  filter_upwards [hd,self_mem_nhdsWithin] with x hx hpos
  rwa [derivWithin_of_isOpen isOpen_Ioi hpos,derivWithin_of_isOpen isOpen_Ioi hpos] at hx

/-- The second derivative of a nonintegral power has its literal complex coefficient. -/
theorem ofReal_cpow_second (a : ℂ) (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y : ℝ => (y:ℂ)^a)) x = a*(a-1)*(x:ℂ)^(a-2) := by
  have hcut : (x:ℂ) ∈ Complex.slitPlane := by simp [Complex.mem_slitPlane_iff,hx]
  have hfirst (y : ℝ) (hy : 0 < y) : deriv (fun z : ℝ => (z:ℂ)^a) y = a*(y:ℂ)^(a-1) := by
    exact ((Complex.hasStrictDerivAt_cpow_const (c := a) (by simp [Complex.mem_slitPlane_iff,hy])).hasDerivAt.comp_ofReal).deriv
  have he : deriv (fun y : ℝ => (y:ℂ)^a) =ᶠ[𝓝 x] (fun y : ℝ => a*(y:ℂ)^(a-1)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hfirst y hy
  rw [he.deriv_eq]
  have hd := ((Complex.hasStrictDerivAt_cpow_const (c := a-1) hcut).hasDerivAt.comp_ofReal).const_mul a
  rw [hd.deriv,show a-1-1=a-2 by ring,mul_assoc]

/-- Below degree two, a power with neither constant nor linear exponent has no C² right extension. -/
theorem not_rightC2Extension_cpow (a : ℂ) (ha : a.re < 2) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ¬RightC2Extension (fun x : ℝ => (x:ℂ)^a) := by
  rintro ⟨g,hg,he⟩
  have hgg : ContinuousAt (deriv (deriv g)) 0 :=
    ((hg.derivWithin (m := 1) (by norm_num)).derivWithin (m := 0) (by norm_num)).continuousAt
  have hapos : 0 < (2-a).re := by norm_num; linarith
  have hane : 2-a ≠ 0 := by intro hh; have := congrArg Complex.re hh; simp at this; linarith
  have hp : Tendsto (fun x : ℝ => (x:ℂ)^(2-a)) (𝓝[>] 0) (𝓝 0) := by
    have hj : ContinuousAt (fun x : ℝ => ((x:ℂ),2-a)) 0 :=
      Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const
    have hc := (Complex.continuousAt_cpow_zero_of_re_pos hapos).comp_of_eq hj (by simp)
    simpa only [Function.comp_def,Complex.ofReal_zero,Complex.zero_cpow hane] using
      hc.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlim := (hgg.tendsto.mono_left nhdsWithin_le_nhds).mul hp
  have he2 := rightGerm_deriv (rightGerm_deriv he)
  have hconst : (fun x : ℝ => deriv (deriv g) x*(x:ℂ)^(2-a)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun _ => a*(a-1)) := by
    filter_upwards [he2,self_mem_nhdsWithin] with x hx hpos
    rw [hx,ofReal_cpow_second a x hpos,mul_assoc,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))]
    simp only [show a-2+(2-a)=0 by ring,Complex.cpow_zero,mul_one]
  have hh : a*(a-1) = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr' hconst.symm)
    (by simpa only [mul_zero] using hlim)
  exact (mul_ne_zero ha0 (sub_ne_zero.mpr ha1)) hh

/-- Multiplication by a nonvanishing C² factor cannot hide an inadmissible boundary power. -/
theorem not_rightC2Extension_cpow_mul (a : ℂ) (ha : a.re < 2) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (f : ℝ → ℂ) (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 ≠ 0) :
    ¬RightC2Extension (fun x : ℝ => (x:ℂ)^a*f x) := by
  rintro ⟨g,hg,he⟩
  apply not_rightC2Extension_cpow a ha ha0 ha1
  refine ⟨fun x => g x/f x,hg.mul (hf.inv hf0),?_⟩
  have hn : ∀ᶠ x in 𝓝[>] (0:ℝ), f x ≠ 0 :=
    (hf.continuousAt.eventually_ne hf0).filter_mono nhdsWithin_le_nhds
  filter_upwards [he,hn] with x hx hfx
  rw [hx,mul_div_cancel_right₀ _ hfx]

end
end GaloisForLFunctions.HTGeometry
