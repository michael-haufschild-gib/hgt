import GaloisForLFunctions.RHTower.XiGaussianHeatWindowNyquistExclusion
import GaloisForLFunctions.RHTower.EvenSectorSmoothSourceScalarization
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Smooth pole-free approximation with a fixed arithmetic support

Even mollification preserves the pole zero. Its whole arithmetic trace has
one fixed finite support, each coordinate converges, and its actual energy
converges. The fixed support is what permits exact finite trace correction.
-/

open Complex MeasureTheory Filter Topology Set Finsupp Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided

theorem smooth_of_contDiff_infty {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 2 f :=
  hf.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

theorem mollify_compact (f : WeilTestFn) (n : ℕ) :
    HasCompactSupport (mollify (invSucc_pos n) f.1) :=
  (hasCompactSupport_bumpC _).convolution _ f.2.2

/-- Smooth even-polar approximants of an actual even-polar source. -/
def polarSmooth (f : WeilEvenPolarTestFn) (n : ℕ) : SmoothEvenPolarTestFn :=
  ⟨⟨⟨mollify (invSucc_pos n) f.1.1,
    smooth_of_contDiff_infty (contDiff_mollify _ f.1.2.1.continuous),
    mollify_compact f.1 n⟩,mollify_neg _ f.2.1,by
      rw [paperFT_mollify _ f.1.2.1.continuous f.1.2.2,f.2.2,mul_zero]⟩,
    contDiff_mollify _ f.1.2.1.continuous⟩

theorem norm_mollify_le {f : ℝ → ℂ} {M : ℝ}
    (hb : ∀ x,‖f x‖ ≤ M) (n : ℕ) (x : ℝ) :
    ‖mollify (invSucc_pos n) f x‖ ≤ M := by
  rw [mollify_apply]
  have hi := ((evenBump (invSucc_pos n)).integrable_normed (μ := volume)).mul_const M
  have hh := norm_integral_le_of_norm_le
    (f := fun t => bumpC (invSucc_pos n) t * f (x-t)) hi (Eventually.of_forall fun t => by
    rw [norm_mul,bumpC,Complex.norm_real,Real.norm_of_nonneg
      ((evenBump (invSucc_pos n)).nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (hb _) ((evenBump (invSucc_pos n)).nonneg_normed t))
  simpa only [integral_mul_const,(evenBump (invSucc_pos n)).integral_normed,one_mul] using hh

theorem tendsto_mollify_pointwise {f : ℝ → ℂ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun n => mollify (invSucc_pos n) f x) atTop (𝓝 (f x)) := by
  have hh := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (φ := fun n => evenBump (invSucc_pos n))
    tendsto_one_div_add_atTop_nhds_zero_nat hf x
  convert hh using 1
  funext n
  rw [mollify_apply,convolution_def]
  rfl

theorem mollify_support_common (f : WeilTestFn) :
    ∃ A : ℝ,0 ≤ A ∧ tsupport f.1 ⊆ Icc (-A) A ∧
      ∀ n,tsupport (mollify (invSucc_pos n) f.1) ⊆ Icc (-A) A := by
  obtain ⟨a,ha⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
  have hfs : tsupport f.1 ⊆ Icc (-|a|) |a| := by
    intro x hx
    have hh := ha hx
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
    exact abs_le.mp (hh.trans (le_abs_self a))
  refine ⟨|a|+1,by positivity,?_,fun n x hx => ?_⟩
  · intro x hx
    obtain ⟨h₁,h₂⟩ := hfs hx
    constructor <;> linarith
  · have hh := tsupport_mollify_subset (invSucc_pos n) hfs hx
    have hr : 1/((n : ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    constructor <;> linarith [hh.1,hh.2]

theorem tendsto_weilTest_mollify (f : WeilTestFn) (x : ℝ) :
    Tendsto (fun n => EF.weilTest (mollify (invSucc_pos n) f.1)
      (mollify (invSucc_pos n) f.1) x) atTop (𝓝 (EF.weilTest f.1 f.1 x)) := by
  obtain ⟨A,hA,_,hs⟩ := mollify_support_common f
  obtain ⟨M,hM⟩ := f.2.2.exists_bound_of_continuous f.2.1.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (f.1 0)).trans (hM 0)
  let B : ℝ → ℝ := (Icc (-A) A).indicator (fun _ => M^2)
  have hBi : Integrable B :=
    (integrableOn_const (s := Icc (-A) A) isCompact_Icc.measure_ne_top).integrable_indicator
      measurableSet_Icc
  unfold EF.weilTest
  simp only [convolution_def,ContinuousLinearMap.mul_apply',EF.tilde]
  apply tendsto_integral_of_dominated_convergence B
  · intro n
    exact ((contDiff_mollify _ f.2.1.continuous).continuous.mul
      (Complex.continuous_conj.comp ((contDiff_mollify _ f.2.1.continuous).continuous.comp
        (by fun_prop)))).aestronglyMeasurable
  · exact hBi
  · intro n
    filter_upwards with t
    change ‖mollify (invSucc_pos n) f.1 t * conj
      (mollify (invSucc_pos n) f.1 (-(x-t)))‖ ≤ B t
    by_cases ht : t ∈ Icc (-A) A
    · rw [show B t=M^2 by simp [B,ht],norm_mul,Complex.norm_conj,pow_two]
      exact mul_le_mul (norm_mollify_le hM n t) (norm_mollify_le hM n _)
        (norm_nonneg _) hM0
    · have hz : mollify (invSucc_pos n) f.1 t=0 :=
        image_eq_zero_of_notMem_tsupport (fun hh => ht (hs n hh))
      rw [hz,zero_mul,norm_zero]
      simp only [B,Set.indicator_of_notMem ht,le_refl]
  · filter_upwards with t
    exact (tendsto_mollify_pointwise f.2.1.continuous t).mul
      (Complex.continuous_conj.tendsto _ |>.comp
        (tendsto_mollify_pointwise f.2.1.continuous (-(x-t))))

theorem tendsto_logValue_mollify (f : WeilTestFn) (j : ℕ) :
    Tendsto (fun n => logValue (mollify (invSucc_pos n) f.1) j)
      atTop (𝓝 (logValue f.1 j)) := by
  exact ((Complex.continuous_re.tendsto _).comp
    ((tendsto_weilTest_mollify f _).add (tendsto_weilTest_mollify f _))).div_const _

theorem logValue_eq_zero_of_support {f : ℝ → ℂ} {A : ℝ}
    (hs : tsupport f ⊆ Icc (-A) A) {j : ℕ} (hj : ⌈Real.exp (A+A)⌉₊ < j) :
    logValue f j=0 := by
  have hb (u : ℝ) (hu : f u≠0) : |u|≤A := abs_le.mpr (hs (subset_tsupport _ hu))
  have hk := weilTest_support_abs_le hb hb
  have hje : Real.exp (A+A)<j := Nat.lt_of_ceil_lt hj
  have hjp : (0 : ℝ)<j := (Real.exp_pos _).trans hje
  have hlog : A+A<Real.log j := (Real.lt_log_iff_exp_lt hjp).mpr hje
  have hp : EF.weilTest f f (Real.log j)=0 := by
    by_contra hh
    linarith [hk _ hh,le_abs_self (Real.log j)]
  have hm : EF.weilTest f f (-Real.log j)=0 := by
    by_contra hh
    have hx := hk _ hh
    rw [abs_neg] at hx
    linarith [le_abs_self (Real.log j)]
  simp [logValue,hp,hm]

/-- One finite coordinate set contains every smoothed trace and its limit. -/
theorem polarSmooth_common_trace_support (f : WeilEvenPolarTestFn) :
    ∃ s : Finset LogIndex,(logVector f.1).support ⊆ s ∧
      ∀ n,(logVector (polarSmooth f n).1.1).support ⊆ s := by
  classical
  obtain ⟨A,_,hf,hs⟩ := mollify_support_common f.1
  let N := ⌈Real.exp (A+A)⌉₊
  refine ⟨(Finset.range (N+1)).subtype (fun j => 2≤j),?_,?_⟩
  · intro j hj
    rw [Finset.mem_subtype,Finset.mem_range]
    by_contra hh
    have hz := logValue_eq_zero_of_support hf (j := j.1) (by omega)
    exact (Finsupp.mem_support_iff.mp hj) (by simpa only [logVector_apply] using hz)
  · intro n j hj
    rw [Finset.mem_subtype,Finset.mem_range]
    by_contra hh
    have hz := logValue_eq_zero_of_support (hs n) (j := j.1) (by omega)
    exact (Finsupp.mem_support_iff.mp hj) (by simpa only [logVector_apply,polarSmooth] using hz)

theorem polarSmooth_trace_tendsto (f : WeilEvenPolarTestFn) (j : LogIndex) :
    Tendsto (fun n => logVector (polarSmooth f n).1.1 j) atTop (𝓝 (logVector f.1 j)) :=
  tendsto_logValue_mollify f.1 j

theorem polarSmooth_pairing_tendsto (f : WeilEvenPolarTestFn) (b : LogIndex → ℝ) :
    Tendsto (fun n => linearCombination ℝ b (logVector (polarSmooth f n).1.1))
      atTop (𝓝 (linearCombination ℝ b (logVector f.1))) := by
  classical
  obtain ⟨s,hf,hs⟩ := polarSmooth_common_trace_support f
  have heq (v : LogIndex →₀ ℝ) (hv : v.support ⊆ s) :
      linearCombination ℝ b v=∑ j ∈ s,v j*b j := by
    rw [linearCombination_apply]
    exact Finsupp.sum_of_support_subset v hv (fun j r => r*b j) (fun _ _ => zero_mul _)
  simp_rw [heq _ (hs _),heq _ hf]
  exact tendsto_finsetSum s fun j _ => (polarSmooth_trace_tendsto f j).mul_const _

/-- Actual pole-plus-archimedean energy converges, using the unconditional
explicit formula and the common finite arithmetic support. -/
theorem polarSmooth_energy_tendsto (f : WeilEvenPolarTestFn) :
    Tendsto (fun n => weilArchRe (EF.weilTest (polarSmooth f n).1.1.1
      (polarSmooth f n).1.1.1)) atTop (𝓝 (weilArchRe (EF.weilTest f.1.1 f.1.1))) := by
  have heq (g : WeilTestFn) : weilArchRe (EF.weilTest g.1 g.1)=
      (zetaZeroConfig.W g.1 g.1).re+
        linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt j : ℝ))
          (logVector g) := by
    rw [zeta_W_eq_weilFullFunctional g.2.1 g.2.2,re_weilFullFunctional_eq]
    ring
  simp_rw [heq]
  exact ((Complex.continuous_re.tendsto _).comp
    (tendsto_W_mollify f.1.2.1 f.1.2.2)).add (polarSmooth_pairing_tendsto f _)

end RHTower.EvenSector
