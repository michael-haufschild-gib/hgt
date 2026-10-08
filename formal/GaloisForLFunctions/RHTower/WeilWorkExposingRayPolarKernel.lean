import GaloisForLFunctions.RHTower.WeilWorkExposingRayLogKernel
import GaloisForLFunctions.RHTower.ZetaWeilFiniteLevelInertia

/-!
# Actual polar packet kernels at logarithmic spectral cost

Finite real translate packets give the exact quadratic form of the
weighted separator kernel. Polar profiles remain polar under every
such packet. Real symmetry then upgrades positivity to every complex
finite vector. No full-cone positivity or kernel positivity is assumed.
Paper: CRITICAL-ONE-POLE-PROOF.md, section4.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral WeilOneSided

/-- A finite real translate packet of an actual compact C2 source. -/
def realTranslateTest {N : ℕ} (f : WeilTestFn) (x c : Fin N → ℝ) : WeilTestFn :=
  ⟨∑ j, (c j : ℂ) • transl (x j) f.1, by
    constructor
    · have he : (∑ j, (c j : ℂ) • transl (x j) f.1) =
          (fun u => ∑ j, (c j : ℂ)*f.1 (u-x j)) := by
        funext u
        simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,transl]
      rw [he]
      exact ContDiff.sum fun j _ => contDiff_const.mul
        (f.2.1.comp (contDiff_id.sub contDiff_const))
    · exact HasCompactSupport.finset_sum fun j _ =>
        (f.2.2.comp_homeomorph (Homeomorph.subRight (x j))).smul_left⟩

theorem paperFT_realTranslateTest {N : ℕ} (f : WeilTestFn) (x c : Fin N → ℝ) (z : ℂ) :
    paperFT (realTranslateTest f x c).1 z =
      paperFT f.1 z * ∑ j, (c j : ℂ)*Complex.exp (I*z*x j) := by
  have he : (realTranslateTest f x c).1 =
      (fun u => ∑ j, (c j : ℂ)*transl (x j) f.1 u) := by
    funext u
    simp only [realTranslateTest,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he,paperFT_finset_sum (f := fun j => transl (x j) f.1)
    Finset.univ (fun j => (c j : ℂ))
    (fun j => f.2.1.continuous.comp (continuous_id.sub continuous_const))
    (fun j => f.2.2.comp_homeomorph (Homeomorph.subRight (x j)))]
  simp only [paperFT_transl]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem normSq_real_exp_sum {N : ℕ} (x c : Fin N → ℝ) (τ : ℝ) :
    ‖∑ j, (c j : ℂ)*Complex.exp (I*(τ : ℂ)*x j)‖^2 =
      ∑ i, ∑ j, c i*c j*Real.cos ((x j-x i)*τ) := by
  have hre : (∑ j, (c j : ℂ)*Complex.exp (I*(τ : ℂ)*x j)).re =
      ∑ j, c j*Real.cos (x j*τ) := by
    simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,mul_zero,sub_zero,Complex.exp_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      one_mul,zero_add,Real.exp_zero]
    congr 1
    ext j
    rw [mul_comm τ (x j)]
  have him : (∑ j, (c j : ℂ)*Complex.exp (I*(τ : ℂ)*x j)).im =
      ∑ j, c j*Real.sin (x j*τ) := by
    simp only [Complex.im_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,Complex.exp_im,
      Complex.I_re,Complex.I_im,one_mul,zero_add,Real.exp_zero]
    congr 1
    ext j
    rw [mul_comm τ (x j)]
  rw [Complex.sq_norm,Complex.normSq_apply,hre,him]
  simp_rw [sub_mul,Real.cos_sub]
  rw [Finset.sum_mul,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact spectral quadratic form of a finite real translate packet. -/
theorem normSq_paperFT_realTranslateTest {N : ℕ} (f : WeilTestFn)
    (x c : Fin N → ℝ) (τ : ℝ) :
    ‖paperFT (realTranslateTest f x c).1 τ‖^2 =
      ∑ i, ∑ j, (c i*c j)*(‖paperFT f.1 τ‖^2*Real.cos ((x j-x i)*τ)) := by
  rw [paperFT_realTranslateTest,norm_mul,mul_pow,normSq_real_exp_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem toL1_finsetSum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i, Integrable (F i)) :
    (integrable_finsetSum' s (fun i _ => hF i)).toL1 (∑ i ∈ s, F i) =
      ∑ i ∈ s, (hF i).toL1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Integrable.toL1_add (F a) (∑ i ∈ s, F i) (hF a)
      (integrable_finsetSum' s (fun i _ => hF i))]
    exact congrArg ((hF a).toL1 (F a) + ·) ih

private theorem integrable_packet_cos {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) (x : ℝ) :
    Integrable (fun τ : ℝ =>
      (‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*Real.cos (x*τ)) := by
  apply (integrable_logWeighted_density hβ hβ1 f).mul_bdd
    (show Continuous (fun τ : ℝ => Real.cos (x*τ)) by fun_prop).aestronglyMeasurable
  filter_upwards [] with τ
  simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (x*τ)

/-- Weighted L1 packet expansion; the real functional is applied only after
this equality in its actual normed domain has been established. -/
theorem logDensityL1_realTranslateTest {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {N : ℕ} (f : WeilTestFn) (x c : Fin N → ℝ) :
    logDensityL1 hβ hβ1 (realTranslateTest f x c) =
      ∑ i, ∑ j, (c i*c j) • logCosDensityL1 hβ hβ1 f (x j-x i) := by
  let F : Fin N → Fin N → ℝ → ℝ := fun i j τ =>
    (c i*c j)*((‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*Real.cos ((x j-x i)*τ))
  have hi (i j : Fin N) : Integrable (F i j) :=
    (integrable_packet_cos hβ hβ1 f (x j-x i)).const_mul (c i*c j)
  have he (i j : Fin N) : (hi i j).toL1 (F i j) =
      (c i*c j) • logCosDensityL1 hβ hβ1 f (x j-x i) := by
    unfold logCosDensityL1
    exact Integrable.toL1_smul
      (fun τ : ℝ => (‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*
        Real.cos ((x j-x i)*τ)) _ (c i*c j)
  have hs (i : Fin N) : Integrable (∑ j, F i j) :=
    integrable_finsetSum' _ (fun j _ => hi i j)
  have heq : logDensityL1 hβ hβ1 (realTranslateTest f x c) =
      (integrable_finsetSum' _ (fun i _ => hs i)).toL1 (∑ i, ∑ j, F i j) := by
    apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
    filter_upwards [] with τ
    simp only [Finset.sum_apply]
    rw [normSq_paperFT_realTranslateTest,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [F]
    ring
  rw [heq,toL1_finsetSum Finset.univ (fun i => ∑ j, F i j) hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [toL1_finsetSum Finset.univ (F i) (hi i)]
  exact Finset.sum_congr rfl fun j _ => he i j

/-- Exact arithmetic quadratic form of a finite real translate packet. -/
theorem atomValue_realTranslateTest {N : ℕ} (b : ℕ → ℝ) (f : WeilTestFn)
    (x c : Fin N → ℝ) :
    -atomValue b (realTranslateTest f x c).1 =
      ∑ i, ∑ j, (c i*c j)*
        (((atomicKernel b 0 f.1 (x j-x i)).re+
          (atomicKernel b 0 f.1 (-(x j-x i))).re)/2) := by
  have ha := congrArg Complex.re (atomicForm_packet b 0 f.2.1.continuous f.2.2
    x (fun j => (c j : ℂ)))
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,neg_zero,mul_zero,zero_mul,
    sub_zero] at ha
  have hswap : (∑ i, ∑ j, c i*(atomicKernel b 0 f.1 (x j-x i)).re*c j) =
      ∑ i, ∑ j, c i*(atomicKernel b 0 f.1 (-(x j-x i))).re*c j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show -(x j-x i)=x i-x j by ring]
    ring
  change -(-(atomicForm b 0 (EF.weilTest _ _)).re) = _
  change -(-(atomicForm b 0 (EF.weilTest
    (∑ j, (c j : ℂ) • transl (x j) f.1)
    (∑ j, (c j : ℂ) • transl (x j) f.1))).re) = _
  rw [neg_neg,ha]
  calc
    _ = ((∑ i, ∑ j, c i*(atomicKernel b 0 f.1 (x j-x i)).re*c j)+
      ∑ i, ∑ j, c i*(atomicKernel b 0 f.1 (-(x j-x i))).re*c j)/2 := by rw [← hswap]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Exact real Gram identity for the ACTUAL weighted separator. -/
theorem logSeparatorKernel_packet {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (b : ℕ → ℝ) (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ)
    {N : ℕ} (f : WeilTestFn) (x c : Fin N → ℝ) :
    ell (logDensityL1 hβ hβ1 (realTranslateTest f x c))-
      atomValue b (realTranslateTest f x c).1 =
      ∑ i, ∑ j, (c i*c j)*logSeparatorKernel hβ hβ1 b ell f (x j-x i) := by
  rw [logDensityL1_realTranslateTest]
  simp only [map_sum,map_smul,smul_eq_mul]
  rw [sub_eq_add_neg,atomValue_realTranslateTest,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold logSeparatorKernel
  ring

/-- Every finite real translate packet of a polar profile is polar. -/
theorem isPolarTest_realTranslateTest {N : ℕ} (f : WeilTestFn) (x c : Fin N → ℝ)
    (hf : ∃ a, IsPolarTest a f.1) : ∃ A, IsPolarTest A (realTranslateTest f x c).1 := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨A,hA⟩ := exists_abs_bound_of_hasCompactSupport (realTranslateTest f x c).2.2
  refine ⟨|A|,abs_nonneg _,(realTranslateTest f x c).2.1,?_,?_,?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro u hu
    exact abs_le.mp ((hA u hu).trans (le_abs_self A))
  · rw [paperFT_realTranslateTest,ha.2.2.2.1,zero_mul]
  · rw [paperFT_realTranslateTest,ha.2.2.2.2,zero_mul]

private theorem positiveDefinite_of_real_even {k : ℝ → ℝ}
    (heven : ∀ y, k (-y)=k y)
    (hpos : ∀ (N : ℕ) (x c : Fin N → ℝ), 0 ≤ ∑ i, ∑ j, (c i*c j)*k (x j-x i)) :
    GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal (fun y => (k y : ℂ)) := by
  intro N x c
  let R : ℝ := (∑ i, ∑ j, ((c i).re*(c j).re)*k (x j-x i))+
    ∑ i, ∑ j, ((c i).im*(c j).im)*k (x j-x i)
  refine ⟨R,add_nonneg (hpos N x (fun i => (c i).re))
    (hpos N x (fun i => (c i).im)),?_⟩
  apply Complex.ext
  · simp only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.star_def,
      Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero]
    dsimp [R]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [Complex.im_sum,Complex.mul_re,Complex.mul_im,Complex.star_def,
      Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero]
    have hswap : (∑ i, ∑ j, (c i).re*k (x j-x i)*(c j).im) =
        ∑ i, ∑ j, (c i).im*k (x j-x i)*(c j).re := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hk : k (x i-x j)=k (x j-x i) := by
        rw [show x i-x j=-(x j-x i) by ring,heven]
      rw [hk]
      ring
    calc
      _ = (∑ i, ∑ j, (c i).re*k (x j-x i)*(c j).im)-
          ∑ i, ∑ j, (c i).im*k (x j-x i)*(c j).re := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hswap,sub_self]

/-- Polar positivity produces the ordinary complex positive-definite
kernel for every actual polar profile, including critical beta=1. -/
theorem positiveDefinite_logSeparatorKernel {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1 f))
    (f : WeilTestFn) (hf : ∃ a, IsPolarTest a f.1) :
    GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      (fun y => (logSeparatorKernel hβ hβ1 b ell f y : ℂ)) := by
  apply positiveDefinite_of_real_even (logSeparatorKernel_neg hβ hβ1 b ell f)
  intro N x c
  rw [← logSeparatorKernel_packet]
  exact sub_nonneg.mpr (h (realTranslateTest f x c) (isPolarTest_realTranslateTest f x c hf))

/-- The weighted cosine cross-density varies continuously in actual L1. -/
theorem continuous_logCosDensityL1 {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) : Continuous (logCosDensityL1 hβ hβ1 f) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let E := fun x τ : ℝ =>
    |(‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*Real.cos (x*τ)-
      (‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*Real.cos (x₀*τ)|
  have he (x : ℝ) : ‖logCosDensityL1 hβ hβ1 f x-logCosDensityL1 hβ hβ1 f x₀‖ =
      ∫ τ : ℝ, E x τ := by
    rw [logCosDensityL1,logCosDensityL1,← Integrable.toL1_sub,L1.norm_of_fun_eq_integral_norm]
    simp only [Pi.sub_apply,Real.norm_eq_abs,E]
  have hm : ∀ᶠ x : ℝ in 𝓝 x₀, AEStronglyMeasurable (E x) :=
    Eventually.of_forall fun x => ((integrable_packet_cos hβ hβ1 f x).sub
      (integrable_packet_cos hβ hβ1 f x₀)).abs.aestronglyMeasurable
  have hb : ∀ᶠ x : ℝ in 𝓝 x₀, ∀ᵐ τ : ℝ,
      ‖E x τ‖ ≤ 2*(‖paperFT f.1 τ‖^2*logSpectralWeight β τ) := by
    filter_upwards [] with x
    filter_upwards [] with τ
    have hw : 0 ≤ ‖paperFT f.1 τ‖^2*logSpectralWeight β τ := by
      have hl : 0 ≤ Real.log (2+|τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
      unfold logSpectralWeight
      positivity
    have hh := abs_sub_le
      ((‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*Real.cos (x*τ)) 0
      ((‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*Real.cos (x₀*τ))
    simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hw] at hh
    have h1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (x*τ)) hw
    have h2 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (x₀*τ)) hw
    simp only [E,Real.norm_eq_abs,abs_abs]
    linarith
  have hl : ∀ᵐ τ : ℝ, Tendsto (fun x : ℝ => E x τ) (𝓝 x₀) (𝓝 (0 : ℝ)) := by
    filter_upwards [] with τ
    have hc : Continuous (fun x : ℝ => E x τ) := by unfold E; fun_prop
    simpa only [E,sub_self,abs_zero] using hc.tendsto x₀
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun τ : ℝ => 2*(‖paperFT f.1 τ‖^2*logSpectralWeight β τ)) hm hb
    ((integrable_logWeighted_density hβ hβ1 f).const_mul 2) hl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [he,integral_zero] using ht

private theorem continuous_atomicKernel_zero (b : ℕ → ℝ) (f : WeilTestFn) :
    Continuous (atomicKernel b 0 f.1) := by
  have hc := (EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2).continuous
  have hs := EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have hp := continuous_primeSum_transl (fun n => b n*Real.sqrt n) hc hs
  have he (n : ℕ) :
      (if 2 ≤ n then b n*Real.sqrt n/Real.sqrt n else 0 : ℝ) =
        if 2 ≤ n then b n else 0 := by
    by_cases hn : 2 ≤ n
    · simp only [if_pos hn]
      exact mul_div_cancel_right₀ _ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast (by omega : 0<n)))
    · simp only [if_neg hn]
  simp only [he] at hp
  convert hp.neg using 1
  funext y
  simp only [atomicKernel,atomicForm,Complex.ofReal_zero,zero_mul,zero_sub,Pi.neg_apply]

/-- Actual separator kernels are continuous without a positivity premise. -/
theorem continuous_logSeparatorKernel {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (b : ℕ → ℝ) (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ) (f : WeilTestFn) :
    Continuous (logSeparatorKernel hβ hβ1 b ell f) := by
  have hs := ell.continuous.comp (continuous_logCosDensityL1 hβ hβ1 f)
  have ha := Complex.continuous_re.comp (continuous_atomicKernel_zero b f)
  exact hs.add ((ha.add (ha.comp continuous_neg)).div_const 2)

/-- A finite positive Bochner measure is PRODUCED for every actual polar
profile of the separator, with no full Weil-positivity input. -/
theorem exists_logSeparatorKernel_measure {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1 f))
    (f : WeilTestFn) (hf : ∃ a, IsPolarTest a f.1) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∀ y : ℝ,
      charFun ν y = (logSeparatorKernel hβ hβ1 b ell f y : ℂ) :=
  GaloisForLFunctions.HTGeometry.exists_charFun_eq_of_positiveDefinite
    (positiveDefinite_logSeparatorKernel hβ hβ1 h f hf)
    (Complex.continuous_ofReal.comp (continuous_logSeparatorKernel hβ hβ1 b ell f))

end RHTower.ExposingRayTransfer
