import GaloisForLFunctions.RHTower.WeilWorkExposingRayCriticalCancellation
import GaloisForLFunctions.RHTower.WeilWorkExposingRayCriticalWindowCancellation
import GaloisForLFunctions.RHTower.WeilWorkExposingRayOnePoleTransfer

/-!
# One-pole extension at the critical logarithmic cost

Translate the one-pole source itself to cancel the remaining pole. Its real
autocorrelation has zero half-pole moment. The exact window Laplace identity
and the source-derived quadratic cancellation exclude the negative direction
left open by sublogarithmic cosh doubling. No Laurent or recovery input is used.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilOneSided WeilSpectral EvenSector

private def realCorr (f : WeilTestFn) (x : ℝ) : ℝ := (EF.weilTest f.1 f.1 x).re

private theorem realCorr_neg (f : WeilTestFn) (x : ℝ) : realCorr f (-x)=realCorr f x := by
  have he := congrFun (tilde_weilTest_self f.1) x
  have hh := congrArg Complex.re he
  simpa only [EF.tilde,Complex.conj_re,realCorr] using hh

private theorem continuous_realCorr (f : WeilTestFn) : Continuous (realCorr f) :=
  Complex.continuous_re.comp (EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2).continuous

private theorem compact_realCorr (f : WeilTestFn) : HasCompactSupport (realCorr f) :=
  (EF.weilTest_hasCompactSupport f.2.2 f.2.2).comp_left Complex.zero_re

private theorem realCorr_pole_zero (f : WeilTestFn)
    (hz : paperFT f.1 (I/2)=0 ∨ paperFT f.1 (-(I/2))=0) :
    ∫ u,realCorr f u*Real.exp (u/2)=0 := by
  have hprod : paperFT (EF.weilTest f.1 f.1) (-(I/2))=0 := by
    rw [EF.paperFT_weilTest f.2.1.continuous f.2.1.continuous f.2.2 f.2.2]
    have he : conj (-(I/2))=I/2 := by
      simpa only [neg_div] using conj_neg_I_div_two
    rw [he]
    rcases hz with h | h <;> simp [h]
  have hi : Integrable fun u : ℝ => EF.weilTest f.1 f.1 u*(Real.exp (u/2):ℂ) :=
    ((EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2).continuous.mul
      (by fun_prop)).integrable_of_hasCompactSupport
      (EF.weilTest_hasCompactSupport f.2.2 f.2.2).mul_right
  have he : paperFT (EF.weilTest f.1 f.1) (-(I/2)) =
      ∫ u : ℝ,EF.weilTest f.1 f.1 u*(Real.exp (u/2):ℂ) := by
    unfold paperFT
    apply integral_congr_ae
    filter_upwards [] with u
    have hx : I* (-(I/2))*(u:ℂ)=((u/2:ℝ):ℂ) := by
      push_cast
      calc
        _ = -(I*I)*(u:ℂ)/2 := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [hx,← Complex.ofReal_exp]
  rw [he] at hprod
  have hr := congrArg Complex.re hprod
  have hri := integral_re hi
  change (∫ u : ℝ,(EF.weilTest f.1 f.1 u*(Real.exp (u/2):ℂ)).re) =
    (∫ u : ℝ,EF.weilTest f.1 f.1 u*(Real.exp (u/2):ℂ)).re at hri
  rw [← hri] at hr
  simpa only [realCorr,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero,Complex.zero_re] using hr

private theorem summable_window (lam : ℕ → ℝ) {q : ℝ → ℝ}
    (hq : HasCompactSupport q) (x : ℝ) :
    Summable fun n : ℕ => (if 2≤n then lam n/Real.sqrt n else 0)*q (Real.log n-x) := by
  have hqc : HasCompactSupport (fun u : ℝ => (q (u-x):ℂ)) :=
    (hq.comp_homeomorph (Homeomorph.subRight x)).comp_left Complex.ofReal_zero
  obtain ⟨N,hN⟩ := exists_forall_log_eq_zero hqc
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hnN : N≤n := by simpa only [Finset.mem_range,not_lt] using hn
  have hz : q (Real.log n-x)=0 := Complex.ofReal_eq_zero.mp (hN n hnN).1
  rw [hz,mul_zero]

private theorem atomicKernel_realCorr (b : ℕ → ℝ) (f : WeilTestFn) (x : ℝ) :
    (atomicKernel b 0 f.1 x).re =
      -(windowKernelSum (criticalWeights b) (realCorr f) x+
        windowKernelSum (criticalWeights b) (realCorr f) (-x)) := by
  have hkc : HasCompactSupport (transl x (EF.weilTest f.1 f.1)) :=
    (EF.weilTest_hasCompactSupport f.2.2 f.2.2).comp_homeomorph (Homeomorph.subRight x)
  have hsum := summable_primeAtoms (fun n => if 2≤n then b n else 0) hkc
  simp only [atomicKernel,atomicForm,Complex.ofReal_zero,zero_mul,zero_sub,Complex.neg_re]
  rw [Complex.re_tsum hsum]
  unfold windowKernelSum
  rw [← (summable_window (criticalWeights b) (compact_realCorr f) x).tsum_add
    (summable_window (criticalWeights b) (compact_realCorr f) (-x))]
  congr 1
  apply tsum_congr
  intro n
  have he : (EF.weilTest f.1 f.1 (-Real.log n-x)).re = realCorr f (Real.log n+x) := by
    change realCorr f (-Real.log n-x)=_
    rw [show -Real.log (n:ℝ)-x=-(Real.log n+x) by ring,realCorr_neg]
  simp only [transl,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.add_re,he,sub_neg_eq_add,criticalWeights]
  by_cases hn : 2≤n
  · simp only [if_pos hn]
    rw [mul_div_cancel_right₀ _ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast (show 0<n by omega)))]
    dsimp [realCorr]
    ring
  · simp only [if_neg hn,zero_mul,add_zero]

private theorem kernel_eq_windows (b : ℕ → ℝ)
    (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ) (f : WeilTestFn) (x : ℝ) :
    logSeparatorKernel (by norm_num : (0:ℝ)≤1) le_rfl b ell f x =
      ell (logCosDensityL1 (by norm_num : (0:ℝ)≤1) le_rfl f x)-
      windowKernelSum (criticalWeights b) (realCorr f) x-
      windowKernelSum (criticalWeights b) (realCorr f) (-x) := by
  rw [logSeparatorKernel,atomicKernel_realCorr,atomicKernel_realCorr,neg_neg]
  ring

private theorem exists_polar_difference (f : WeilTestFn)
    (hz : paperFT f.1 (I/2)=0 ∨ paperFT f.1 (-(I/2))=0) (a : ℝ) :
    ∃ x : ℝ,(x=a ∨ x=-a) ∧
      ∃ R,IsPolarTest R (translatedDifference x (Real.exp (-a/2)) f).1 := by
  have hcompact (x : ℝ) (hpos : paperFT (translatedDifference x (Real.exp (-a/2)) f).1 (I/2)=0)
      (hneg : paperFT (translatedDifference x (Real.exp (-a/2)) f).1 (-(I/2))=0) :
      ∃ R,IsPolarTest R (translatedDifference x (Real.exp (-a/2)) f).1 := by
    let g := translatedDifference x (Real.exp (-a/2)) f
    obtain ⟨R,hR⟩ := exists_abs_bound_of_hasCompactSupport g.2.2
    refine ⟨|R|,abs_nonneg _,g.2.1,closure_minimal ?_ isClosed_Icc,hpos,hneg⟩
    intro u hu
    exact abs_le.mp ((hR u hu).trans (le_abs_self R))
  rcases hz with hz | hz
  · refine ⟨-a,Or.inr rfl,hcompact (-a) ?_ ?_⟩
    · rw [paperFT_translatedDifference,hz,mul_zero]
    · have he : -(-1/2:ℝ)*(-a)=-a/2 := by ring
      have hp : ((-1/2:ℝ):ℂ)*I=-(I/2) := by push_cast; ring
      simpa only [he,hp] using paperFT_translatedDifference_pole (-a) (-1/2) f
  · refine ⟨a,Or.inl rfl,hcompact a ?_ ?_⟩
    · have he : -(1/2:ℝ)*a=-a/2 := by ring
      have hp : ((1/2:ℝ):ℂ)*I=I/2 := by push_cast; ring
      simpa only [he,hp] using paperFT_translatedDifference_pole a (1/2) f
    · rw [paperFT_translatedDifference,hz,mul_zero]

private theorem onePole_kernel_le_cosh
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn,(∃ a,IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0:ℝ)≤1) le_rfl f))
    (f : WeilTestFn) (hz : paperFT f.1 (I/2)=0 ∨ paperFT f.1 (-(I/2))=0) (a : ℝ) :
    logSeparatorKernel (by norm_num : (0:ℝ)≤1) le_rfl b ell f a ≤
      logSeparatorKernel (by norm_num : (0:ℝ)≤1) le_rfl b ell f 0*Real.cosh (a/2) := by
  obtain ⟨x,hx,hpolar⟩ := exists_polar_difference f hz a
  have hh := sub_nonneg.mpr (h _ hpolar)
  rw [logSeparatorKernel_translatedDifference] at hh
  have he : logSeparatorKernel (by norm_num : (0:ℝ)≤1) le_rfl b ell f x =
      logSeparatorKernel (by norm_num : (0:ℝ)≤1) le_rfl b ell f a := by
    rcases hx with rfl | rfl
    · rfl
    · exact logSeparatorKernel_neg _ _ _ _ _ _
  rw [he] at hh
  have hcoef : 1+Real.exp (-a/2)^2=2*Real.exp (-a/2)*Real.cosh (a/2) := by
    have hp : Real.exp (-a/2)*Real.exp (a/2)=1 := by
      rw [← Real.exp_add,show -a/2+a/2=0 by ring,Real.exp_zero]
    rw [Real.cosh_eq,show -(a/2)=-a/2 by ring]
    nlinarith only [hp]
  rw [hcoef] at hh
  exact (mul_le_mul_iff_right₀ (show 0<2*Real.exp (-a/2) by positivity)).mp
    (by nlinarith only [hh])

/-- Critical logarithmic separators extend to either one-pole source. All
boundary and growth inputs are derived from the original polar inequality. -/
theorem critical_separator_onePole
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn,(∃ a,IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0:ℝ)≤1) le_rfl f))
    (f : WeilTestFn) (hz : paperFT f.1 (I/2)=0 ∨ paperFT f.1 (-(I/2))=0) :
    atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0:ℝ)≤1) le_rfl f) := by
  let k := logSeparatorKernel (by norm_num : (0:ℝ)≤1) le_rfl b ell f
  let S := ‖ell‖*‖logDensityL1 (by norm_num : (0:ℝ)≤1) le_rfl f‖
  have hS (a : ℝ) : -S ≤ ell (logCosDensityL1 (by norm_num : (0:ℝ)≤1) le_rfl f a) := by
    have hb : |ell (logCosDensityL1 (by norm_num : (0:ℝ)≤1) le_rfl f a)| ≤ S := by
      have hn := ell.le_opNorm (logCosDensityL1 (by norm_num : (0:ℝ)≤1) le_rfl f a)
      rw [Real.norm_eq_abs] at hn
      exact hn.trans (mul_le_mul_of_nonneg_left (norm_logCosDensityL1_le _ _ f a) (norm_nonneg _))
    exact (abs_le.mp hb).1
  have hk : 0≤k 0 := by
    by_contra hn
    have hkneg : k 0<0 := lt_of_not_ge hn
    obtain ⟨D,hD⟩ := (compact_realCorr f).isCompact.isBounded.subset_closedBall 0
    have hzero (u : ℝ) (hu : |D| < |u|) : realCorr f u=0 := by
      by_contra hn
      have hh := hD (subset_tsupport (realCorr f) hn)
      rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
      linarith [le_abs_self D]
    have hc := nonpos_of_critical_window_tail (fun σ hσ => summable_criticalWeights h hσ)
      (tendsto_critical_quadratic_zero h) (continuous_realCorr f) (compact_realCorr f)
      (realCorr_pole_zero f hz) (A := |D|) (c := -k 0/2) (M := S) (fun a ha => ?_)
    · linarith
    · have hw := kernelSum_eq_zero_of_le (criticalWeights b) (abs_nonneg D) hzero
        (a := -a) (by linarith)
      have hka := onePole_kernel_le_cosh h f hz a
      have he := kernel_eq_windows b ell f a
      rw [hw,sub_zero] at he
      have hcosh : Real.exp (a/2)/2 ≤ Real.cosh (a/2) := by
        rw [Real.cosh_eq]
        linarith [Real.exp_pos (-(a/2))]
      have hm := mul_le_mul_of_nonpos_left hcosh hkneg.le
      change k a ≤ k 0*Real.cosh (a/2) at hka
      change k a = _ at he
      nlinarith only [hka,he,hS a,hm]
  dsimp only [k] at hk
  rw [logSeparatorKernel_zero] at hk
  exact sub_nonneg.mp hk

end RHTower.ExposingRayTransfer
