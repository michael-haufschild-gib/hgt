import GaloisForLFunctions.RHTower.WeilWorkExposingRayLogLocalMass
import GaloisForLFunctions.RHTower.WeilWorkExposingRayCoshDoubling

/-!
# Actual separator kernels below logarithmic spectral cost

An actual polar separator with weight `1 + log(2 + |t|)^beta` gives an
even real translation kernel. Its growth is derived from the actual
resonator coefficient bound; its exact cosh recurrence is derived from
the actual three-translate polar source. For `0 <= beta < 1`, these yield
the cosh majorant without a growth or full-positivity premise.

The majorant proves separator nonnegativity on both actual exponential
one-pole difference families. Their imaginary zero is verified with the
corpus Fourier convention. Extension to every one-pole source requires
the separate compact-primitive limit; no full-source or WP02 sign is
asserted here.

Paper: docs/reports/weil-work/results/02-exposing-ray/ONE-POLE-SUBLOG-PROOF.md.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral WeilOneSided

private theorem norm_atomicKernel_le_cutoff (b : ℕ → ℝ) {f : ℝ → ℂ} {a M : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) (hM : ∀ y, ‖EF.weilTest f f y‖ ≤ M)
    {H : ℕ} (hH : 1 ≤ H) {y : ℝ} (hy : |y|+2*a ≤ Real.log H) :
    ‖atomicKernel b 0 f y‖ ≤ 2*M*∑ n ∈ Finset.Icc 2 H, |b n| := by
  have hvan (u : ℝ) (hu : a < |u|) : f u=0 := by
    by_contra h
    have hh := hs (subset_tsupport f h)
    have hle := abs_le.mpr hh
    linarith
  have hzero (n : ℕ) (hn : n∉Finset.Icc 2 H) :
      ((if 2 ≤ n then b n else 0 : ℝ) : ℂ)*
        (EF.weilTest f f (Real.log n-y)+EF.weilTest f f (-Real.log n-y)) = 0 := by
    by_cases hn2 : 2 ≤ n
    · have hnH : H < n := by
        by_contra hh
        exact hn (Finset.mem_Icc.mpr ⟨hn2,by omega⟩)
      have hlog : Real.log (H:ℝ) < Real.log n := Real.log_lt_log
        (by exact_mod_cast (show 0 < H by omega)) (by exact_mod_cast hnH)
      have h1 : 2*a < |Real.log (n:ℝ)-y| := by
        linarith [le_abs_self (Real.log (n:ℝ)-y), le_abs_self y]
      have h2 : 2*a < |-Real.log (n:ℝ)-y| := by
        linarith [neg_le_abs (-Real.log (n:ℝ)-y), neg_le_abs y]
      rw [weilTest_self_eq_zero hvan h1, weilTest_self_eq_zero hvan h2]
      simp
    · simp [hn2]
  unfold atomicKernel atomicForm
  simp only [Complex.ofReal_zero,zero_mul,zero_sub,WeilSpectral.transl,norm_neg]
  rw [tsum_eq_sum (s := Finset.Icc 2 H) hzero]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 2 H, ‖((if 2 ≤ n then b n else 0 : ℝ) : ℂ)*
        (EF.weilTest f f (Real.log n-y)+EF.weilTest f f (-Real.log n-y))‖ := norm_sum_le _ _
    _ ≤ 2*M*∑ n ∈ Finset.Icc 2 H, |b n| := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      rw [if_pos (Finset.mem_Icc.mp hn).1,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      have hh : ‖EF.weilTest f f (Real.log n-y)+EF.weilTest f f (-Real.log n-y)‖ ≤ 2*M :=
        (norm_add_le _ _).trans (by linarith [hM (Real.log n-y),hM (-Real.log n-y)])
      have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg (b n))
      nlinarith only [hm]

theorem integrable_logCos {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) (x : ℝ) :
    Integrable (fun τ : ℝ =>
      (‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*Real.cos (x*τ)) := by
  apply (integrable_logWeighted_density hβ hβ1 f).mul_bdd
    (show Continuous (fun τ : ℝ => Real.cos (x*τ)) by fun_prop).aestronglyMeasurable
  filter_upwards [] with τ
  rw [Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

/-- Weighted cosine cross-density of an actual compact C2 source. -/
def logCosDensityL1 {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) (x : ℝ) : Lp ℝ 1 (volume : Measure ℝ) :=
  (integrable_logCos hβ hβ1 f x).toL1
    (fun τ : ℝ => (‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*Real.cos (x*τ))

theorem logCosDensityL1_zero {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) : logCosDensityL1 hβ hβ1 f 0 = logDensityL1 hβ hβ1 f := by
  apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
  filter_upwards [] with τ
  simp

theorem logCosDensityL1_neg {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) (x : ℝ) :
    logCosDensityL1 hβ hβ1 f (-x) = logCosDensityL1 hβ hβ1 f x := by
  apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
  filter_upwards [] with τ
  simp

private theorem logWeight_nonneg (β τ : ℝ) : 0 ≤ logSpectralWeight β τ := by
  have hl : 0 ≤ Real.log (2+|τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  unfold logSpectralWeight
  positivity

theorem norm_logCosDensityL1_le {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) (x : ℝ) :
    ‖logCosDensityL1 hβ hβ1 f x‖ ≤ ‖logDensityL1 hβ hβ1 f‖ := by
  rw [logCosDensityL1,L1.norm_of_fun_eq_integral_norm,norm_logDensityL1]
  apply integral_mono (integrable_logCos hβ hβ1 f x).norm
    (integrable_logWeighted_density hβ hβ1 f)
  intro τ
  have hn : 0 ≤ ‖paperFT f.1 τ‖^2*logSpectralWeight β τ :=
    mul_nonneg (sq_nonneg _) (logWeight_nonneg _ _)
  dsimp only
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hn]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hn).trans_eq (mul_one _)

/-- Real symmetric kernel of the actual spectral-minus-arithmetic form. -/
def logSeparatorKernel {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (b : ℕ → ℝ) (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ)
    (f : WeilTestFn) (x : ℝ) : ℝ :=
  ell (logCosDensityL1 hβ hβ1 f x) +
    ((atomicKernel b 0 f.1 x).re+(atomicKernel b 0 f.1 (-x)).re)/2

theorem logSeparatorKernel_zero {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (b : ℕ → ℝ) (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ)
    (f : WeilTestFn) : logSeparatorKernel hβ hβ1 b ell f 0 =
      ell (logDensityL1 hβ hβ1 f)-atomValue b f.1 := by
  unfold logSeparatorKernel
  rw [logCosDensityL1_zero]
  have h0 : atomicKernel b 0 f.1 0 = atomicForm b 0 (EF.weilTest f.1 f.1) := by
    unfold atomicKernel
    congr 1
    funext y
    change EF.weilTest f.1 f.1 (y-0) = EF.weilTest f.1 f.1 y
    rw [sub_zero]
  simp only [neg_zero,h0,atomValue]
  ring

theorem logSeparatorKernel_neg {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (b : ℕ → ℝ) (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ)
    (f : WeilTestFn) (x : ℝ) :
    logSeparatorKernel hβ hβ1 b ell f (-x) = logSeparatorKernel hβ hβ1 b ell f x := by
  simp only [logSeparatorKernel,logCosDensityL1_neg,neg_neg]
  ring

private theorem normSq_farTest (f : WeilTestFn) (x τ : ℝ) :
    ‖paperFT (farTest x f).1 τ‖^2 =
      ‖paperFT f.1 τ‖^2*(1-farPolarCoeff x*Real.cos (x*τ))^2 := by
  change ‖paperFT (farSource x f.1) τ‖^2 = _
  rw [paperFT_farSource f.2.1.continuous f.2.2,norm_mul,mul_pow]
  congr 1
  have hc : 1-(farPolarCoeff x : ℂ)*Complex.cos ((x : ℂ)*τ) =
      ((1-farPolarCoeff x*Real.cos (x*τ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul,← Complex.ofReal_cos]
    push_cast
    rfl
  rw [hc,Complex.norm_real,Real.norm_eq_abs,sq_abs]

private theorem logDensityL1_farTest_eq {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) (x : ℝ) :
    logDensityL1 hβ hβ1 (farTest x f) =
      (1+farPolarCoeff x^2/2) • logDensityL1 hβ hβ1 f -
      (2*farPolarCoeff x) • logCosDensityL1 hβ hβ1 f x +
      (farPolarCoeff x^2/2) • logCosDensityL1 hβ hβ1 f (2*x) := by
  unfold logDensityL1 logCosDensityL1
  rw [← Integrable.toL1_smul',← Integrable.toL1_smul',← Integrable.toL1_sub,
    ← Integrable.toL1_smul',← Integrable.toL1_add]
  apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
  filter_upwards [] with τ
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [normSq_farTest,show 2*x*τ=2*(x*τ) by ring,Real.cos_two_mul]
  ring

/-- Exact quadratic identity for the actual three-translate polar source. -/
theorem logSeparatorKernel_farTest {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (b : ℕ → ℝ) (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ)
    (f : WeilTestFn) (x : ℝ) :
    ell (logDensityL1 hβ hβ1 (farTest x f))-atomValue b (farTest x f).1 =
      (1+farPolarCoeff x^2/2)*logSeparatorKernel hβ hβ1 b ell f 0 -
      (2*farPolarCoeff x)*logSeparatorKernel hβ hβ1 b ell f x +
      (farPolarCoeff x^2/2)*logSeparatorKernel hβ hβ1 b ell f (2*x) := by
  have he : ell (logDensityL1 hβ hβ1 (farTest x f)) =
      (1+farPolarCoeff x^2/2)*ell (logDensityL1 hβ hβ1 f) -
      (2*farPolarCoeff x)*ell (logCosDensityL1 hβ hβ1 f x) +
      (farPolarCoeff x^2/2)*ell (logCosDensityL1 hβ hβ1 f (2*x)) := by
    rw [logDensityL1_farTest_eq,map_add,map_sub,map_smul,map_smul,map_smul]
    rfl
  have ha := atomicForm_farSource b 0 f.2.1.continuous f.2.2 x
  rw [show (farPolarCoeff x : ℂ)^2/4 = ((farPolarCoeff x^2/4 : ℝ) : ℂ) by
    push_cast; rfl] at ha
  have har := congrArg Complex.re ha
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] at har
  norm_num at har
  unfold logSeparatorKernel atomValue
  rw [logCosDensityL1_zero,he]
  simp only [neg_zero]
  change _ - -(atomicForm b 0 (EF.weilTest (farSource x f.1) (farSource x f.1))).re = _
  rw [har]
  ring

/-- Actual polar positivity forces the sharp cosh doubling recurrence. -/
theorem logSeparatorKernel_cosh_recurrence {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1 f))
    (f : WeilTestFn) (x : ℝ) :
    4*Real.cosh (x/2)*(logSeparatorKernel hβ hβ1 b ell f x -
      logSeparatorKernel hβ hβ1 b ell f 0*Real.cosh (x/2)) ≤
      logSeparatorKernel hβ hβ1 b ell f (2*x) -
      logSeparatorKernel hβ hβ1 b ell f 0*Real.cosh ((2*x)/2) := by
  have hh := sub_nonneg.mpr (h (farTest x f) (isPolarTest_farSource f.2.1 f.2.2 x))
  rw [logSeparatorKernel_farTest] at hh
  have hc := Real.cosh_pos (x/2)
  have hm := mul_nonneg hh (sq_nonneg (Real.cosh (x/2)))
  unfold farPolarCoeff at hm
  field_simp at hm
  rw [mul_comm x 2] at hm
  have hcosh : Real.cosh ((2*x)/2) = 2*Real.cosh (x/2)^2-1 := by
    rw [show (2*x)/2=2*(x/2) by ring,Real.cosh_two_mul]
    nlinarith only [Real.cosh_sq_sub_sinh_sq (x/2)]
  rw [hcosh]
  nlinarith only [hm]

private theorem exists_atomicKernel_log_growth {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1 f)) (f : WeilTestFn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖atomicKernel b 0 f.1 x‖ ≤ C*Real.exp (|x|/2)*(1+|x|)^β := by
  obtain ⟨D,hD,hmass⟩ := exists_sqrt_log_mass_of_polar_bound hβ hβ1 h
  obtain ⟨a0,ha0⟩ := exists_abs_bound_of_hasCompactSupport f.2.2
  let a := |a0|
  have ha : 0 ≤ a := abs_nonneg _
  have hs : tsupport f.1 ⊆ Icc (-a) a := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    exact abs_le.mp ((ha0 x hx).trans (le_abs_self a0))
  have hc := (weilTest_self_data f.2.1 hs).2.1.continuous
  obtain ⟨M,hM⟩ := hc.bounded_above_of_compact_support
    (EF.weilTest_hasCompactSupport f.2.2 f.2.2)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  let C := 2*M*D*Real.exp ((2*a+1)/2)*(2*a+2)^β
  refine ⟨C,by dsimp [C]; positivity,fun x => ?_⟩
  let N := ⌈Real.exp (|x|+2*a)⌉₊
  have hN : 1 ≤ N := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hlow : Real.exp (|x|+2*a) ≤ (N:ℝ) := Nat.le_ceil _
  have hcut : |x|+2*a ≤ Real.log (N:ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos _) hlow
    simpa only [Real.log_exp] using hh
  have hNup : (N:ℝ) ≤ Real.exp (|x|+2*a+1) := by
    have hh : (N:ℝ) ≤ Real.exp (|x|+2*a)+1 :=
      (Nat.ceil_lt_add_one (by positivity : 0≤Real.exp (|x|+2*a))).le
    have he : 1 ≤ Real.exp (|x|+2*a) := Real.one_le_exp_iff.mpr (by positivity)
    have h1 := Real.add_one_le_exp (1:ℝ)
    rw [Real.exp_add]
    dsimp [N]
    nlinarith only [hh,he,h1]
  have hlog : Real.log (N:ℝ) ≤ |x|+2*a+1 := by
    have hh := Real.log_le_log hNpos hNup
    simpa only [Real.log_exp] using hh
  have hroot : Real.sqrt (N:ℝ) ≤ Real.exp (|x|/2)*Real.exp ((2*a+1)/2) := by
    calc
      _ ≤ Real.sqrt (Real.exp (|x|+2*a+1)) := Real.sqrt_le_sqrt hNup
      _ = Real.exp ((|x|+2*a+1)/2) := (Real.exp_half _).symm
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlog0 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hbase : 1+Real.log (N:ℝ) ≤ (2*a+2)*(1+|x|) := by
    nlinarith [abs_nonneg x]
  have hw : (1+Real.log (N:ℝ))^β ≤ (2*a+2)^β*(1+|x|)^β := by
    have hh := Real.rpow_le_rpow (by positivity : 0≤1+Real.log (N:ℝ)) hbase hβ
    simpa only [Real.mul_rpow (by positivity : 0≤2*a+2) (by positivity : 0≤1+|x|)] using hh
  calc
    _ ≤ 2*M*∑ n ∈ Finset.Icc 2 N,|b n| := norm_atomicKernel_le_cutoff b hs hM hN hcut
    _ ≤ 2*M*(D*Real.sqrt N*(1+Real.log N)^β) :=
      mul_le_mul_of_nonneg_left (hmass N hN) (by positivity)
    _ ≤ 2*M*(D*(Real.exp (|x|/2)*Real.exp ((2*a+1)/2))*
        ((2*a+2)^β*(1+|x|)^β)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hroot hD) hw
        (by positivity) (by positivity)
    _ = C*Real.exp (|x|/2)*(1+|x|)^β := by dsimp [C]; ring

/-- Every actual weighted separator supplies the growth needed by doubling.
The original exponent is retained; no growth assumption is added. -/
theorem exists_logSeparatorKernel_growth {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1 f)) (f : WeilTestFn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      |logSeparatorKernel hβ hβ1 b ell f x| ≤
        C*Real.exp (|x|/2)*(1+|x|)^β := by
  obtain ⟨D,hD,hd⟩ := exists_atomicKernel_log_growth hβ hβ1 h f
  let S := ‖ell‖*‖logDensityL1 hβ hβ1 f‖
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨S+D,by positivity,fun x => ?_⟩
  have hs : |ell (logCosDensityL1 hβ hβ1 f x)| ≤ S := by
    calc
      _ ≤ ‖ell‖*‖logCosDensityL1 hβ hβ1 f x‖ := by
        simpa only [Real.norm_eq_abs] using ell.le_opNorm (logCosDensityL1 hβ hβ1 f x)
      _ ≤ S := mul_le_mul_of_nonneg_left (norm_logCosDensityL1_le hβ hβ1 f x) (norm_nonneg _)
  have he : 1 ≤ Real.exp (|x|/2) := Real.one_le_exp_iff.mpr (by positivity)
  have hp : 1 ≤ (1+|x|)^β := Real.one_le_rpow (by linarith [abs_nonneg x]) hβ
  have ht : 1 ≤ Real.exp (|x|/2)*(1+|x|)^β := by nlinarith only [he,hp]
  have hx := (Complex.abs_re_le_norm (atomicKernel b 0 f.1 x)).trans (hd x)
  have hnx := (Complex.abs_re_le_norm (atomicKernel b 0 f.1 (-x))).trans (hd (-x))
  simp only [abs_neg] at hnx
  have ha := abs_add_le (atomicKernel b 0 f.1 x).re (atomicKernel b 0 f.1 (-x)).re
  have hb : |((atomicKernel b 0 f.1 x).re+(atomicKernel b 0 f.1 (-x)).re)/2| ≤
      D*Real.exp (|x|/2)*(1+|x|)^β := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hsum := (abs_add_le (ell (logCosDensityL1 hβ hβ1 f x))
    (((atomicKernel b 0 f.1 x).re+(atomicKernel b 0 f.1 (-x)).re)/2)).trans
    (add_le_add hs hb)
  have hSbound := mul_le_mul_of_nonneg_left ht hS
  dsimp [logSeparatorKernel]
  nlinarith only [hsum,hSbound]

/-- Actual polar separators have the cosh majorant below linear log cost.
All growth and recurrence inputs are produced from actual sources above. -/
theorem logSeparatorKernel_le_cosh {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1.le f))
    (f : WeilTestFn) (x : ℝ) :
    logSeparatorKernel hβ hβ1.le b ell f x ≤
      logSeparatorKernel hβ hβ1.le b ell f 0*Real.cosh (x/2) := by
  let k := logSeparatorKernel hβ hβ1.le b ell f
  let d : ℝ → ℝ := fun y => k y-k 0*Real.cosh (y/2)
  obtain ⟨C,hC,hgrowth⟩ := exists_logSeparatorKernel_growth hβ hβ1.le h f
  have hpos (x : ℝ) (hx : 0 < x) : d x ≤ 0 := by
    apply nonpos_of_cosh_doubling_sublinear hβ hβ1
      (show 0 ≤ C+|k 0| by positivity) (d := d) (x := x)
    · intro y hy
      have he : Real.exp (-y/2)*Real.exp (y/2) = 1 := by
        rw [← Real.exp_add,show -y/2+y/2=0 by ring,Real.exp_zero]
      have hky := mul_le_mul_of_nonneg_left
        ((le_abs_self (k y)).trans (hgrowth y)) (Real.exp_pos (-y/2)).le
      rw [abs_of_pos hy] at hky
      have hk : Real.exp (-y/2)*k y ≤ C*(1+y)^β := by
        calc
          _ ≤ Real.exp (-y/2)*(C*Real.exp (y/2)*(1+y)^β) := hky
          _ = C*(1+y)^β*(Real.exp (-y/2)*Real.exp (y/2)) := by ring
          _ = _ := by rw [he,mul_one]
      have ht : Real.exp (-y/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hc0 : 0 ≤ Real.exp (-y/2)*Real.cosh (y/2) := by positivity
      have hc1 : Real.exp (-y/2)*Real.cosh (y/2) ≤ 1 := by
        rw [Real.cosh_eq,show -(y/2) = -y/2 by ring]
        have ht0 := (Real.exp_pos (-y/2)).le
        nlinarith only [he,ht,ht0]
      have hp : 1 ≤ (1+y)^β := Real.one_le_rpow (by linarith) hβ
      have hterm : -k 0*(Real.exp (-y/2)*Real.cosh (y/2)) ≤ |k 0| := by
        calc
          _ ≤ |k 0| * (Real.exp (-y/2)*Real.cosh (y/2)) :=
            mul_le_mul_of_nonneg_right (neg_le_abs _) hc0
          _ ≤ |k 0| := by nlinarith only [mul_le_mul_of_nonneg_left hc1 (abs_nonneg (k 0))]
      have hterm2 := mul_le_mul_of_nonneg_left hp (abs_nonneg (k 0))
      dsimp [d]
      nlinarith only [hk,hterm,hterm2]
    · intro y _
      exact logSeparatorKernel_cosh_recurrence hβ hβ1.le h f y
    · exact hx
  rcases lt_trichotomy 0 x with hx|hx|hx
  · exact sub_nonpos.mp (hpos x hx)
  · subst x
    simp
  · have hh := sub_nonpos.mp (hpos (-x) (by linarith))
    dsimp [d,k] at hh
    simpa only [logSeparatorKernel_neg,neg_div,Real.cosh_neg] using hh

/-- Actual translated difference, retaining its compact C2 regularity. -/
def translatedDifference (x r : ℝ) (f : WeilTestFn) : WeilTestFn :=
  ⟨WeilSpectral.transl x f.1 - (r : ℂ) • f.1,
    (f.2.1.comp (contDiff_id.sub contDiff_const)).sub (contDiff_const.smul f.2.1),
    (f.2.2.comp_homeomorph (Homeomorph.subRight x)).sub f.2.2.smul_left⟩

theorem paperFT_translatedDifference (x r : ℝ) (f : WeilTestFn) (z : ℂ) :
    paperFT (translatedDifference x r f).1 z =
      (cexp (I*z*(x : ℂ))-(r : ℂ))*paperFT f.1 z := by
  have hi (s : ℝ) : Integrable (fun y : ℝ => f.1 (y-s)*cexp (I*z*y)) :=
    ((f.2.1.continuous.comp (continuous_id.sub continuous_const)).mul
      (by fun_prop)).integrable_of_hasCompactSupport
      (f.2.2.comp_homeomorph (Homeomorph.subRight s)).mul_right
  have i0 : Integrable (fun y : ℝ => f.1 y*cexp (I*z*y)) := by simpa using hi 0
  have he : (fun y : ℝ => (translatedDifference x r f).1 y*cexp (I*z*y)) =
      fun y => f.1 (y-x)*cexp (I*z*y)-(r:ℂ)*(f.1 y*cexp (I*z*y)) := by
    funext y
    simp only [translatedDifference,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,WeilSpectral.transl]
    ring
  rw [paperFT,he,integral_sub (hi x) (i0.const_mul _),integral_const_mul]
  change paperFT (WeilSpectral.transl x f.1) z-(r:ℂ)*paperFT f.1 z = _
  rw [paperFT_transl]
  ring

/-- The exponential coefficient cancels its literal imaginary evaluation. -/
theorem paperFT_translatedDifference_pole (x s : ℝ) (f : WeilTestFn) :
    paperFT (translatedDifference x (Real.exp (-s*x)) f).1 ((s:ℂ)*I) = 0 := by
  rw [paperFT_translatedDifference]
  have he : I*((s:ℂ)*I)*(x:ℂ) = ((-s*x:ℝ):ℂ) := by
    push_cast
    calc
      _ = (s:ℂ)*(x:ℂ)*(I*I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he,← Complex.ofReal_exp,sub_self,zero_mul]

private theorem normSq_translatedDifference (x r τ : ℝ) (f : WeilTestFn) :
    ‖paperFT (translatedDifference x r f).1 τ‖^2 =
      (1+r^2-2*r*Real.cos (x*τ))*‖paperFT f.1 τ‖^2 := by
  rw [paperFT_translatedDifference,norm_mul,mul_pow]
  congr 1
  have he : I*(τ:ℂ)*(x:ℂ) = ((x*τ:ℝ):ℂ)*I := by push_cast; ring
  rw [he,Complex.sq_norm,Complex.normSq_sub]
  rw [Complex.normSq_eq_norm_sq,Complex.norm_exp_ofReal_mul_I]
  simp only [Complex.normSq_ofReal,Complex.conj_ofReal,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.exp_ofReal_mul_I_re]
  ring

private theorem logDensityL1_translatedDifference {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (x r : ℝ) (f : WeilTestFn) :
    logDensityL1 hβ hβ1 (translatedDifference x r f) =
      (1+r^2) • logDensityL1 hβ hβ1 f-(2*r) • logCosDensityL1 hβ hβ1 f x := by
  unfold logDensityL1 logCosDensityL1
  rw [← Integrable.toL1_smul',← Integrable.toL1_smul',← Integrable.toL1_sub]
  apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
  filter_upwards [] with τ
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [normSq_translatedDifference]
  ring

private theorem translatedDifference_packet (x r : ℝ) (f : WeilTestFn) :
    (translatedDifference x r f).1 = ∑ j : Fin 2,
      (![-(r:ℂ),1] j) • WeilSpectral.transl (![0,x] j) f.1 := by
  funext y
  simp [translatedDifference,Fin.sum_univ_succ,WeilSpectral.transl]
  ring

/-- Exact two-translate identity for the actual separating form. -/
theorem logSeparatorKernel_translatedDifference {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (b : ℕ → ℝ) (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ)
    (f : WeilTestFn) (x r : ℝ) :
    ell (logDensityL1 hβ hβ1 (translatedDifference x r f))-
        atomValue b (translatedDifference x r f).1 =
      (1+r^2)*logSeparatorKernel hβ hβ1 b ell f 0 -
        2*r*logSeparatorKernel hβ hβ1 b ell f x := by
  have ha := atomicForm_packet b 0 f.2.1.continuous f.2.2 (![0,x]) (![-(r:ℂ),1])
  rw [← translatedDifference_packet] at ha
  simp [Fin.sum_univ_succ] at ha
  have har := congrArg Complex.re ha
  norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im] at har
  rw [logDensityL1_translatedDifference,map_sub,map_smul,map_smul]
  unfold logSeparatorKernel atomValue
  rw [logCosDensityL1_zero,har]
  simp only [neg_zero,smul_eq_mul]
  ring

/-- Every actual two-pole separator is nonnegative on both exponential
one-pole difference families for beta<1, with no extra growth premise. -/
theorem log_separator_nonneg_exponential_differences {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1.le f))
    (f : WeilTestFn) (x : ℝ) :
    atomValue b (translatedDifference x (Real.exp (x/2)) f).1 ≤
      ell (logDensityL1 hβ hβ1.le (translatedDifference x (Real.exp (x/2)) f)) ∧
    atomValue b (translatedDifference x (Real.exp (-x/2)) f).1 ≤
      ell (logDensityL1 hβ hβ1.le (translatedDifference x (Real.exp (-x/2)) f)) := by
  have hk := logSeparatorKernel_le_cosh hβ hβ1 h f x
  have hcase (r : ℝ) (hr : 0 ≤ r) (he : 1+r^2 = 2*r*Real.cosh (x/2)) :
      atomValue b (translatedDifference x r f).1 ≤
        ell (logDensityL1 hβ hβ1.le (translatedDifference x r f)) := by
    apply sub_nonneg.mp
    rw [logSeparatorKernel_translatedDifference]
    have hh := mul_le_mul_of_nonneg_left hk (show 0≤2*r by positivity)
    rw [he]
    nlinarith only [hh]
  have he : Real.exp (-x/2)*Real.exp (x/2) = 1 := by
    rw [← Real.exp_add,show -x/2+x/2=0 by ring,Real.exp_zero]
  constructor
  · apply hcase _ (Real.exp_pos _).le
    rw [Real.cosh_eq,show -(x/2) = -x/2 by ring]
    nlinarith only [he]
  · apply hcase _ (Real.exp_pos _).le
    rw [Real.cosh_eq,show -(x/2) = -x/2 by ring]
    nlinarith only [he]

end RHTower.ExposingRayTransfer
