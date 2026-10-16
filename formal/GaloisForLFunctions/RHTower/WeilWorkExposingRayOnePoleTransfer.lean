import GaloisForLFunctions.RHTower.WeilWorkExposingRayOnePolePrimitive
import GaloisForLFunctions.RHTower.WeilFractionalMassTailRigidity

/-!
# One-pole extension of actual sublogarithmic separators

Every actual weighted polar separator is nonnegative on each compact C2
source killing either half-pole, for logarithmic exponent `0 ≤ β < 1`.
The compact primitive, normalized differences, weighted L1 limit and
arithmetic-pairing limit are all produced. No growth or recovery premise
is added. `WeilWorkExposingRayCriticalOnePole` separately completes the endpoint
beta = 1 using large differences and arithmetic Laplace cancellation. The
unrestricted full-source problem is separate.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral WeilOneSided

/-- Exact Fourier multiplier of the first-order exponential difference. -/
def differenceMultiplier (h s τ : ℝ) : ℂ :=
  (cexp (I*(τ:ℂ)*(h:ℂ))-(Real.exp (-s*h):ℂ))/(h:ℂ)

/-- The actual compact C2 normalized difference, including its value at h=0. -/
def exponentialDifferenceQuotient (h s : ℝ) (g : WeilTestFn) : WeilTestFn :=
  translatedDifference h (Real.exp (-s*h))
    ⟨(h:ℂ)⁻¹ • g.1,contDiff_const.smul g.2.1,g.2.2.smul_left⟩

theorem paperFT_exponentialDifferenceQuotient (h s τ : ℝ) (g : WeilTestFn) :
    paperFT (exponentialDifferenceQuotient h s g).1 τ =
      differenceMultiplier h s τ*paperFT g.1 τ := by
  rw [exponentialDifferenceQuotient,paperFT_translatedDifference]
  change _ * paperFT ((h:ℂ)⁻¹ • g.1) τ = _
  rw [WeilSpectral.paperFT_smul]
  unfold differenceMultiplier
  ring

theorem tendsto_differenceMultiplier (s τ : ℝ) :
    Tendsto (fun h : ℝ => differenceMultiplier h s τ) (𝓝[>] 0) (𝓝 (I*(τ:ℂ)+(s:ℂ))) := by
  have h1 : HasDerivAt (fun h : ℝ => cexp (I*(τ:ℂ)*(h:ℂ))) (I*(τ:ℂ)) 0 := by
    simpa using hasDerivAt_cexp_I_mul (τ:ℂ) 0
  have h2 : HasDerivAt (fun h : ℝ => (Real.exp (-s*h):ℂ)) (-(s:ℂ)) 0 := by
    simpa using hasDerivAt_exp_mul_complex (-s) 0
  have ht := (h1.sub h2).tendsto_slope_zero_right
  simpa [differenceMultiplier,Complex.real_smul,div_eq_mul_inv,mul_comm] using ht

theorem norm_differenceMultiplier_le {h s : ℝ} (hh : 0<h) (hh1 : h≤1)
    (hs : |s|≤1/2) (τ : ℝ) : ‖differenceMultiplier h s τ‖ ≤ 2*|τ|+1 := by
  have hp := FractionalMassTailRigidity.norm_cexp_mul_I_sub_le (τ*h) 0
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,sub_zero] at hp
  have he : I*(τ:ℂ)*(h:ℂ) = ((τ*h:ℝ):ℂ)*I := by push_cast; ring
  have harg : |-s*h| ≤ 1 := by
    rw [abs_mul,abs_neg,abs_of_pos hh]
    nlinarith [abs_nonneg s]
  have hr := Real.abs_exp_sub_one_le harg
  rw [abs_mul,abs_neg,abs_of_pos hh] at hr
  have hc : ‖(1:ℂ)-(Real.exp (-s*h):ℂ)‖ = |Real.exp (-s*h)-1| := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  have hb : ‖cexp (I*(τ:ℂ)*(h:ℂ))-(Real.exp (-s*h):ℂ)‖ ≤
      2*|τ| * h+2*|s| * h := by
    calc
      _ = ‖(cexp (I*(τ:ℂ)*(h:ℂ))-1)+(1-(Real.exp (-s*h):ℂ))‖ := by congr 1; ring
      _ ≤ ‖cexp (I*(τ:ℂ)*(h:ℂ))-1‖+‖(1:ℂ)-(Real.exp (-s*h):ℂ)‖ := norm_add_le _ _
      _ ≤ 2*|τ*h|+2*|s| * h := by
        rw [he,hc]
        exact add_le_add hp (by simpa only [mul_assoc] using hr)
      _ = _ := by rw [abs_mul,abs_of_pos hh]; ring
  unfold differenceMultiplier
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
  apply (div_le_iff₀ hh).mpr
  nlinarith [mul_le_mul_of_nonneg_right hs hh.le]

private theorem normSq_linearSymbol (s τ : ℝ) :
    ‖I*(τ:ℂ)+(s:ℂ)‖^2 = τ^2+s^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [Complex.mul_re,Complex.mul_im,pow_two,add_comm]

theorem density_exponentialDifferenceQuotient_le {s : ℝ} (hs : s^2=1/4)
    (f g : WeilTestFn)
    (hfg : ∀ τ : ℝ, paperFT f.1 τ = -(I*(τ:ℂ)+(s:ℂ))*paperFT g.1 τ)
    {h : ℝ} (hh : 0<h) (hh1 : h≤1) (τ : ℝ) :
    ‖paperFT (exponentialDifferenceQuotient h s g).1 τ‖^2 ≤ 8*‖paperFT f.1 τ‖^2 := by
  have hsabs : |s|≤1/2 := by nlinarith [sq_abs s,abs_nonneg s]
  have hn := norm_differenceMultiplier_le hh hh1 hsabs τ
  have hsq : ‖differenceMultiplier h s τ‖^2 ≤ 8*(τ^2+s^2) := by
    have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_abs τ,sq_nonneg (2*|τ|-1)]
  rw [paperFT_exponentialDifferenceQuotient,norm_mul,mul_pow,hfg τ,
    norm_mul,norm_neg,mul_pow,normSq_linearSymbol]
  have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖paperFT g.1 τ‖)
  nlinarith only [hh]

theorem tendsto_density_exponentialDifferenceQuotient (s : ℝ) (f g : WeilTestFn)
    (hfg : ∀ τ : ℝ, paperFT f.1 τ = -(I*(τ:ℂ)+(s:ℂ))*paperFT g.1 τ) (τ : ℝ) :
    Tendsto (fun h : ℝ => ‖paperFT (exponentialDifferenceQuotient h s g).1 τ‖^2)
      (𝓝[>] 0) (𝓝 (‖paperFT f.1 τ‖^2)) := by
  have ht := ((tendsto_differenceMultiplier s τ).norm.pow 2).mul_const (‖paperFT g.1 τ‖^2)
  simpa only [paperFT_exponentialDifferenceQuotient,norm_mul,mul_pow,hfg τ,norm_neg] using ht


private theorem one_le_logWeight (β τ : ℝ) : 1 ≤ logSpectralWeight β τ := by
  have hl : 0 ≤ Real.log (2+|τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  have hp := Real.rpow_nonneg hl β
  unfold logSpectralWeight
  linarith

/-- Actual primitive differences converge in the weighted spectral L1
norm. The dominating density is produced by the exact primitive symbol. -/
theorem tendsto_logDensity_exponentialDifferenceQuotient {β s : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hs : s^2=1/4) (f g : WeilTestFn)
    (hfg : ∀ τ : ℝ, paperFT f.1 τ = -(I*(τ:ℂ)+(s:ℂ))*paperFT g.1 τ) :
    Tendsto (fun h : ℝ => logDensityL1 hβ hβ1 (exponentialDifferenceQuotient h s g))
      (𝓝[>] 0) (𝓝 (logDensityL1 hβ hβ1 f)) := by
  let E := fun h τ : ℝ =>
    |‖paperFT (exponentialDifferenceQuotient h s g).1 τ‖^2*logSpectralWeight β τ-
      ‖paperFT f.1 τ‖^2*logSpectralWeight β τ|
  have he (h : ℝ) :
      ‖logDensityL1 hβ hβ1 (exponentialDifferenceQuotient h s g)-logDensityL1 hβ hβ1 f‖ =
        ∫ τ : ℝ,E h τ := by
    rw [logDensityL1,logDensityL1,← Integrable.toL1_sub,L1.norm_of_fun_eq_integral_norm]
    simp only [Pi.sub_apply,Real.norm_eq_abs,E]
  have hm : ∀ᶠ h : ℝ in 𝓝[>] 0, AEStronglyMeasurable (E h) :=
    Eventually.of_forall fun h =>
      ((integrable_logWeighted_density hβ hβ1 (exponentialDifferenceQuotient h s g)).sub
        (integrable_logWeighted_density hβ hβ1 f)).abs.aestronglyMeasurable
  have hb : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ᵐ τ : ℝ,
      ‖E h τ‖ ≤ 9*(‖paperFT f.1 τ‖^2*logSpectralWeight β τ) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with h hh
    filter_upwards [] with τ
    have hw : 0 ≤ logSpectralWeight β τ := le_trans (by norm_num) (one_le_logWeight β τ)
    have hu := mul_nonneg (sq_nonneg ‖paperFT (exponentialDifferenceQuotient h s g).1 τ‖) hw
    have hv := mul_nonneg (sq_nonneg ‖paperFT f.1 τ‖) hw
    have hd := mul_le_mul_of_nonneg_right
      (density_exponentialDifferenceQuotient_le hs f g hfg hh.1 hh.2.le τ) hw
    dsimp [E]
    simp only [abs_abs]
    apply abs_le.mpr
    constructor <;> nlinarith only [hu,hv,hd]
  have hl : ∀ᵐ τ : ℝ, Tendsto (fun h : ℝ => E h τ) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    filter_upwards [] with τ
    have ht := ((tendsto_density_exponentialDifferenceQuotient s f g hfg τ).mul_const
      (logSpectralWeight β τ)).sub_const (‖paperFT f.1 τ‖^2*logSpectralWeight β τ)
    simpa only [sub_self,abs_zero,E] using ht.abs
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun τ : ℝ => 9*(‖paperFT f.1 τ‖^2*logSpectralWeight β τ)) hm hb
    ((integrable_logWeighted_density hβ hβ1 f).const_mul 9) hl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [he,integral_zero] using ht

/-- Both signs of the actual primitive quotient inherit separator positivity. -/
theorem log_separator_nonneg_quotient {β s : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hs : s^2=1/4) {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1.le f))
    (g : WeilTestFn) (u : ℝ) :
    atomValue b (exponentialDifferenceQuotient u s g).1 ≤
      ell (logDensityL1 hβ hβ1.le (exponentialDifferenceQuotient u s g)) := by
  let G : WeilTestFn := ⟨(u:ℂ)⁻¹ • g.1,contDiff_const.smul g.2.1,g.2.2.smul_left⟩
  have hh := log_separator_nonneg_exponential_differences hβ hβ1 h G u
  by_cases hsign : 0 ≤ s
  · have hs' : s=1/2 := by nlinarith only [hs,hsign]
    have he : -s*u = -u/2 := by rw [hs']; ring
    simpa only [exponentialDifferenceQuotient,he,G] using hh.2
  · have hs' : s=-(1/2) := by nlinarith only [hs,lt_of_not_ge hsign]
    have he : -s*u = u/2 := by rw [hs']; ring
    simpa only [exponentialDifferenceQuotient,he,G] using hh.1

private theorem source_aperture (f : WeilTestFn) :
    ∃ a : ℝ, 0 ≤ a ∧ tsupport f.1 ⊆ Icc (-a) a := by
  obtain ⟨a,ha⟩ := exists_abs_bound_of_hasCompactSupport f.2.2
  refine ⟨|a|,abs_nonneg _,closure_minimal ?_ isClosed_Icc⟩
  intro x hx
  exact abs_le.mp ((ha x hx).trans (le_abs_self a))

private theorem plainDensity_integrable (f : WeilTestFn) :
    Integrable (fun τ : ℝ => ‖paperFT f.1 τ‖^2) := by
  obtain ⟨a,_,ha⟩ := source_aperture f
  exact integrable_normSq_paperFT f.2.1 ha

private theorem plainCos_integrable (f : WeilTestFn) (y : ℝ) :
    Integrable (fun τ : ℝ => ‖paperFT f.1 τ‖^2*Real.cos (τ*y)) := by
  apply (plainDensity_integrable f).mul_bdd
    (show Continuous (fun τ : ℝ => Real.cos (τ*y)) by fun_prop).aestronglyMeasurable
  filter_upwards [] with τ
  simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (τ*y)

private theorem atomCoeff_cosine (f : WeilTestFn) (n : ℕ) :
    (∫ τ : ℝ,‖paperFT f.1 τ‖^2*Real.cos (τ*Real.log n)) = Real.pi*atomCoeff f.1 n := by
  obtain ⟨a,_,ha⟩ := source_aperture f
  exact integral_normSq_paperFT_mul_cos_eq f.2.1 ha (Real.log n)

/-- Every individual raw atom is uniformly controlled by weighted L1 error. -/
theorem pi_mul_abs_atomCoeff_sub_le {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1)
    (f g : WeilTestFn) (n : ℕ) :
    Real.pi*|atomCoeff f.1 n-atomCoeff g.1 n| ≤
      ‖logDensityL1 hβ hβ1 f-logDensityL1 hβ hβ1 g‖ := by
  have hi : Integrable (fun τ : ℝ =>
      (‖paperFT f.1 τ‖^2-‖paperFT g.1 τ‖^2)*Real.cos (τ*Real.log n)) := by
    convert (plainCos_integrable f (Real.log n)).sub (plainCos_integrable g (Real.log n)) using 1
    funext τ
    simp only [Pi.sub_apply]
    ring
  have he : Real.pi*(atomCoeff f.1 n-atomCoeff g.1 n) =
      ∫ τ : ℝ,(‖paperFT f.1 τ‖^2-‖paperFT g.1 τ‖^2)*Real.cos (τ*Real.log n) := by
    rw [mul_sub,← atomCoeff_cosine f n,← atomCoeff_cosine g n,
      ← integral_sub (plainCos_integrable f _) (plainCos_integrable g _)]
    apply integral_congr_ae
    filter_upwards [] with τ
    ring
  have hw := (integrable_logWeighted_density hβ hβ1 f).sub
    (integrable_logWeighted_density hβ hβ1 g)
  calc
    _ = |Real.pi*(atomCoeff f.1 n-atomCoeff g.1 n)| := by
      rw [abs_mul,abs_of_pos Real.pi_pos]
    _ = |∫ τ : ℝ,(‖paperFT f.1 τ‖^2-‖paperFT g.1 τ‖^2)*Real.cos (τ*Real.log n)| := by rw [he]
    _ ≤ ∫ τ : ℝ,|(‖paperFT f.1 τ‖^2-‖paperFT g.1 τ‖^2)*Real.cos (τ*Real.log n)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun τ : ℝ => (‖paperFT f.1 τ‖^2-‖paperFT g.1 τ‖^2)*Real.cos (τ*Real.log n))
    _ ≤ ∫ τ : ℝ,|‖paperFT f.1 τ‖^2*logSpectralWeight β τ-
        ‖paperFT g.1 τ‖^2*logSpectralWeight β τ| := by
      apply integral_mono hi.abs hw.abs
      intro τ
      dsimp only
      simp only [Pi.sub_apply]
      have hw0 : 0≤logSpectralWeight β τ := le_trans (by norm_num) (one_le_logWeight β τ)
      rw [← sub_mul,abs_mul,abs_mul,abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_left
        ((Real.abs_cos_le_one _).trans (one_le_logWeight β τ)) (abs_nonneg _)
    _ = _ := by
      rw [logDensityL1,logDensityL1,← Integrable.toL1_sub,L1.norm_of_fun_eq_integral_norm]
      simp only [Pi.sub_apply,Real.norm_eq_abs]

private theorem quotient_support {g : WeilTestFn} {a : ℝ}
    (hg : tsupport g.1 ⊆ Icc (-a) a) {h : ℝ} (hh : 0<h) (hh1 : h≤1) (s : ℝ) :
    tsupport (exponentialDifferenceQuotient h s g).1 ⊆ Icc (-(a+1)) (a+1) := by
  have hzero (u : ℝ) (hu : a < |u|) : g.1 u=0 := by
    by_contra hz
    have hb := abs_le.mpr (hg (subset_tsupport g.1 hz))
    linarith
  apply closure_minimal _ isClosed_Icc
  intro u hu
  by_contra hnot
  have hau : a+1 < |u| := by
    have hn : ¬ |u| ≤ a+1 := fun hh => hnot (abs_le.mp hh)
    exact lt_of_not_ge hn
  have hu0 := hzero u (by linarith)
  have htri : |u|≤|u-h|+|h| := by
    simpa only [sub_add_cancel] using abs_add_le (u-h) h
  rw [abs_of_pos hh] at htri
  have hum0 := hzero (u-h) (by linarith)
  apply hu
  simp [exponentialDifferenceQuotient,translatedDifference,WeilSpectral.transl,hu0,hum0]

private theorem tendsto_atomCoeff_quotient {β s : ℝ} (hβ : 0≤β) (hβ1 : β≤1)
    (hs : s^2=1/4) (f g : WeilTestFn)
    (hfg : ∀ τ : ℝ,paperFT f.1 τ=-(I*(τ:ℂ)+(s:ℂ))*paperFT g.1 τ) (n : ℕ) :
    Tendsto (fun h : ℝ => atomCoeff (exponentialDifferenceQuotient h s g).1 n)
      (𝓝[>] 0) (𝓝 (atomCoeff f.1 n)) := by
  have ht := tendsto_logDensity_exponentialDifferenceQuotient hβ hβ1 hs f g hfg
  have he : Tendsto (fun h : ℝ =>
      ‖logDensityL1 hβ hβ1 (exponentialDifferenceQuotient h s g)-logDensityL1 hβ hβ1 f‖/Real.pi)
      (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    simpa using ((ht.sub_const (logDensityL1 hβ hβ1 f)).norm).div_const Real.pi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ he
  filter_upwards [] with h
  rw [Real.norm_eq_abs]
  apply (le_div_iff₀ Real.pi_pos).mpr
  simpa only [mul_comm] using pi_mul_abs_atomCoeff_sub_le hβ hβ1
    (exponentialDifferenceQuotient h s g) f n

/-- The common compact support pays the entire finite arithmetic pairing. -/
theorem tendsto_atomValue_exponentialDifferenceQuotient {β s : ℝ}
    (hβ : 0≤β) (hβ1 : β≤1) (hs : s^2=1/4) (b : ℕ → ℝ) (f g : WeilTestFn)
    (hfg : ∀ τ : ℝ,paperFT f.1 τ=-(I*(τ:ℂ)+(s:ℂ))*paperFT g.1 τ) :
    Tendsto (fun h : ℝ => atomValue b (exponentialDifferenceQuotient h s g).1)
      (𝓝[>] 0) (𝓝 (atomValue b f.1)) := by
  obtain ⟨af,haf,hfs⟩ := source_aperture f
  obtain ⟨ag,hag,hgs⟩ := source_aperture g
  let A := af+ag+1
  have hfA : tsupport f.1 ⊆ Icc (-A) A := by
    intro u hu
    have hh := hfs hu
    dsimp [A]
    constructor <;> linarith [hh.1,hh.2]
  let N := ⌊Real.exp (2*A)⌋₊
  have heq : ∀ᶠ h : ℝ in 𝓝[>] 0,
      atomValue b (exponentialDifferenceQuotient h s g).1 =
        ∑ n ∈ Finset.Icc 2 N,b n*atomCoeff (exponentialDifferenceQuotient h s g).1 n := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with h hh
    apply atomValue_eq_sum
    intro u hu
    have hb := quotient_support hgs hh.1 hh.2.le s hu
    dsimp [A]
    constructor <;> linarith [hb.1,hb.2]
  have ht : Tendsto (fun h : ℝ =>
      ∑ n ∈ Finset.Icc 2 N,b n*atomCoeff (exponentialDifferenceQuotient h s g).1 n)
      (𝓝[>] 0) (𝓝 (∑ n ∈ Finset.Icc 2 N,b n*atomCoeff f.1 n)) := by
    apply tendsto_finsetSum
    intro n _
    exact (tendsto_atomCoeff_quotient hβ hβ1 hs f g hfg n).const_mul (b n)
  rw [← atomValue_eq_sum b hfA] at ht
  exact ht.congr' (Filter.Eventually.mono heq (fun _ hh => hh.symm))

/-- Actual weighted polar separators extend to every source with either
half-pole zero for beta<1. The primitive and all limit inputs are produced. -/
theorem log_separator_onePole {β s : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hs : s^2=1/4)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn,(∃ a,IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1.le f))
    (f : WeilTestFn) (hz : paperFT f.1 ((s:ℂ)*I)=0) :
    atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1.le f) := by
  obtain ⟨g,_,_,hfg⟩ := exists_compact_onePole_primitive s f hz
  have ha := tendsto_atomValue_exponentialDifferenceQuotient hβ hβ1.le hs b f g (fun τ => hfg τ)
  have he := ell.continuous.tendsto (logDensityL1 hβ hβ1.le f) |>.comp
    (tendsto_logDensity_exponentialDifferenceQuotient hβ hβ1.le hs f g (fun τ => hfg τ))
  exact le_of_tendsto_of_tendsto ha he
    (Eventually.of_forall fun u => log_separator_nonneg_quotient hβ hβ1 hs h g u)

end RHTower.ExposingRayTransfer
