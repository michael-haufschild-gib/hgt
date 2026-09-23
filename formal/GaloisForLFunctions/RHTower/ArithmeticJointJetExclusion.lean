import GaloisForLFunctions.RHTower.ArithmeticEvenReflectionExclusion
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# Joint arithmetic first-jet exclusion at actual simple critical zeros

The complete even and odd arithmetic bounds force both the Hardy value and its
first derivative to be quadratically small at an off-line zero. Their actual sum
of absolute values defines an explicit positive exclusion radius whenever that
first jet is nonzero. The radius retains the critical zero itself.

The existing unconditional superlinear simple-critical census supplies actual
critical zeros with nonzero Hardy slope, nonzero critical arithmetic response,
and positive exclusion radii above every height. Neither all-height first-jet
nonvanishing nor global strip coverage is asserted.
-/

set_option autoImplicit false
noncomputable section
open Complex Real MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The full odd rational correction has a uniform bound after retaining every height factor. -/
theorem norm_reflectionTargetQuadraticCorrection_le_four {s : ℂ}
    (hs : s ∈ minimumStrip) (ht : 1 ≤ |s.im|) :
    ‖reflectionTargetQuadraticCorrection s‖ ≤ 4 := by
  let c := criticalResponsePoint s.im
  let C := Complex.normSq (star s*(1-star s))
  let C₀ := Complex.normSq (star c*(1-star c))
  let u := |s.im|
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : 1 ≤ u := ht
  have hu3 : 0 ≤ u^(3 : ℕ) := by positivity
  have hu4 : 1 ≤ u^(4 : ℕ) := one_le_pow₀ hu1
  have hu5 : 1 ≤ u^(5 : ℕ) := one_le_pow₀ hu1
  have hC : u^(4 : ℕ) ≤ C := reflection_target_normSq_lower s
  have hC₀ : u^(4 : ℕ) ≤ C₀ := by
    simpa only [show c.im=s.im by simp [c,criticalResponsePoint]] using reflection_target_normSq_lower c
  have hCpos : 0 < C := lt_of_lt_of_le (pow_pos hu 4) hC
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (pow_pos hu 4) hC₀
  have hprod : u^(8 : ℕ) ≤ C*C₀ := by
    calc
      u^(8 : ℕ) = u^(4 : ℕ)*u^(4 : ℕ) := by ring
      _ ≤ C*C₀ := mul_le_mul hC hC₀ (by positivity) hCpos.le
  have h38 : u^(3 : ℕ) ≤ u^(8 : ℕ) := by
    calc u^(3 : ℕ) ≤ u^(3 : ℕ)*u^(5 : ℕ) := by nlinarith [mul_le_mul_of_nonneg_left hu5 hu3]
         _ = u^(8 : ℕ) := by ring
  have hδ : (s.re-1/2)^(2 : ℕ) ≤ 1/4 := by
    have hd : |s.re-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have h := mul_self_le_mul_self (abs_nonneg _) hd
    rw [←pow_two,←pow_two,sq_abs] at h
    norm_num at h
    exact h
  have harg : 0 ≤ 2*s.im^(2 : ℕ)-1/2+(s.re-1/2)^(2 : ℕ) ∧
      2*s.im^(2 : ℕ)-1/2+(s.re-1/2)^(2 : ℕ) ≤ 3*u^(2 : ℕ) := by
    have hu2 : 1 ≤ u^(2 : ℕ) := one_le_pow₀ hu1
    have hsq : s.im^(2 : ℕ)=u^(2 : ℕ) := by simp [u]
    rw [hsq]
    constructor <;> nlinarith [sq_nonneg (s.re-1/2)]
  have hfirst : ‖((s.im*(2*s.im^(2 : ℕ)-1/2+(s.re-1/2)^(2 : ℕ))/(C*C₀):ℝ):ℂ)*I‖ ≤ 3 := by
    rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_div,abs_mul,abs_of_nonneg harg.1,abs_of_pos (mul_pos hCpos hC₀pos)]
    apply (div_le_iff₀ (mul_pos hCpos hC₀pos)).mpr
    have h := mul_le_mul_of_nonneg_left harg.2 hu.le
    change u*(2*s.im^(2 : ℕ)-1/2+(s.re-1/2)^(2 : ℕ)) ≤ _
    nlinarith
  have hc : u ≤ ‖star c+1‖ := by
    simpa [u,c,criticalResponsePoint] using Complex.abs_im_le_norm (star c+1)
  have hq : u^(2 : ℕ) ≤ ‖(star c+1)^(2 : ℕ)‖ := by
    rw [norm_pow]
    exact pow_le_pow_left₀ hu.le hc 2
  have hm := reflection_target_mean_norm_lower s
  have hden : 12 ≤ ‖12*(star c+1)^(2 : ℕ)*((star c+1)^(2 : ℕ)-(((s.re-1/2)^(2 : ℕ):ℝ):ℂ))‖ := by
    rw [show (star c+1)^(2 : ℕ)-(((s.re-1/2)^(2 : ℕ):ℝ):ℂ)=(star s+1)*(2-s) by
      exact reflection_mean_quadratic_difference s]
    rw [show (12:ℂ)*(star c+1)^(2 : ℕ)*((star s+1)*(2-s))=
      (star c+1)^(2 : ℕ)*(12*(star s+1)*(2-s)) by ring,norm_mul]
    have h := mul_le_mul hq hm (by positivity) (norm_nonneg _)
    change u^(2 : ℕ)*(12*u^(2 : ℕ)) ≤ _ at h
    nlinarith
  have hmean : ‖1/(12*(star c+1)^(2 : ℕ)*((star c+1)^(2 : ℕ)-(((s.re-1/2)^(2 : ℕ):ℝ):ℂ)))‖ ≤ 1/12 := by
    rw [norm_div,norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hden
  change ‖((s.im*(2*s.im^(2 : ℕ)-1/2+(s.re-1/2)^(2 : ℕ))/(C*C₀):ℝ):ℂ)*I+
    1/(12*(star c+1)^(2 : ℕ)*((star c+1)^(2 : ℕ)-(((s.re-1/2)^(2 : ℕ):ℝ):ℂ)))‖ ≤ _
  exact (norm_add_le _ _).trans (by linarith)

/-- The fixed normalization cannot amplify the Hardy amplitude correction beyond two. -/
theorem abs_hardyResponseNormalizationRate_im_le_two {t : ℝ} (ht : 1 ≤ |t|) :
    |(hardyResponseNormalizationRate t).im| ≤ 2 := by
  have hu : 0 < |t| := by linarith
  have h₀ : |t| ≤ ‖criticalResponsePoint t‖ := by
    simpa [criticalResponsePoint] using Complex.abs_im_le_norm (criticalResponsePoint t)
  have h₁ : |t| ≤ ‖criticalResponsePoint t+1‖ := by
    simpa [criticalResponsePoint] using Complex.abs_im_le_norm (criticalResponsePoint t+1)
  have hi₀ : ‖(criticalResponsePoint t)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (ht.trans h₀)
  have hi₁ : ‖(criticalResponsePoint t+1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (ht.trans h₁)
  apply (Complex.abs_im_le_norm _).trans
  unfold hardyResponseNormalizationRate
  simp only [one_div]
  exact (norm_add_le _ _).trans (by linarith)

/-- Both arithmetic constraints force the full Hardy first jet to be quadratically small at an off-line zero. -/
theorem hardy_first_jet_at_offline_zero_le {s : ℂ} (hs : s ∈ minimumStrip)
    (ht : 1 ≤ |s.im|) (hd : s.re ≠ 1/2) (hz : riemannZeta s=0) :
    |hardyZ s.im|+|deriv hardyZ s.im| ≤ 48*s.im^(2 : ℕ)*(s.re-1/2)^(2 : ℕ) := by
  have hR := norm_reflectionTargetQuadraticCorrection_le_four hs ht
  have hD := normalized_derivative_constraint_at_offline_zero hs hd hz
  have hnorm : ‖deriv normalizedMinimumZeta (criticalResponsePoint s.im)‖ ≤ 49*(s.re-1/2)^(2 : ℕ)/12 := by
    have h := norm_add_le
      (star (deriv normalizedMinimumZeta (criticalResponsePoint s.im))-
        (((s.re-1/2)^(2 : ℕ):ℝ):ℂ)*reflectionTargetQuadraticCorrection s)
      ((((s.re-1/2)^(2 : ℕ):ℝ):ℂ)*reflectionTargetQuadraticCorrection s)
    rw [sub_add_cancel,norm_star,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)] at h
    nlinarith [mul_le_mul_of_nonneg_left hR (sq_nonneg (s.re-1/2))]
  have hJ := (hardy_response_component_bounds s.im).2
  rw [criticalFullLogResponse_add_target_eq_derivative,norm_star] at hJ
  have hp := hardyResponseDenominator_norm_le ht
  have hJ' : |hardyResponseSlope s.im| ≤ 49/2*s.im^(2 : ℕ)*(s.re-1/2)^(2 : ℕ) := by
    apply hJ.trans
    have h := mul_le_mul hp hnorm (norm_nonneg _) (by positivity : 0 ≤ 6*s.im^(2 : ℕ))
    convert h using 1
    ring
  have hH := hardy_amplitude_at_zero_le hs ht hz
  have hk := abs_hardyResponseNormalizationRate_im_le_two ht
  have hder := abs_sub (hardyResponseSlope s.im)
    ((hardyResponseNormalizationRate s.im).im*hardyZ s.im)
  rw [hardyResponseSlope,add_sub_cancel_right,abs_mul] at hder
  change |deriv hardyZ s.im| ≤ |hardyResponseSlope s.im| + _ at hder
  nlinarith [mul_le_mul hk hH (abs_nonneg _) (by norm_num : (0:ℝ)≤2)]

/-- The literal Hardy value/slope size used by the arithmetic exclusion radius. -/
def hardyFirstJetSize (t : ℝ) : ℝ := |hardyZ t|+|deriv hardyZ t|

/-- The source-defined horizontal radius retaining a strict factor-two comparison reserve. -/
def hardyFirstJetRadius (t : ℝ) : ℝ := Real.sqrt (hardyFirstJetSize t/(96*t^(2 : ℕ)))

/-- A nonzero actual first jet gives a positive radius at nonzero height. -/
theorem hardyFirstJetRadius_pos {t : ℝ} (ht : t ≠ 0) (hJ : 0 < hardyFirstJetSize t) :
    0 < hardyFirstJetRadius t := by
  apply Real.sqrt_pos.mpr
  exact div_pos hJ (mul_pos (by norm_num) (sq_pos_of_ne_zero ht))

/-- Within the explicit first-jet radius, any strip zero is critical. -/
theorem zero_in_hardyFirstJetRadius_is_critical {s : ℂ} (hs : s ∈ minimumStrip)
    (ht : 1 ≤ |s.im|) (hJ : 0 < hardyFirstJetSize s.im)
    (hδ : |s.re-1/2| ≤ hardyFirstJetRadius s.im) (hz : riemannZeta s=0) : s.re=1/2 := by
  by_contra hd
  have h := hardy_first_jet_at_offline_zero_le hs ht hd hz
  change hardyFirstJetSize s.im ≤ _ at h
  have hu : s.im ≠ 0 := abs_pos.mp (by linarith : 0 < |s.im|)
  have hsq := mul_self_le_mul_self (abs_nonneg (s.re-1/2)) hδ
  rw [←pow_two,←pow_two,sq_abs,hardyFirstJetRadius,Real.sq_sqrt (by positivity)] at hsq
  have hd2 := (le_div_iff₀ (by positivity : 0 < 96*s.im^(2 : ℕ))).mp hsq
  nlinarith

/-- The current unconditional superlinear census supplies simple critical Xi zeros above every height. -/
theorem exists_high_simple_critical_xi (T : ℝ) :
    ∃ t : ℝ, T < t ∧ 0 < t ∧ xi (criticalResponsePoint t)=0 ∧
      (analyticOrderAt xi (criticalResponsePoint t)).toNat=1 := by
  classical
  by_contra! h
  apply not_linear_bound_of_superlinear (c := 1/(72*Real.pi)) (K := 0)
    (m := (xiSimpleCriticalZeroCount T:ℝ)) (by positivity)
    eventually_superlinear_xiSimpleCriticalZeroCount
  intro U hU
  have hle : xiSimpleCriticalZeroCount U ≤ xiSimpleCriticalZeroCount T := by
    unfold xiSimpleCriticalZeroCount
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzu,hline,horder⟩ := Finset.mem_filter.mp hz
    obtain ⟨hre0,hre1,him0,himU,hzero⟩ := mem_stripFinsetPos.mp hzu
    have heq : z=criticalResponsePoint z.im := by
      apply Complex.ext <;> simp [criticalResponsePoint,hline]
    have himT : z.im ≤ T := by
      by_contra hn
      have hh := h z.im (lt_of_not_ge hn) him0
      rw [←heq] at hh
      exact hh hzero horder
    exact Finset.mem_filter.mpr ⟨mem_stripFinsetPos.mpr ⟨hre0,hre1,him0,himT,hzero⟩,
      hline,horder⟩
  norm_num only [zero_mul,zero_add]
  exact_mod_cast hle

/-- Actual simple critical Xi zeros have nonzero Hardy slope, by the analytic order bridge. -/
theorem hardy_derivative_ne_zero_of_simple_critical_xi {t : ℝ}
    (hzero : xi (criticalResponsePoint t)=0)
    (horder : (analyticOrderAt xi (criticalResponsePoint t)).toNat=1) :
    hardyZ t=0 ∧ deriv hardyZ t ≠ 0 := by
  have hc : criticalResponsePoint t ∈ minimumStrip := by norm_num [criticalResponsePoint,minimumStrip]
  have hz : riemannZeta (criticalResponsePoint t)=0 :=
    (xi_zero_iff_zeta_zero_of_mem_strip hc.1 hc.2).mp hzero
  have hzorder : analyticOrderAt riemannZeta (criticalResponsePoint t)=1 := by
    rw [←xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hc]
    exact (ENat.toNat_eq_iff_eq_coe _ 1).mp horder
  have ha := unitPhaseZeta_analytic (criticalResponsePoint t) hc
  have hDorder : analyticOrderAt (deriv riemannZeta) (criticalResponsePoint t)=0 := by
    exact analyticOrderAt_deriv_of_pos ha (n := 0) (by simpa using hzorder)
  have hD : deriv riemannZeta (criticalResponsePoint t) ≠ 0 :=
    (analyticOrderAt_eq_zero.mp hDorder).resolve_left (not_not.mpr ha.deriv)
  rw [criticalResponsePoint_eq_linePt] at hz hD
  exact ⟨(riemannZeta_line_eq_zero_iff_hardyZ t).mp hz,
    fun h => hD ((deriv_riemannZeta_eq_zero_iff_deriv_hardyZ_of_zero hz).mpr h)⟩

/-- Simple critical zeros furnish positive actual first jets while their amplitudes vanish. -/
theorem hardyFirstJetSize_pos_of_simple_critical_xi {t : ℝ}
    (hzero : xi (criticalResponsePoint t)=0)
    (horder : (analyticOrderAt xi (criticalResponsePoint t)).toNat=1) :
    0 < hardyFirstJetSize t := by
  obtain ⟨hH,hD⟩ := hardy_derivative_ne_zero_of_simple_critical_xi hzero horder
  simpa [hardyFirstJetSize,hH] using abs_pos.mpr hD

/-- Actual simple critical zeros retain a nonzero arithmetic critical response. -/
theorem critical_response_ne_zero_of_simple_critical_xi {t : ℝ}
    (hzero : xi (criticalResponsePoint t)=0)
    (horder : (analyticOrderAt xi (criticalResponsePoint t)).toNat=1) :
    criticalFullLogResponse t+reflectionZeroTarget (criticalResponsePoint t) ≠ 0 := by
  obtain ⟨hH,hD⟩ := hardy_derivative_ne_zero_of_simple_critical_xi hzero horder
  intro hz
  have hn := hardy_response_norm_sq t
  rw [hz] at hn
  norm_num [hardyResponseSlope,hH] at hn
  apply hD
  nlinarith [hn]

/-- Actual critical zeros with explicit positive off-line exclusion radii occur arbitrarily high. -/
theorem exists_high_critical_zero_with_jet_exclusion (T : ℝ) :
    ∃ t : ℝ, T < t ∧ 1 ≤ t ∧ riemannZeta (criticalResponsePoint t)=0 ∧
      deriv hardyZ t ≠ 0 ∧
      criticalFullLogResponse t+reflectionZeroTarget (criticalResponsePoint t) ≠ 0 ∧
      0 < hardyFirstJetRadius t ∧
      ∀ s : ℂ, s ∈ minimumStrip → s.im=t → |s.re-1/2| ≤ hardyFirstJetRadius t →
        riemannZeta s=0 → s.re=1/2 := by
  obtain ⟨t,hT,ht0,hzero,horder⟩ := exists_high_simple_critical_xi (max T 1)
  have ht1 : 1 ≤ t := le_of_lt ((le_max_right T 1).trans_lt hT)
  have hc : criticalResponsePoint t ∈ minimumStrip := by norm_num [criticalResponsePoint,minimumStrip]
  have hz := (xi_zero_iff_zeta_zero_of_mem_strip hc.1 hc.2).mp hzero
  have hD := (hardy_derivative_ne_zero_of_simple_critical_xi hzero horder).2
  have hJ := hardyFirstJetSize_pos_of_simple_critical_xi hzero horder
  refine ⟨t,(le_max_left T 1).trans_lt hT,ht1,hz,hD,
    critical_response_ne_zero_of_simple_critical_xi hzero horder,hardyFirstJetRadius_pos ht0.ne' hJ,fun s hs hst hd hzs => ?_⟩
  apply zero_in_hardyFirstJetRadius_is_critical hs _ _ _ hzs
  · simpa only [hst,abs_of_pos ht0] using ht1
  · simpa only [hst] using hJ
  · simpa only [hst] using hd

end RHTower.DeletionMixedRefinement

