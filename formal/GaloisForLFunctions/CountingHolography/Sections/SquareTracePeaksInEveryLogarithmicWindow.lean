import GaloisForLFunctions.CountingHolography.Sections.TheThetaMeanOfTheSquareTrace
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.FiniteSpectrumOscillation

/-!
# Positive excursions of the two long square lags

A positive quartet filter intertwines translation with a multiplier on
its retained finite spectrum. The square multiplier is nonzero throughout
the open zeta strip. A peak therefore survives at every exponent below the
zero width in every sufficiently late logarithmic window.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology MeasureTheory Complex Finset Set
open ArithmeticScatteringHolography ArithmeticOrientationGeometry RenormalizedIntersectionTheory
open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality _root_.RHTower
open scoped ComplexConjugate

private abbrev baseCoeff := evenCoeff zetaZeroConfig (boxSpline 1 3)
private def filteredCoeff (k : ℝ → ℝ) (z : ℂ) :=
  baseCoeff z*sourceTransform (fun x => (k x:ℂ)) (I*z)
private def squareCoeff (k : ℝ → ℝ) (z : ℂ) :=
  filteredCoeff k z*(Complex.exp (z*(Real.log 4:ℝ))-2)

private theorem two_trace_series (u : ℝ) :
    2*realSplineTrace u = ∑' z : ℂ, (baseCoeff z*Complex.exp (z*u)).re := by
  have h := configuration_shifted_trace_series temperedConfig_zetaZeroConfig 0 u
  rw [← orbitCorr_eq_re_lagStructure_spline,orbitCorr_splineCycle_eq] at h
  simpa only [Complex.ofReal_zero,sub_zero,neg_zero,zero_mul,Real.exp_zero,one_mul] using h

/-- Translation by log four multiplies each surviving mode by 4^z. -/
private theorem finite_filter_square_trace {k : ℝ → ℝ} (hkc : Continuous k)
    (hm : ∀ s : ℝ, Integrable fun x => Real.exp (s*|x|)*|k x|)
    (S : Finset ℂ) (hout : ∀ z ∉ S, filteredCoeff k z=0) (t : ℝ) :
    (∫ x, k x*(-squareLongTrace (t+x))) = (∑ z ∈ S, squareCoeff k z*Complex.exp (z*t)).re := by
  have hs (v : ℝ) : (∫ x, k x*(2*realSplineTrace (v+x))) =
      ∑ z ∈ S, (filteredCoeff k z*Complex.exp (z*v)).re := by
    simp_rw [two_trace_series]
    rw [integral_kernel_cexp_tsum baseCoeff id (by norm_num : (0:ℝ) ≤ 1/2)
      (summable_norm_evenCoeff_spline temperedConfig_zetaZeroConfig)
      (fun _ hz => abs_re_le_of_evenCoeff_ne_zero hz) hkc hm v]
    simp only [id_eq,← sourceTransform_I_mul_eq_laplace,← filteredCoeff]
    exact tsum_eq_sum (fun z hz => by rw [hout z hz,zero_mul,Complex.zero_re])
  obtain ⟨A,hA,hF⟩ := realSplineTrace_strip_bound
  have hi (v : ℝ) : Integrable (fun x => k x*(2*realSplineTrace (v+x))) := by
    simp_rw [mul_left_comm (k _) 2]
    exact (integrable_kernel_of_strip_bound hA (by norm_num : (0:ℝ) ≤ 1/2)
      (Complex.continuous_re.comp continuous_splineSeries) hkc (hm _) hF v).const_mul 2
  have he (x : ℝ) : k x*(-squareLongTrace (t+x)) =
      k x*(2*realSplineTrace ((t+Real.log 4)+x))-2*(k x*(2*realSplineTrace (t+x))) := by
    unfold squareLongTrace
    rw [show t+x+Real.log 4=t+Real.log 4+x by ring]; ring
  simp_rw [he]
  rw [integral_sub (hi _) ((hi t).const_mul 2),integral_const_mul,hs,hs,
    show (∑ z ∈ S, squareCoeff k z*Complex.exp (z*t)).re = ∑ z ∈ S, (squareCoeff k z*Complex.exp (z*t)).re from
      map_sum Complex.reCLM _ S,mul_sum,← sum_sub_distrib]
  refine sum_congr rfl fun z _ => ?_
  have hid : squareCoeff k z*Complex.exp (z*t) = filteredCoeff k z*Complex.exp (z*(t+Real.log 4:ℝ))-
      2*(filteredCoeff k z*Complex.exp (z*t)) := by
    unfold squareCoeff
    rw [Complex.ofReal_add,mul_add,Complex.exp_add]; ring
  rw [hid,Complex.sub_re]
  simp

private theorem square_multiplier_ne {z : ℂ} (hz : z.re < 1/2) :
    Complex.exp (z*(Real.log 4:ℝ))-2 ≠ 0 := by
  have ht : Real.exp ((1/2)*Real.log 4)=2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    push_cast
    rw [show (1/2:ℝ)*(2*Real.log 2)=Real.log 2 by ring,Real.exp_log (by norm_num)]
  have h := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hz (Real.log_pos (by norm_num : (1:ℝ)<4)))
  rw [ht] at h
  intro he
  have he' := congrArg norm (sub_eq_zero.mp he)
  rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at he'
  norm_num at he'
  linarith only [he',h]

private theorem squareCoeff_conj (k : ℝ → ℝ) (z : ℂ) :
    squareCoeff k (conj z)=conj (squareCoeff k z) := by
  simp only [squareCoeff,filteredCoeff,baseCoeff,evenCoeff_conj,sourceTransform_I_mul_conj,
    map_mul,map_sub,map_ofNat,← Complex.exp_conj,Complex.conj_ofReal]

/-- Below the zero width, every sufficiently late log window contains a
square long-lag value above any fixed multiple of exp(a u). -/
theorem squareLongTrace_peaks_in_every_logarithmic_window {a : ℝ} (ha : 0 ≤ a)
    (haw : a < zetaZeroWidth) (H : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∃ u : ℝ, |u-T| ≤ 16*Real.log (T+2) ∧ H*Real.exp (a*u) < squareLongTrace u := by
  classical
  have hex : ∃ ρ ∈ zetaZeroConfig.carrier, 1/2+a < ρ.re := by
    by_contra! h
    exact haw.not_ge ((zetaZeroWidth_le_iff_re_le ha).mpr h)
  obtain ⟨ρ,hρ,hdeep⟩ := hex
  let z := ρ-1/2
  have hre : z.re = ρ.re-1/2 := by dsimp only [z]; simp
  have hz : baseCoeff z ≠ 0 := evenCoeff_spline_sees hρ (by linarith only [hdeep,ha])
  obtain ⟨k,C,S,hC,hkc,hk,hm,hbudget,hkeep,haway⟩ := exists_zeta_quartet_log_filter hz (by linarith only [hre,hdeep,ha])
  have hout (w : ℂ) (hw : w ∉ S) : filteredCoeff k w = 0 := by
    by_cases hc : baseCoeff w=0
    · rw [filteredCoeff,hc,zero_mul]
    rw [filteredCoeff,haway w hw hc,mul_zero]
  let d := squareCoeff k
  let R := S.filter fun w => d w ≠ 0
  have hmem (w : ℂ) : w ∈ R ↔ d w ≠ 0 := by
    simp only [R,mem_filter]
    refine ⟨fun h => h.2,fun h => ⟨?_,h⟩⟩
    by_contra hw
    exact h (by dsimp only [d,squareCoeff]; rw [hout _ hw,zero_mul])
  have hconj (w : ℂ) : d (conj w)=conj (d w) := squareCoeff_conj k w
  have hc (w : ℂ) (hw : w ∈ R) : conj w ∈ R := by
    apply (hmem _).mpr
    rw [hconj]
    exact fun hh => (hmem w).mp hw (by simpa using congrArg conj hh)
  have him (w : ℂ) (hw : w ∈ R) : w.im ≠ 0 := by
    apply evenCoeff_spline_real
    intro hb
    exact (hmem w).mp hw (by dsimp only [d,squareCoeff,filteredCoeff,baseCoeff]; rw [hb,zero_mul,zero_mul])
  have hzR : z ∈ R := (hmem _).mpr (mul_ne_zero (mul_ne_zero hz hkeep)
    (square_multiplier_ne (by linarith only [hre,hρ.2.2])))
  obtain ⟨v,hv,hmax⟩ := R.exists_max_image Complex.re ⟨z,hzR⟩
  have hva : 0 < v.re-a := by linarith only [hmax z hzR,hre,hdeep]
  obtain ⟨L,η,U,hL,hη,hneg⟩ := finite_spectrum_dense_negative R d hc (fun w _ => hconj w)
    him hv ((hmem v).mp hv) hmax
  have hsum (t : ℝ) : (∫ x, k x*(-squareLongTrace (t+x)))=(∑ w ∈ R, d w*Complex.exp (w*t)).re := by
    rw [finite_filter_square_trace hkc hm S hout]
    congr 1
    exact (sum_subset (filter_subset _ _) (fun w _ hw => by
      have hh : d w=0 := by_contra fun h => hw ((hmem w).mpr h)
      change d w*Complex.exp (w*t)=0
      rw [hh,zero_mul])).symm
  obtain ⟨A,hA,hbound⟩ := squareLongTrace_bound
  let F := fun u => H*Real.exp (a*u)-squareLongTrace u
  let M := ∫ x : ℝ, Real.exp (a*x)*k x
  have ham : a ≤ 1/2 := haw.le.trans zetaZeroWidth_le_half
  have hF (u : ℝ) : |F u| ≤ (|H|+A)*Real.exp (1/2*|u|) := by
    have he := Real.exp_le_exp.mpr (calc a*u ≤ a*|u| := mul_le_mul_of_nonneg_left (le_abs_self _) ha
                                        _ ≤ 1/2*|u| := mul_le_mul_of_nonneg_right ham (abs_nonneg _))
    have hh := abs_sub_le (H*Real.exp (a*u)) 0 (squareLongTrace u)
    simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_pos (Real.exp_pos _)] at hh
    dsimp only [F]
    linarith only [hh,hbound u,mul_le_mul_of_nonneg_left he (abs_nonneg H)]
  have hki : Integrable k := by simpa only [zero_mul,Real.exp_zero,one_mul,abs_of_pos (hk _)] using hm 0
  have hmi : Integrable fun x : ℝ => Real.exp (a*x)*k x := by
    apply (hm a).mono' (show Continuous (fun x : ℝ => Real.exp (a*x)*k x) by fun_prop).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self x) ha)) (abs_nonneg _)
  have hweight (t : ℝ) : Integrable fun x => k x*F (t+x) :=
    integrable_kernel_of_strip_bound (add_nonneg (abs_nonneg H) hA) (by norm_num)
      ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).sub continuous_squareLongTrace)
      hkc (hm _) hF t
  have havg (t : ℝ) : (∫ x, k x*F (t+x))=H*Real.exp (a*t)*M+(∑ w ∈ R,d w*Complex.exp (w*t)).re := by
    have he (x : ℝ) : k x*F (t+x)=(H*Real.exp (a*t))*(Real.exp (a*x)*k x)+k x*(-squareLongTrace (t+x)) := by
      dsimp only [F]; rw [mul_add,Real.exp_add]; ring
    have hfi := integrable_kernel_of_strip_bound hA (by norm_num : (0:ℝ) ≤ 1/2)
      continuous_squareLongTrace hkc (hm _) hbound t
    have hni : Integrable (fun x => k x*(-squareLongTrace (t+x))) := by simpa only [mul_neg] using hfi.neg
    simp_rw [he]
    rw [integral_add (hmi.const_mul _) hni,integral_const_mul,hsum]
  have hleak : Tendsto (fun T : ℝ => (|H|+A)*C*Real.exp (1/2*L-T)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul ((|H|+A)*C*Real.exp (1/2*L))
    simpa only [sub_eq_add_neg,Real.exp_add,mul_assoc,mul_zero] using hh
  have hg := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hva)).const_mul_atTop hη
  filter_upwards [eventually_ge_atTop U,eventually_ge_atTop 6,eventually_ge_atTop (Real.exp (2+L)),
    hleak.eventually_le_const zero_lt_one,hg.eventually_gt_atTop (|H*M|+2)] with T hU hT hlate herr hgr
  have hlog : 2+L ≤ Real.log (T+2) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) (hlate.trans (by linarith))
  obtain ⟨t,ht,hneg'⟩ := hneg T hU
  have ht₀ : 0 ≤ t := by linarith only [ht.1,hT]
  by_contra! hbad
  have hlocal (x : ℝ) (hx : |x| ≤ 8*Real.log (T+2)) : -(0:ℝ) ≤ F (t+x) := by
    have hu : |t+x-T| ≤ 16*Real.log (T+2) := by
      obtain ⟨hx₁,hx₂⟩ := abs_le.mp hx
      rw [abs_le]
      constructor <;> linarith only [hx₁,hx₂,ht.1,ht.2,hlog,hL]
    dsimp only [F]; linarith only [hbad _ hu]
  have hfloor := positive_kernel_logarithmic_floor (A := |H|+A) (C := C) (b := 1/2) (D := 1/2)
    (K := 0) (B := L) (t := t) (add_nonneg (abs_nonneg _) hA) hC.le (by norm_num) (by linarith only [hT])
    (by norm_num) le_rfl hT (by linarith only [hlog,hL]) (by rw [abs_of_nonneg ht₀]; exact ht.2)
    (fun x => (hk x).le) hki (by simpa only [abs_of_pos (hk _)] using hm (1/2+T)) (hweight t) hF
    (hbudget _ (by linarith only [hT])) hlocal
  simp only [neg_zero,zero_mul,zero_sub,havg] at hfloor
  have hgt : |H*M|+2 < η*Real.exp ((v.re-a)*t) := lt_of_lt_of_le hgr
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1 hva.le)) hη.le)
  have hp : 1 ≤ Real.exp (a*t) := Real.one_le_exp (mul_nonneg ha ht₀)
  have he : Real.exp (v.re*t)=Real.exp ((v.re-a)*t)*Real.exp (a*t) := by rw [← Real.exp_add]; congr 1; ring
  rw [he] at hneg'
  linarith only [hfloor,herr,hneg',mul_lt_mul_of_pos_right hgt (Real.exp_pos (a*t)),hp,
    mul_le_mul_of_nonneg_right (le_abs_self (H*M)) (Real.exp_pos (a*t)).le]

#print axioms squareLongTrace_peaks_in_every_logarithmic_window

end GaloisForLFunctions.CountingHolography.Sections
