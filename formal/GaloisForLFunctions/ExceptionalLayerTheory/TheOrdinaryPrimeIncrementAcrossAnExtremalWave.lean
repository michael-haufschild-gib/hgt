import GaloisForLFunctions.ExceptionalLayerTheory.TheTwoIntervalRadiusControlsEachSquaredPrimeIncrement
import GaloisForLFunctions.ExceptionalLayerTheory.ABoundedQuartetRadiusHasAFiniteExtremalLayer
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRayleighFloor

/-!
# Sign control for the ordinary-prime increment

A unit average makes the prime count continuous at a cost of at most one
prime's logarithm. A continuous increment cannot reverse sign on a part of
a wave where its squared amplitude stays above the squared-error bound.
-/

noncomputable section
open Filter Topology MeasureTheory Set
open RHTower ComplexConjugate _root_.HTGeometry
open GaloisForLFunctions.ZeroConfigurationGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory

private def unitAverageTheta (x : ℝ) := ∫ y in x..x+1, Chebyshev.theta y

private theorem continuous_unitAverageTheta : Continuous unitAverageTheta := by
  let P := fun x : ℝ => ∫ y in (0:ℝ)..x, Chebyshev.theta y
  have hi (a b : ℝ) : IntervalIntegrable Chebyshev.theta volume a b :=
    Chebyshev.theta_mono.intervalIntegrable
  have hp : Continuous P := intervalIntegral.continuous_primitive hi 0
  have he (x : ℝ) : unitAverageTheta x = P (x+1)-P x := by
    have ha := intervalIntegral.integral_add_adjacent_intervals (hi 0 x) (hi x (x+1))
    exact eq_sub_of_add_eq' ha
  rw [funext he]
  exact (hp.comp (continuous_id.add continuous_const)).sub hp

private theorem abs_unitAverageTheta_sub_theta {x : ℝ} (hx : 0 ≤ x) :
    |unitAverageTheta x - Chebyshev.theta x| ≤ Real.log (x+1) := by
  have hxx : x ≤ x+1 := le_add_of_nonneg_right zero_le_one
  have hi : IntervalIntegrable Chebyshev.theta volume x (x+1) :=
    Chebyshev.theta_mono.intervalIntegrable
  have hlo := intervalIntegral.integral_mono_on hxx
    (intervalIntegrable_const (c := Chebyshev.theta x)) hi
    (fun y hy => Chebyshev.theta_mono hy.1)
  have hhi := intervalIntegral.integral_mono_on hxx hi
    (intervalIntegrable_const (c := Chebyshev.theta (x+1)))
    (fun y hy => Chebyshev.theta_mono hy.2)
  simp only [intervalIntegral.integral_const,add_sub_cancel_left,one_smul] at hlo hhi
  rw [unitAverageTheta, abs_of_nonneg (sub_nonneg.mpr hlo)]
  refine (sub_le_sub_right hhi _).trans ?_
  rw [RHTower.Sieve.theta_sub_eq_sum_Ioc hxx, Nat.floor_add_one hx,
    Nat.Ioc_succ_singleton, Finset.sum_filter, Finset.sum_singleton]
  split_ifs
  · apply Real.log_le_log (by positivity)
    exact_mod_cast (show (⌊x⌋₊ : ℝ)+1 ≤ x+1 from add_le_add_right (Nat.floor_le hx) 1)
  · exact Real.log_nonneg (by linarith only [hx])

/-- A continuous approximation to the signed normalized prime increment.
The numerator of the error costs at most the logarithms of two possible jumps. -/
theorem exists_continuous_normalizedPrimeIncrement_approx (β : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∃ V : ℝ → ℝ, Continuous V ∧ ∀ t, 0 ≤ t →
      |V t - normalizedPrimeIncrement β h t| ≤ (2*t+h+2)/Real.exp (β*t) := by
  let E := fun t => unitAverageTheta (Real.exp t) - Real.exp t
  have hE : Continuous E := (continuous_unitAverageTheta.comp Real.continuous_exp).sub Real.continuous_exp
  refine ⟨fun t => (E (t+h)-E t)/Real.exp (β*t),
    ((hE.comp (continuous_id.add continuous_const)).sub hE).div
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)) (fun _ => Real.exp_ne_zero _), ?_⟩
  have herr (s : ℝ) (hs : 0 ≤ s) : |E s-thetaLogError s| ≤ s+1 := by
    dsimp only [E, thetaLogError]
    rw [sub_sub_sub_cancel_right]
    refine (abs_unitAverageTheta_sub_theta (Real.exp_pos _).le).trans ?_
    rw [Real.log_le_iff_le_exp (by positivity)]
    have he : 1 ≤ Real.exp s := Real.one_le_exp hs
    have htwo : 2 ≤ Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
    rw [Real.exp_add]
    linarith only [he, mul_le_mul_of_nonneg_left htwo (Real.exp_pos s).le]
  intro t ht
  rw [normalizedPrimeIncrement, ← sub_div, abs_div, abs_of_pos (Real.exp_pos _)]
  apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
  rw [logStepIncrement, show E (t+h)-E t-(thetaLogError (t+h)-thetaLogError t) =
    (E (t+h)-thetaLogError (t+h))-(E t-thetaLogError t) by ring]
  exact (abs_sub _ _).trans ((add_le_add (herr _ (add_nonneg ht hh)) (herr _ ht)).trans_eq (by ring))

/-- From a point to a crest where the signs agree, suppose the squared wave
never falls below its initial value. Uniform squared-amplitude control on
that interval bounds the signed error even when the initial sign differs. -/
theorem sq_sub_le_on_wave_lobe {u D : ℝ → ℝ} {t s B : ℝ}
    (hu : ContinuousOn u (uIcc t s)) (hD : ContinuousOn D (uIcc t s))
    (hcrest : 0 < u s * D s)
    (hlobe : ∀ r ∈ uIcc t s, D t^2 ≤ D r^2)
    (hbound : ∀ r ∈ uIcc t s, |u r^2-D r^2| ≤ B) :
    (u t-D t)^2 ≤ 6*B := by
  have ht := hbound t left_mem_uIcc
  have hB := (abs_nonneg _).trans ht
  by_cases hsmall : D t^2 ≤ B
  · nlinarith only [(abs_le.mp ht).2, hsmall, sq_nonneg (u t+D t)]
  have hsign : 0 ≤ u t * D t := by
    by_contra! hn
    obtain ⟨r,hr,hr0⟩ := intermediate_value_uIcc (hu.mul hD)
      (show (0:ℝ) ∈ uIcc (u t*D t) (u s*D s) from mem_uIcc_of_le hn.le hcrest.le)
    have hl := hlobe r hr
    have hb := (abs_le.mp (hbound r hr)).1
    rcases mul_eq_zero.mp hr0 with he | he
    · rw [he, zero_pow two_ne_zero, zero_sub] at hb
      exact hsmall (by linarith only [hl,hb])
    · rw [he,zero_pow two_ne_zero] at hl
      exact hsmall (hl.trans hB)
  have hle : |u t-D t| ≤ |u t+D t| := sq_le_sq.mp (by nlinarith only [hsign])
  calc _ = |u t-D t| * |u t-D t| := by rw [← sq, sq_abs]
    _ ≤ |u t-D t| * |u t+D t| := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ = |u t^2-D t^2| := by rw [← abs_mul]; congr 1; ring
    _ ≤ 6*B := ht.trans (by linarith only [hB])

/-- At a bounded trial the signed boundary increment is one nonzero sinusoid.
Its frequency is the absolute ordinate of an actual extremal zero. -/
theorem exists_cosine_boundaryStep_of_bounded_thetaRadial {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) :
    let β := zetaZeroAbscissa
    let D := boundaryStep β (quarterPeriodStep γ) (primeErrorBoundaryTrace β)
    ∃ (q : XiZeroCopy) (K φ : ℝ), (q.1 : ℂ).re = β ∧ 0 < K ∧
      ∀ t, D t = K * Real.cos (|xiCopyOrdinate q|*t+φ) := by
  classical
  intro β D
  obtain ⟨q,hq,hall⟩ := (extremal_radial_exclusion_or_one_top_pair hΘ hγ hm).resolve_left hb
  let ω := |xiCopyOrdinate q|
  let h := quarterPeriodStep γ
  let a := stepAmplitude β h
  let hf := finite_top_of_bounded_thetaRadial hΘ hγ hb
  let S := hf.toFinset
  let b := fun r : XiZeroCopy => if xiCopyOrdinate r = ω then a r else conj (a r)
  let B := ∑ r ∈ S, b r
  have hneg (t : ℝ) : expChar (-ω) t = conj (expChar ω t) := by
    rw [expChar,expChar,← Complex.exp_conj]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring
  have hsum (t : ℝ) : D t = (B * expChar ω t).re := by
    have hfin : (D t : ℂ) = ∑ r ∈ S, a r * expChar (xiCopyOrdinate r) t := by
      rw [stepAmplitude_carrier hΘ, expSeriesCarrier]
      apply tsum_eq_sum
      intro r hr
      have hne : (r.1 : ℂ).re ≠ β := fun he => hr (hf.mem_toFinset.mpr he)
      simp only [a, stepAmplitude, primeErrorBoundaryAmplitude, if_neg hne, mul_zero, zero_mul]
    have he := congrArg Complex.re hfin
    rw [Complex.ofReal_re, Complex.re_sum] at he
    rw [he, show B * expChar ω t = ∑ r ∈ S, b r * expChar ω t from Finset.sum_mul S b _, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hpos : xiCopyOrdinate r = ω
    · simp only [b, if_pos hpos, hpos]
    · have habs := hall r (hf.mem_toFinset.mp hr)
      have hω : xiCopyOrdinate r = -ω := by
        rcases abs_choice (xiCopyOrdinate r) with hp | hn
        · exact (hpos (hp.symm.trans habs)).elim
        · dsimp only [ω]
          linarith only [hn,habs]
      simp only [b,if_neg hpos,hω,hneg]
      rw [Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.conj_re, Complex.conj_im]
      ring
  have hform (t : ℝ) : D t = ‖B‖ * Real.cos (ω*t+B.arg) := by
    rw [hsum]
    calc (B * expChar ω t).re =
        ((‖B‖ : ℂ) * Complex.exp (((ω*t+B.arg : ℝ) : ℂ)*Complex.I)).re := by
          conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I B]
          rw [expChar, mul_assoc, ← Complex.exp_add]
          push_cast
          ring_nf
      _ = _ := by simp [Complex.exp_re, Complex.mul_im, Complex.mul_re]
  have hB : B ≠ 0 := by
    intro hzero
    have hcircle := boundaryStep_circle_of_bounded_thetaRadial hΘ hb 0
    change D 0^2 + D (0+h)^2 = _ at hcircle
    simp only [hform, hzero, norm_zero, zero_mul, zero_pow two_ne_zero, add_zero] at hcircle
    exact (sq_pos_of_pos (quartetRadialCoeff_pos hγ hm)).ne' hcircle.symm
  exact ⟨q,‖B‖,B.arg,hq,norm_pos_iff.mpr hB,hform⟩

private theorem abs_sub_le_of_between {r t s : ℝ} (hr : r ∈ uIcc t s) :
    |r-s| ≤ |t-s| := by
  rcases mem_uIcc.mp hr with ⟨ht,hs⟩ | ⟨hs,ht⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr hs),abs_of_nonpos (sub_nonpos.mpr (ht.trans hs))]
    linarith only [ht]
  · rw [abs_of_nonneg (sub_nonneg.mpr hs),abs_of_nonneg (sub_nonneg.mpr (hs.trans ht))]
    exact sub_le_sub_right ht _

/-- The nearest crest of the absolute cosine is within half a lobe, and its
absolute value can only increase on the segment leading to that crest. -/
private theorem exists_cosine_crest {ω : ℝ} (hω : 0 < ω) (φ t : ℝ) :
    ∃ s : ℝ, |t-s| ≤ Real.pi/(2*ω) ∧ |Real.cos (ω*s+φ)| = 1 ∧
      ∀ r ∈ uIcc t s, |Real.cos (ω*t+φ)| ≤ |Real.cos (ω*r+φ)| := by
  let k := round ((ω*t+φ)/Real.pi)
  let s := ((k:ℝ)*Real.pi-φ)/ω
  have hcenter : ω*s+φ = k*Real.pi := by
    dsimp only [s]
    field_simp [hω.ne'] <;> ring
  have ht : |ω*(t-s)| ≤ Real.pi/2 := by
    have he : ω*(t-s) = ((ω*t+φ)/Real.pi-k)*Real.pi := by
      rw [sub_mul, div_mul_cancel₀ _ Real.pi_ne_zero]
      linarith only [hcenter]
    rw [he,abs_mul,abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_right (abs_sub_round _) Real.pi_pos.le).trans_eq (by ring)
  refine ⟨s,?_,by rw [hcenter, Real.abs_cos_int_mul_pi],?_⟩
  · rw [abs_mul,abs_of_pos hω] at ht
    apply (le_div_iff₀ (mul_pos zero_lt_two hω)).mpr
    linarith only [ht]
  intro r hr
  have hb : |ω*(r-s)| ≤ |ω*(t-s)| := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sub_le_of_between hr) (abs_nonneg ω)
  have hangle (x : ℝ) (hx : |ω*(x-s)| ≤ Real.pi/2) :
      |Real.cos (ω*x+φ)| = Real.cos |ω*(x-s)| := by
    rw [show ω*x+φ = ω*(x-s)+k*Real.pi by linarith only [hcenter],
      Real.cos_add_int_mul_pi,abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul,
      ← Real.cos_abs (ω*(x-s))]
    apply abs_of_nonneg
    exact Real.cos_nonneg_of_mem_Icc ⟨(neg_nonpos.mpr (half_pos Real.pi_pos).le).trans (abs_nonneg _),hx⟩
  rw [hangle t ht,hangle r (hb.trans ht)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (ht.trans (half_le_self Real.pi_pos.le)) hb

#print axioms exists_continuous_normalizedPrimeIncrement_approx
#print axioms exists_cosine_boundaryStep_of_bounded_thetaRadial

end GaloisForLFunctions.ExceptionalLayerTheory
