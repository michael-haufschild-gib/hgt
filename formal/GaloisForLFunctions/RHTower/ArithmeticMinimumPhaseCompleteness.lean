import GaloisForLFunctions.RHTower.ArithmeticZeroMinimumClasses
import GaloisForLFunctions.RHTower.ZetaRealStrip
import Mathlib.Analysis.Complex.OpenMapping

/-!
# The complex information omitted by arithmetic minimum balance

The normalized arithmetic remainder sum is the rational zero boundary minus the
conjugate of `ζ(s)/(s(s+1))`. Its real balance therefore tests only one real
component of the zeta value. The omitted imaginary component is retained exactly.

Every open-strip zeta zero has nonzero points satisfying that real balance in
every neighborhood. Moreover, any such zero forces an off-line nonzero point
satisfying the same balance. Both conclusions follow from analytic openness and
the coefficient-side negative sign of zeta on the real strip, with no assumption
on zero multiplicity. The real balance already supplies profile negativity and
minimum attainment below the decay exponent, even without a zero assumption.

Power tilting also orders any two attained profile minima independently of the
zero equation. None of these statements excludes off-line zeta zeros.
-/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The full rational boundary prescribed by a zeta zero. -/
def minimumZeroBoundary (s : ℂ) : ℂ := -(star s * (1 - star s))⁻¹ / 2

/-- The complex discrepancy between the actual arithmetic sum and its zero boundary. -/
def minimumComplexDefect (s : ℂ) : ℂ :=
  (∑' p : ℕ+, minimumBalanceTerm s p) - minimumZeroBoundary s

private theorem normalization_ne {s : ℂ} (hs : 0 < s.re) :
    minimumNormalization s ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have he := congrArg Complex.re h
    simp at he
    linarith
  · intro h
    have he := congrArg Complex.re h
    simp at he
    linarith

private theorem boundary_den_ne {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    star s * (1 - star s) ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.zero_re] at he
  have hp : 0 < s.re * (1 - s.re) := mul_pos hs (by linarith)
  nlinarith [sq_nonneg s.im]

/-- Exact arithmetic reconstruction with both real and imaginary zeta components retained. -/
theorem tsum_minimumBalanceTerm_eq {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    (∑' p : ℕ+, minimumBalanceTerm s p) = minimumZeroBoundary s -
      star (riemannZeta s / (s * (s + 1))) := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs'; norm_num at hs'
  have h0 := (mul_ne_zero_iff.1 (normalization_ne hs)).1
  have hp := (mul_ne_zero_iff.1 (normalization_ne hs)).2
  have hm := (mul_ne_zero_iff.1 (boundary_den_ne hs hs')).2
  simp only [minimumBalanceTerm, tsum_div_const]
  rw [moebius_infiniteRemainder_eq hs hs1]
  simp only [minimumZeroBoundary, minimumNormalization, star_div₀, star_mul,
    star_add, star_one]
  field_simp
  ring

/-- The full arithmetic discrepancy is the negative conjugate of the normalized zeta value. -/
theorem minimumComplexDefect_eq {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    minimumComplexDefect s = -star (riemannZeta s / (s * (s + 1))) := by
  rw [minimumComplexDefect, tsum_minimumBalanceTerm_eq hs hs']
  ring

/-- The real discrepancy records only the real component of the normalized zeta value. -/
theorem minimumComplexDefect_re_eq {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    (minimumComplexDefect s).re = -(riemannZeta s / (s * (s + 1))).re := by
  rw [minimumComplexDefect_eq hs hs']
  simp only [Complex.neg_re, Complex.star_def, Complex.conj_re]

/-- The omitted imaginary discrepancy is exactly the imaginary component of normalized zeta. -/
theorem minimumComplexDefect_im_eq {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    (minimumComplexDefect s).im = (riemannZeta s / (s * (s + 1))).im := by
  rw [minimumComplexDefect_eq hs hs']
  simp only [Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg]

/-- The full complex arithmetic discrepancy vanishes exactly at the actual zeta zeros. -/
theorem minimumComplexDefect_eq_zero_iff {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    minimumComplexDefect s = 0 ↔ riemannZeta s = 0 := by
  have hden : s * (s + 1) ≠ 0 := by
    intro h
    apply normalization_ne hs
    simpa only [minimumNormalization, star_mul, star_add, star_one, star_zero, mul_comm] using congrArg star h
  rw [minimumComplexDefect_eq hs hs']
  rw [neg_eq_zero, star_eq_zero, div_eq_zero_iff]
  simp only [hden, or_false]

/-- The real arithmetic balance is exactly the vanishing of one real projection of normalized zeta. -/
theorem real_minimum_balance_iff {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    (∑' p : ℕ+, minimumBalanceTerm s p).re = (minimumZeroBoundary s).re ↔
      (riemannZeta s / (s * (s + 1))).re = 0 := by
  rw [tsum_minimumBalanceTerm_eq hs hs']
  simp only [Complex.sub_re, Complex.star_def, Complex.conj_re]
  constructor <;> intro h <;> linarith

/-- The negative weighted profile identity needs only the real balance, not a zeta zero. -/
theorem tsum_minimumProfile_div_weight_of_real_balance {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1)
    (hb : (∑' p : ℕ+, minimumBalanceTerm s p).re = (minimumZeroBoundary s).re)
    (a : ℝ) :
    (∑' p : ℕ+, minimumProfile s a p / (p : ℝ) ^ (a + 1)) =
      -((star s * (1 - star s))⁻¹).re / 2 := by
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs'
  calc
    _ = (∑' p : ℕ+, minimumBalanceTerm s p).re := by
      rw [Complex.re_tsum (summable_minimumBalanceTerm hs hs1)]
      exact tsum_congr fun p => minimumProfile_div_weight s a p.pos
    _ = _ := by rw [hb]; simp [minimumZeroBoundary]

/-- Every profile has a negative entry whenever the projected arithmetic balance holds. -/
theorem exists_minimumProfile_neg_of_real_balance {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1)
    (hb : (∑' p : ℕ+, minimumBalanceTerm s p).re = (minimumZeroBoundary s).re)
    (a : ℝ) : ∃ p : ℕ, 0 < p ∧ minimumProfile s a p < 0 := by
  by_contra h
  push Not at h
  have hn := minimum_boundary_neg hs hs'
  rw [← tsum_minimumProfile_div_weight_of_real_balance hs hs' hb a] at hn
  have hnn : 0 ≤ ∑' p : ℕ+, minimumProfile s a p / (p : ℝ) ^ (a + 1) := by
    apply tsum_nonneg
    intro p
    exact div_nonneg (h p p.pos) (Real.rpow_nonneg (by positivity) _)
  linarith

/-- The projected balance already forces a finite negative minimum below the decay exponent. -/
theorem negativeMinimum_attained_of_real_balance {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1)
    (hb : (∑' p : ℕ+, minimumBalanceTerm s p).re = (minimumZeroBoundary s).re)
    {a : ℝ} (ha : a < 2 * s.re) :
    ∃ p, HasNegativeMinimum (minimumProfile s a) p := by
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs'
  exact exists_negativeMinimum_of_tendsto_zero (tendsto_minimumProfile hs hs1 ha)
    (exists_minimumProfile_neg_of_real_balance hs hs' hb a)

/-- The imaginary rational boundary retains the signed displacement from the critical line. -/
theorem minimumZeroBoundary_im (s : ℂ) :
    (minimumZeroBoundary s).im =
      s.im * (2 * s.re - 1) / (2 * Complex.normSq (star s * (1 - star s))) := by
  simp only [minimumZeroBoundary, Complex.div_ofNat_im, Complex.neg_im, Complex.inv_im,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- At a zeta zero, the exact imaginary arithmetic sum is proportional to horizontal displacement. -/
theorem tsum_minimumBalanceTerm_im_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s = 0) :
    (∑' p : ℕ+, minimumBalanceTerm s p).im =
      s.im * (2 * s.re - 1) / (2 * Complex.normSq (star s * (1 - star s))) := by
  rw [tsum_minimumBalanceTerm_eq hs hs', hz]
  simpa using minimumZeroBoundary_im s

/-- Changing the profile exponent is a literal power tilt of the same real arithmetic data. -/
theorem minimumProfile_eq_power_tilt (s : ℂ) (a b : ℝ) {p : ℕ} (hp : 0 < p) :
    minimumProfile s b p = (p : ℝ) ^ (b - a) * minimumProfile s a p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [minimumProfile, minimumProfile, ← mul_assoc, ← Real.rpow_add hp']
  congr 2
  ring

/-- A positive strictly increasing tilt cannot move an attained negative minimum to a smaller index. -/
theorem negative_minimum_order_of_strict_weight {f w : ℕ → ℝ} {p q : ℕ}
    (hp : HasNegativeMinimum f p)
    (hq : HasNegativeMinimum (fun n => w n * f n) q)
    (hw : ∀ n : ℕ, 0 < n → 0 < w n)
    (hmono : ∀ i j : ℕ, 0 < i → i < j → w i < w j) : p ≤ q := by
  by_contra hn
  have hqp : q < p := by omega
  have h1 : w p * f p < w q * f p :=
    mul_lt_mul_of_neg_right (hmono q p hq.1 hqp) hp.2.1
  have h2 : w q * f p ≤ w q * f q :=
    mul_le_mul_of_nonneg_left (hp.2.2 q hq.1) (hw q hq.1).le
  exact (not_lt_of_ge (hq.2.2 p hp.1)) (h1.trans_le h2)

/-- Increasing the exponent orders attained profile minima without using the zero equation. -/
theorem minimumProfile_minimum_order {s : ℂ} {a b : ℝ} (hab : a < b)
    {p q : ℕ} (hp : HasNegativeMinimum (minimumProfile s a) p)
    (hq : HasNegativeMinimum (minimumProfile s b) q) : p ≤ q := by
  apply negative_minimum_order_of_strict_weight hp
    (w := fun n => (n : ℝ) ^ (b - a))
  · refine ⟨hq.1, ?_, ?_⟩
    · simpa only [← minimumProfile_eq_power_tilt s a b hq.1] using hq.2.1
    · intro n hn
      simpa only [← minimumProfile_eq_power_tilt s a b hq.1,
        ← minimumProfile_eq_power_tilt s a b hn] using hq.2.2 n hn
  · intro n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  · intro i j hi hij
    exact Real.rpow_lt_rpow (by positivity) (by exact_mod_cast hij) (sub_pos.2 hab)

/-- The open critical strip, independent of the arithmetic class labels. -/
def minimumStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

/-- The holomorphic zeta normalization whose real projection is the minimum balance. -/
def normalizedMinimumZeta (s : ℂ) : ℂ := riemannZeta s / (s * (s + 1))

private theorem minimumStrip_open : IsOpen minimumStrip := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

private theorem normalizedMinimumZeta_analytic :
    AnalyticOnNhd ℂ normalizedMinimumZeta minimumStrip := by
  have hzeta : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun z hz =>
    (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  intro s hs
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num [minimumStrip] at hs
  have hden : s * (s + 1) ≠ 0 := by
    apply mul_ne_zero
    · intro h; subst s; norm_num [minimumStrip] at hs
    · intro h
      have hr := congrArg Complex.re h
      simp at hr
      have := hs.1
      linarith
  exact ((hzeta.analyticOnNhd isOpen_compl_singleton) s (by simpa using hs1)).div
    (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) hden

private theorem normalizedMinimumZeta_open_of_zero {ρ : ℂ}
    (hρ : ρ ∈ minimumStrip) (hz : riemannZeta ρ = 0) :
    ∀ V ⊆ minimumStrip, IsOpen V → IsOpen (normalizedMinimumZeta '' V) := by
  have hconn : IsPreconnected minimumStrip :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  rcases normalizedMinimumZeta_analytic.is_constant_or_isOpen hconn with hc | ho
  · obtain ⟨c, hc⟩ := hc
    have hc0 : c = 0 := by simpa [normalizedMinimumZeta, hz] using (hc ρ hρ).symm
    have ha := hc (1 / 2 : ℂ) (by norm_num [minimumStrip])
    rw [hc0] at ha
    have hn : riemannZeta (1 / 2 : ℂ) ≠ 0 := by
      simpa using RHTower.riemannZeta_real_strip_ne_zero
        (σ := 1 / 2) (by norm_num) (by norm_num)
    have hden : (1 / 2 : ℂ) * ((1 / 2 : ℂ) + 1) ≠ 0 := by norm_num
    change riemannZeta (1 / 2 : ℂ) / ((1 / 2 : ℂ) * ((1 / 2 : ℂ) + 1)) = 0 at ha
    exact False.elim (hn ((div_eq_zero_iff.1 ha).resolve_right hden))
  · exact ho

/-- Every strip zero has nonzero points satisfying the real arithmetic balance arbitrarily nearby. No simplicity assumption is used. -/
theorem exists_nearby_nonzero_real_minimum_balance {ρ : ℂ}
    (hρ : ρ ∈ minimumStrip) (hz : riemannZeta ρ = 0) {r : ℝ} (hr : 0 < r) :
    ∃ s : ℂ, s ∈ minimumStrip ∧ dist s ρ < r ∧ riemannZeta s ≠ 0 ∧
      (∑' p : ℕ+, minimumBalanceTerm s p).re = (minimumZeroBoundary s).re := by
  let V : Set ℂ := minimumStrip ∩ Metric.ball ρ r
  have hV : IsOpen V := minimumStrip_open.inter Metric.isOpen_ball
  have hρV : ρ ∈ V := ⟨hρ, Metric.mem_ball_self hr⟩
  have hopen : IsOpen (normalizedMinimumZeta '' V) :=
    normalizedMinimumZeta_open_of_zero hρ hz V Set.inter_subset_left hV
  have hzero : (0 : ℂ) ∈ normalizedMinimumZeta '' V :=
    ⟨ρ, hρV, by simp [normalizedMinimumZeta, hz]⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 hzero
  have himg : ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ normalizedMinimumZeta '' V := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨s, hs, he⟩ := himg
  refine ⟨s, hs.1, hs.2, ?_, (real_minimum_balance_iff hs.1.1 hs.1.2).2 ?_⟩
  · intro hzs
    have him := congrArg Complex.im he
    simp [normalizedMinimumZeta, hzs] at him
    linarith
  · have hre := congrArg Complex.re he
    simpa only [normalizedMinimumZeta, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero] using hre

private theorem exists_offline_positive_normalizedMinimumZeta {ρ : ℂ}
    (hρ : ρ ∈ minimumStrip) (hz : riemannZeta ρ = 0) :
    ∃ w : ℂ, w ∈ minimumStrip ∧ w.re ≠ 1 / 2 ∧ 0 < (normalizedMinimumZeta w).re := by
  have hopen := normalizedMinimumZeta_open_of_zero hρ hz minimumStrip
    (Set.Subset.refl _) minimumStrip_open
  have hzero : (0 : ℂ) ∈ normalizedMinimumZeta '' minimumStrip :=
    ⟨ρ, hρ, by simp [normalizedMinimumZeta, hz]⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 hzero
  have himg : ((ε / 2 : ℝ) : ℂ) ∈ normalizedMinimumZeta '' minimumStrip := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨w, hw, he⟩ := himg
  have hwpos : 0 < (normalizedMinimumZeta w).re := by rw [he]; exact half_pos hε
  by_cases hwline : w.re = 1 / 2
  · let A : Set ℂ := minimumStrip ∩ (fun z => (normalizedMinimumZeta z).re) ⁻¹' Set.Ioi 0
    have hA : IsOpen A :=
      (Complex.continuous_re.comp_continuousOn normalizedMinimumZeta_analytic.continuousOn).isOpen_inter_preimage minimumStrip_open isOpen_Ioi
    obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.1 hA w ⟨hw, hwpos⟩
    have hx : w + ((δ / 2 : ℝ) : ℂ) ∈ A := by
      apply hδball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
      linarith
    refine ⟨_, hx.1, ?_, hx.2⟩
    simp only [Complex.add_re, Complex.ofReal_re, hwline]
    linarith
  · exact ⟨w, hw, hwline, hwpos⟩

private theorem normalizedMinimumZeta_real_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (normalizedMinimumZeta (σ : ℂ)).re < 0 := by
  obtain ⟨x, hx, he⟩ := RHTower.riemannZeta_real_strip_neg h0 h1
  rw [normalizedMinimumZeta, he]
  have hform : (x : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1)) =
      ((x / (σ * (σ + 1)) : ℝ) : ℂ) := by push_cast; rfl
  rw [hform, Complex.ofReal_re]
  exact div_neg_of_neg_of_pos hx (mul_pos h0 (by linarith))

/-- Any strip zero forces an off-line nonzero point satisfying the exact real arithmetic balance. The proof uses analytic openness and a vertical intermediate value argument. -/
theorem exists_offline_nonzero_real_minimum_balance_of_zero {ρ : ℂ}
    (hρ : ρ ∈ minimumStrip) (hz : riemannZeta ρ = 0) :
    ∃ s : ℂ, s ∈ minimumStrip ∧ s.re ≠ 1 / 2 ∧ riemannZeta s ≠ 0 ∧
      (∑' p : ℕ+, minimumBalanceTerm s p).re = (minimumZeroBoundary s).re := by
  obtain ⟨w, hw, hwline, hwpos⟩ := exists_offline_positive_normalizedMinimumZeta hρ hz
  let v : ℝ → ℂ := fun t => (w.re : ℂ) + (t : ℂ) * Complex.I
  have hv (t : ℝ) : v t ∈ minimumStrip := by simpa [v, minimumStrip] using hw
  have hvcont : Continuous v := by fun_prop
  have hfcont : Continuous (fun t : ℝ => (normalizedMinimumZeta (v t)).re) := by
    apply Complex.continuous_re.comp
    apply continuous_iff_continuousAt.2
    intro t
    exact (normalizedMinimumZeta_analytic (v t) (hv t)).continuousAt.comp hvcont.continuousAt
  have h0 : (normalizedMinimumZeta (v 0)).re ≤ 0 := by
    simpa [v] using (normalizedMinimumZeta_real_neg hw.1 hw.2).le
  have h1 : 0 ≤ (normalizedMinimumZeta (v w.im)).re := by
    simpa only [v, Complex.re_add_im] using hwpos.le
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : ℝ) w.im hfcont ⟨h0, h1⟩
  have hre : (v t).re = w.re := by simp [v]
  by_cases hzv : riemannZeta (v t) = 0
  · have hgap : 0 < |w.re - 1 / 2| := abs_pos.2 (sub_ne_zero.2 hwline)
    obtain ⟨s, hs, hdist, hzs, hbal⟩ := exists_nearby_nonzero_real_minimum_balance
      (hv t) hzv (r := |w.re - 1 / 2| / 2) (half_pos hgap)
    refine ⟨s, hs, ?_, hzs, hbal⟩
    intro hsline
    have hbound : |s.re - (v t).re| ≤ dist s (v t) := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - v t)
    rw [hsline, hre, abs_sub_comm] at hbound
    linarith
  · refine ⟨v t, hv t, ?_, hzv, (real_minimum_balance_iff (hv t).1 (hv t).2).2 ht⟩
    simpa only [hre] using hwline

end RHTower.DeletionMixedRefinement
