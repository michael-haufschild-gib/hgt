import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorQuotientMellin
import GaloisForLFunctions.HTGeometry.FinitePoleVerticalContourShift

/-!
# Actual finite-pole Mellin contour transport

The exact deficit polynomial determines all possible interior poles. Analyticity
on the boundary, absolute integrability and vanishing horizontal sides follow
from the cubic datum and its checked rapid tails. Every Laurent order is retained.
-/

noncomputable section

open Complex Set Filter MeasureTheory Topology Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

/-- All possible poles of the completed degree-two quotient. -/
def degreeTwoPoleSet (P : Polynomial ℂ) : Finset ℂ :=
  P.roots.toFinset ∪ {0, 1}

private lemma xi_ne_zero_left {s : ℂ} (hs : s.re ≤ -1) : xi s ≠ 0 := by
  have hr : 1 < (1 - s).re := by simp only [sub_re, one_re]; linarith
  have hr0 : 0 < (1 - s).re := by linarith
  have h0 : (1 : ℂ) - s ≠ 0 := by intro h; norm_num [h] at hr
  have h1 : (1 : ℂ) - s ≠ 1 := by intro h; norm_num [h] at hr
  have he := MaassZetaSquaredConverse.two_xi_eq hr0 h1
  rw [xi_one_sub] at he
  intro hz
  rw [hz, mul_zero] at he
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    (Complex.Gammaℝ_ne_zero_of_re_pos hr0)) (riemannZeta_ne_zero_of_one_lt_re hr)) he.symm

/-- Exact orders prevent the clearing polynomial from acquiring left-hand roots. -/
theorem deficitPolynomial_ne_zero_left {E : ℂ → ℂ} (P : Polynomial ℂ)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {s : ℂ} (hs : s.re ≤ -1) : P.eval s ≠ 0 := by
  have hxiord : analyticOrderAt xi s = 0 :=
    (xi_analyticOnNhd_univ s (mem_univ _)).analyticOrderAt_eq_zero.mpr (xi_ne_zero_left hs)
  have hd : xiDeficit E s = 0 := by simp [xiDeficit, analyticOrderNatAt, hxiord]
  apply (P.differentiable.differentiableOn.analyticAt
    (s := univ) Filter.univ_mem).analyticOrderAt_eq_zero.mp
  rw [hord s, hd, Nat.cast_zero]

/-- All possible poles lie strictly inside the two contour lines. -/
theorem degreeTwoPoleSet_re {E : ℂ → ℂ} (P : Polynomial ℂ)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {s : ℂ} (hs : s ∈ degreeTwoPoleSet P) : -1 < s.re ∧ s.re < 2 := by
  rcases Finset.mem_union.mp hs with hp | he
  · have hzero : P.eval s = 0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hp)
    constructor
    · by_contra h
      exact deficitPolynomial_ne_zero_left P hord (le_of_not_gt h) hzero
    · by_contra h
      exact deficitPolynomial_ne_zero_right P hord (le_of_not_gt h) hzero
  · simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> norm_num

/-- Analyticity off the explicitly finite pole set, with removable values already repaired. -/
theorem poleClearedDegreeTwoCompletion_analyticAt_off (P : Polynomial ℂ) (hP : P ≠ 0)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) {s : ℂ} (hs : s ∉ degreeTwoPoleSet P) :
    AnalyticAt ℂ (poleClearedDegreeTwoCompletion P H) s := by
  have hroots : s ∉ P.roots := by
    intro hr
    exact hs (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hr))
  have hp : P.eval s ≠ 0 := by
    intro hz
    exact hroots ((Polynomial.mem_roots hP).mpr hz)
  have h0 : s ≠ 0 := by intro h; subst s; exact hs (by simp [degreeTwoPoleSet])
  have h1 : s ≠ 1 := by intro h; subst s; exact hs (by simp [degreeTwoPoleSet])
  exact poleClearedDegreeTwoCompletion_analyticAt P hH hp h0 h1

private lemma line_decay_of_tail {F : ℝ → ℂ} (hF : Continuous F) {T C : ℝ}
    (htail : ∀ t : ℝ, T ≤ |t| → ‖F t‖ ≤ C / (1 + |t|) ^ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖F t‖ ≤ B / (1 + t ^ 2) := by
  have hc : Continuous (fun t : ℝ => ((1 + t ^ 2 : ℝ) : ℂ) * F t) := by fun_prop
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-T) T) hc.continuousOn
  refine ⟨max 0 (max M C), le_max_left _ _, fun t => ?_⟩
  rw [le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  by_cases ht : T ≤ |t|
  · have h := (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 2)).mp (htail t ht)
    have hab : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    exact ((mul_le_mul_of_nonneg_left hab (norm_nonneg _)).trans h).trans
      ((le_max_right M C).trans (le_max_right 0 _))
  · have hm := hM t (abs_le.mp (le_of_lt (lt_of_not_ge ht)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + t ^ 2)] at hm
    exact (by simpa [mul_comm] using hm : ‖F t‖ * (1 + t ^ 2) ≤ M).trans
      ((le_max_left M C).trans (le_max_right 0 _))

/-- Both actual boundary lines are absolutely integrable, including their inverse-Mellin weights. -/
theorem poleClearedDegreeTwoCompletion_integrable_line {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P : Polynomial ℂ) (hP : P ≠ 0)
    (hH : Differentiable ℂ H) (hHfinite : FiniteOrderEnvelope H)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {σ x : ℝ} (hσ : σ = -1 ∨ σ = 2) (hx : 0 < x) :
    Integrable fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
      poleClearedDegreeTwoCompletion P H ((σ : ℂ) + t * I) := by
  have hσa : -1 ≤ σ := by rcases hσ with rfl | rfl <;> norm_num
  have hσb : σ ≤ 2 := by rcases hσ with rfl | rfl <;> norm_num
  have hana : ∀ t : ℝ, AnalyticAt ℂ (poleClearedDegreeTwoCompletion P H) ((σ : ℂ) + t * I) := by
    intro t
    apply poleClearedDegreeTwoCompletion_analyticAt_off P hP hH
    intro ht
    have hr := degreeTwoPoleSet_re P hord ht
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_self, add_zero] at hr
    rcases hσ with rfl | rfl <;> linarith [hr.1, hr.2]
  have hcont : Continuous fun t : ℝ => poleClearedDegreeTwoCompletion P H ((σ : ℂ) + t * I) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (f := fun u : ℝ => (σ : ℂ) + u * I)
        (g := poleClearedDegreeTwoCompletion P H) (x := t) (hana t).continuousAt (by fun_prop)
  obtain ⟨T, _, htail⟩ := poleClearedDegreeTwoCompletion_rapid_tail hD P hP hH hHfinite hfac
  obtain ⟨C, hC, hc⟩ := htail 2
  obtain ⟨B, hB, hb⟩ := line_decay_of_tail hcont (T := T) (fun t ht => by
    simpa using hc ((σ : ℂ) + t * I) (by simpa using hσa) (by simpa using hσb) (by simpa using ht))
  have hcontw : Continuous fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
      poleClearedDegreeTwoCompletion P H ((σ : ℂ) + t * I) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))).mul hcont
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (x ^ (-σ) * B))
    hcontw.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    mul_one, sub_self, add_zero]
  calc
    x ^ (-σ) * ‖poleClearedDegreeTwoCompletion P H ((σ : ℂ) + t * I)‖ ≤
        x ^ (-σ) * (B / (1 + t ^ 2)) := mul_le_mul_of_nonneg_left (hb t) (by positivity)
    _ = (x ^ (-σ) * B) * (1 + t ^ 2)⁻¹ := by ring

/-- The actual inverse-Mellin horizontal sides vanish; no bound through the poles is assumed. -/
theorem poleClearedDegreeTwoCompletion_horizontal_tendsto {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P : Polynomial ℂ) (hP : P ≠ 0)
    (hH : Differentiable ℂ H) (hHfinite : FiniteOrderEnvelope H)
    (hfac : ∀ z, P.eval z * E z = H z * xi z) {x : ℝ} (hx : 0 < x)
    {h : ℝ → ℝ} (hh : ∀ T, |h T| = |T|) :
    Tendsto (fun T : ℝ => HIntegral
      (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) (-1) 2 (h T))
      atTop (𝓝 0) := by
  obtain ⟨T₀, hT₀, htail⟩ := poleClearedDegreeTwoCompletion_rapid_tail hD P hP hH hHfinite hfac
  obtain ⟨C, hC, hc⟩ := htail 2
  have hbound : ∀ᶠ T : ℝ in atTop, ‖HIntegral
      (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) (-1) 2 (h T)‖ ≤
      (x ^ (1 : ℝ) + x ^ (-2 : ℝ)) * (C / (1 + T ^ 2)) * |(2 : ℝ) - (-1)| := by
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hTpos : 0 ≤ T := by linarith
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hu
    have hb := hc ((u : ℂ) + (h T : ℂ) * I) (by simpa using hu.1.le)
      (by simpa using hu.2) (by simpa [hh, abs_of_nonneg hTpos] using hT)
    have hb' : ‖poleClearedDegreeTwoCompletion P H ((u : ℂ) + (h T : ℂ) * I)‖ ≤
        C / (1 + T ^ 2) := by
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
        mul_zero, add_zero, zero_add, hh, abs_of_nonneg hTpos] at hb
      refine hb.trans (div_le_div_of_nonneg_left hC (by positivity) ?_)
      nlinarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (-((u : ℂ) + (h T : ℂ) * I)).re = -u := by simp
    rw [hre]
    have hxpow : x ^ (-u) ≤ x ^ (1 : ℝ) + x ^ (-2 : ℝ) := by
      rcases le_total 1 x with h1 | h1
      · have hp := Real.rpow_le_rpow_of_exponent_le h1 (show -u ≤ (1 : ℝ) by linarith [hu.1])
        exact hp.trans (le_add_of_nonneg_right (le_of_lt (Real.rpow_pos_of_pos hx (-2))))
      · have hp := Real.rpow_le_rpow_of_exponent_ge hx h1 (show (-2 : ℝ) ≤ -u by linarith [hu.2])
        exact hp.trans (le_add_of_nonneg_left (le_of_lt (Real.rpow_pos_of_pos hx 1)))
    exact mul_le_mul hxpow hb' (norm_nonneg _) (by positivity)
  have hlim : Tendsto (fun T : ℝ =>
      (x ^ (1 : ℝ) + x ^ (-2 : ℝ)) * (C / (1 + T ^ 2)) * |(2 : ℝ) - (-1)|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => 1 + T ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
    have h2 : Tendsto (fun T : ℝ => C / (1 + T ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h1
    simpa using (h2.const_mul (x ^ (1 : ℝ) + x ^ (-2 : ℝ))).mul_const |(2 : ℝ) - (-1)|
  exact squeeze_zero_norm' hbound hlim

/-- The actual contour shift, retaining residues at every possible pole of every order. -/
theorem poleClearedDegreeTwoCompletion_contour_shift {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P : Polynomial ℂ) (hP : P ≠ 0)
    (hH : Differentiable ℂ H) (hHfinite : FiniteOrderEnvelope H)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ, (x : ℂ) ^ (-(2 + t * I)) * poleClearedDegreeTwoCompletion P H (2 + t * I)) -
        (∫ t : ℝ, (x : ℂ) ^ (-(-1 + t * I)) * poleClearedDegreeTwoCompletion P H (-1 + t * I)) =
      2 * (Real.pi : ℂ) * ∑ p ∈ degreeTwoPoleSet P,
        laurentCoeff (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) p (-1) := by
  have hpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  have hpowA : ∀ s, AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ (-s)) s :=
    fun _ => hpow.differentiableOn.analyticAt Filter.univ_mem
  have htop := poleClearedDegreeTwoCompletion_horizontal_tendsto hD P hP hH hHfinite hfac hx
    (h := fun T => T) (fun _ => rfl)
  have hbot := poleClearedDegreeTwoCompletion_horizontal_tendsto hD P hP hH hHfinite hfac hx
    (h := fun T => -T) (fun _ => abs_neg _)
  simpa using verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq
    (f := fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s)
    (a := -1) (c := 2) (P := degreeTwoPoleSet P) (by norm_num)
    (fun _ hp => degreeTwoPoleSet_re P hord hp)
    (fun p _ => (hpowA p).meromorphicAt.mul (poleClearedDegreeTwoCompletion_meromorphicAt P hH p))
    (fun s _ _ hp => (hpowA s).mul (poleClearedDegreeTwoCompletion_analyticAt_off P hP hH hp))
    (poleClearedDegreeTwoCompletion_integrable_line hD P hP hH hHfinite hfac hord (Or.inl rfl) hx)
    (poleClearedDegreeTwoCompletion_integrable_line hD P hP hH hHfinite hfac hord (Or.inr rfl) hx)
    (T := fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop
    (htop.comp tendsto_natCast_atTop_atTop) (hbot.comp tendsto_natCast_atTop_atTop)

end RHTower.WeilHigherDenominator
