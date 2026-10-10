import GaloisForLFunctions.RHTower.XiGaussianHeatGramIndexInfinite

/-!
# The arch−prime Hankel form and its Hodge-index law

The heat moments `M_n(τ) = Σ_q w_q^n e^{-τ w_q}` are, up to sign, the derivatives of the zero heat
trace: `ν^{(n)} = (−1)^n M_n` on `Re τ > 0`.  Differentiating the three-term formula
`π ν = Arch + 2π e^{τ/4} − Prime` gives the arithmetic moments

`w_n(a) = (−1)^n (Arch − Prime)^{(n)}(a) / π = M_n(a) − 2 (−1/4)^n e^{a/4}`
(`archPrimeMoment_eq`).

The pole is a point mass at `λ = −¼` with positive weight `2e^{a/4}`.  The arch−prime Hankel form
`W_a(P) = Σ_{k,l} p_k \overline{p_l} w_{k+l}(a)` therefore satisfies

`W_a(P) = H_a(P) − 2 e^{a/4} |P(−¼)|²`   (`archPrimeHankel_eq`).

**Theorem** (`archPrimeHankel_negativeIndex_eq_card_add_one`, `archPrimeHankel_negative_of_infinite`).
The negative index of `W_a` is `1 + #U` (in `ℕ ∪ {∞}`), where `U` is the set of off-line zero
quadruples.  This is a Hodge-index law: the pole plays the ample class, and RH holds iff `W_a` has
exactly one negative square, iff `W_a ⪰ 0` on the hyperplane `P(−¼) = 0`
(`riemannHypothesis_iff_archPrimeHankel_nonneg_of_eval_neg_quarter`).

The extra negative direction is `K/K(−¼)`, where `K` vanishes at every frequency with `Re w ≤ Λ`.
Its value at the pole is `1`, while its heat Hankel mass is a tail that tends to `0` as `Λ → ∞`.
-/

open Complex Filter Topology Set Polynomial

namespace RHTower

noncomputable section

/-! ## Heat moments and the derivatives of the three-term formula -/

/-- The heat moment `M_n(τ) = Σ_q w_q^n e^{-τ w_q}`. -/
def xiHeatMoment (n : ℕ) (τ : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, xiHeatFrequency q ^ n * Complex.exp (-τ * xiHeatFrequency q)

theorem xiHeatMoment_zero (τ : ℂ) : xiHeatMoment 0 τ = xiGaussianHeatTraceC τ := by
  simp [xiHeatMoment, xiGaussianHeatTraceC, xiGaussianHeatTermC_eq_exp]

theorem abs_im_xiHeatFrequency_le (q : XiZeroCopy) :
    |(xiHeatFrequency q).im| ≤ |(xiSpectralPoint q).re| := by
  rw [xiHeatFrequency_im]
  have h := xiSpectralPoint_im_sq_lt_quarter q
  have him : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
    have : (xiSpectralPoint q).im ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith
    exact abs_le_of_sq_le_sq' this (by norm_num) |> fun h => abs_le.2 h
  rw [abs_mul, abs_mul, abs_two]
  nlinarith [abs_nonneg (xiSpectralPoint q).re]

/-- The heat factor on a bounded half-strip is absorbed by half of the real part. -/
theorem norm_exp_neg_mul_xiHeatFrequency_le {b B R : ℝ} (hb : 0 < b) {τ : ℂ} (h1 : b < τ.re)
    (h2 : τ.re < B) (h3 : |τ.im| < R) (q : XiZeroCopy) :
    ‖Complex.exp (-τ * xiHeatFrequency q)‖ ≤
      Real.exp (B / 4 + b / 8 + R ^ 2 / (2 * b)) * Real.exp (-(b / 2 * (xiHeatFrequency q).re)) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.2
  set w := xiHeatFrequency q with hw
  set γ := (xiSpectralPoint q).re with hγ
  have hre : (-τ * w).re = -(τ.re * w.re) + τ.im * w.im := by simp [Complex.mul_re]; ring
  rw [hre]
  have hwre : w.re = γ ^ 2 - (xiSpectralPoint q).im ^ 2 := xiHeatFrequency_re q
  have him4 := xiSpectralPoint_im_sq_lt_quarter q
  have hwlow : -(1 / 4) < w.re := neg_quarter_lt_re_xiHeatFrequency q
  have hγ2 : γ ^ 2 ≤ w.re + 1 / 4 := by rw [hwre]; linarith
  have himw := abs_im_xiHeatFrequency_le q
  rw [← hγ] at himw
  have hR0 : 0 ≤ R := (abs_nonneg _).trans h3.le
  have hA : τ.im * w.im ≤ R * |γ| := by
    calc τ.im * w.im ≤ |τ.im * w.im| := le_abs_self _
      _ = |τ.im| * |w.im| := abs_mul _ _
      _ ≤ R * |γ| := mul_le_mul h3.le himw (abs_nonneg _) hR0
  have hB : R * |γ| ≤ b / 2 * γ ^ 2 + R ^ 2 / (2 * b) := by
    have hγsq : |γ| ^ 2 = γ ^ 2 := sq_abs γ
    have key : b / 2 * γ ^ 2 + R ^ 2 / (2 * b) - R * |γ| = (b * |γ| - R) ^ 2 / (2 * b) := by
      rw [← hγsq]
      field_simp
      ring
    have : 0 ≤ (b * |γ| - R) ^ 2 / (2 * b) := by positivity
    linarith
  have hC : -(τ.re * w.re) ≤ -(b * w.re) + B / 4 := by
    rcases le_or_gt 0 w.re with h | h
    · nlinarith
    · nlinarith
  nlinarith

/-- **The moments differentiate into each other.** -/
theorem hasDerivAt_xiHeatMoment (n : ℕ) {τ₀ : ℂ} (h : 0 < τ₀.re) :
    HasDerivAt (xiHeatMoment n) (-xiHeatMoment (n + 1) τ₀) τ₀ := by
  set b : ℝ := τ₀.re / 2 with hbdef
  set B : ℝ := τ₀.re + 1 with hBdef
  set R : ℝ := |τ₀.im| + 1 with hRdef
  have hb : 0 < b := by positivity
  set U : Set ℂ := ({τ | b < τ.re} ∩ {τ | τ.re < B}) ∩ {τ | |τ.im| < R}
  have hU : IsOpen U :=
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)).inter
      (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)
  have hmem : τ₀ ∈ U := ⟨⟨by simp only [mem_setOf_eq]; linarith, by simp only [mem_setOf_eq]; linarith⟩,
    by simp only [mem_setOf_eq, R]; linarith⟩
  set F : XiZeroCopy → ℂ → ℂ := fun q τ =>
    xiHeatFrequency q ^ n * Complex.exp (-τ * xiHeatFrequency q) with hF
  set K : ℝ := Real.exp (B / 4 + b / 8 + R ^ 2 / (2 * b)) with hK
  have hbound : ∀ (q : XiZeroCopy) (τ : ℂ), τ ∈ U → ‖F q τ‖ ≤
      K * ((1 + ‖xiHeatFrequency q‖) ^ n * Real.exp (-(b / 2 * (xiHeatFrequency q).re))) := by
    intro q τ hτU
    have he := norm_exp_neg_mul_xiHeatFrequency_le hb hτU.1.1 hτU.1.2 hτU.2 q
    have hp : ‖xiHeatFrequency q ^ n‖ ≤ (1 + ‖xiHeatFrequency q‖) ^ n := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
    simp only [F]
    rw [norm_mul]
    calc ‖xiHeatFrequency q ^ n‖ * ‖Complex.exp (-τ * xiHeatFrequency q)‖
        ≤ (1 + ‖xiHeatFrequency q‖) ^ n *
            (K * Real.exp (-(b / 2 * (xiHeatFrequency q).re))) :=
          mul_le_mul hp he (norm_nonneg _) (by positivity)
      _ = K * ((1 + ‖xiHeatFrequency q‖) ^ n * Real.exp (-(b / 2 * (xiHeatFrequency q).re))) := by
          ring
  have hdiff : ∀ q : XiZeroCopy, DifferentiableOn ℂ (F q) U := fun q => by
    simp only [F]
    fun_prop
  have hsum := (summable_one_add_norm_pow_mul_exp (by positivity : 0 < b / 2) n).mul_left K
  have hD := Complex.differentiableOn_tsum_of_summable_norm hsum hdiff hU hbound
  have hDer := Complex.hasSum_deriv_of_summable_norm hsum hdiff hU hbound hmem
  have hderiv : ∀ q : XiZeroCopy, deriv (F q) τ₀ =
      -(xiHeatFrequency q ^ (n + 1) * Complex.exp (-τ₀ * xiHeatFrequency q)) := by
    intro q
    have hd : HasDerivAt (F q) (xiHeatFrequency q ^ n *
        (Complex.exp (-τ₀ * xiHeatFrequency q) * (-xiHeatFrequency q))) τ₀ := by
      simp only [F]
      refine HasDerivAt.const_mul _ ?_
      have h1 : HasDerivAt (fun τ : ℂ => -τ * xiHeatFrequency q) (-xiHeatFrequency q) τ₀ := by
        simpa using ((hasDerivAt_id τ₀).neg.mul_const (xiHeatFrequency q))
      exact h1.cexp
    rw [hd.deriv]
    ring
  have hP : deriv (xiHeatMoment n) τ₀ = -xiHeatMoment (n + 1) τ₀ := by
    have h1 := hDer.tsum_eq
    rw [show (fun w => ∑' (i : XiZeroCopy), F i w) = xiHeatMoment n from rfl] at h1
    rw [← h1, tsum_congr hderiv, tsum_neg, xiHeatMoment]
  rw [← hP]
  exact (hD.differentiableAt (hU.mem_nhds hmem)).hasDerivAt

theorem gaussianArchPoleC_eq (τ : ℂ) :
    gaussianArchPoleC τ = 2 * Real.pi * Complex.exp (τ / 4) := by
  rw [gaussianArchPoleC, xiMassArchPole]
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Derivatives of the arch−prime part.**  On `Re τ > 0`,
`(Arch − Prime)^{(n)}(τ) = π (−1)^n M_n(τ) − 2π (1/4)^n e^{τ/4}`. -/
theorem iteratedDeriv_arch_sub_prime (n : ℕ) {τ : ℂ} (hτ : 0 < τ.re) :
    iteratedDeriv n (fun σ => gaussianArchCriticalC σ - gaussianPrimeChirpC σ) τ =
      (Real.pi : ℂ) * (-1) ^ n * xiHeatMoment n τ -
        2 * Real.pi * (1 / 4 : ℂ) ^ n * Complex.exp (τ / 4) := by
  have hH : IsOpen {σ : ℂ | 0 < σ.re} := isOpen_lt continuous_const continuous_re
  induction n generalizing τ with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, mul_one, xiHeatMoment_zero]
    have h := pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime hτ
    rw [gaussianArchPoleC_eq] at h
    linear_combination -h
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun σ => gaussianArchCriticalC σ - gaussianPrimeChirpC σ) =ᶠ[𝓝 τ]
        fun σ => (Real.pi : ℂ) * (-1) ^ n * xiHeatMoment n σ -
          2 * Real.pi * (1 / 4 : ℂ) ^ n * Complex.exp (σ / 4) := by
      filter_upwards [hH.mem_nhds hτ] with σ hσ
      exact ih hσ
    rw [heq.deriv_eq]
    have hd : HasDerivAt (fun σ => (Real.pi : ℂ) * (-1) ^ n * xiHeatMoment n σ -
        2 * Real.pi * (1 / 4 : ℂ) ^ n * Complex.exp (σ / 4))
        ((Real.pi : ℂ) * (-1) ^ n * (-xiHeatMoment (n + 1) τ) -
          2 * Real.pi * (1 / 4 : ℂ) ^ n * (Complex.exp (τ / 4) * (1 / 4))) τ := by
      refine ((hasDerivAt_xiHeatMoment n hτ).const_mul _).sub (HasDerivAt.const_mul _ ?_)
      have h1 : HasDerivAt (fun σ : ℂ => σ / 4) (1 / 4) τ := by
        simpa using (hasDerivAt_id τ).div_const 4
      exact h1.cexp
    rw [hd.deriv]
    ring

/-! ## Moment form of the Hankel forms -/

/-- The arithmetic moments `w_n(a) = (−1)^n (Arch − Prime)^{(n)}(a)/π`. -/
def archPrimeMoment (n : ℕ) (a : ℝ) : ℂ :=
  (-1) ^ n * iteratedDeriv n (fun σ => gaussianArchCriticalC σ - gaussianPrimeChirpC σ) (a : ℂ) /
    Real.pi

theorem archPrimeMoment_eq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    archPrimeMoment n a = xiHeatMoment n a - 2 * (-1 / 4 : ℂ) ^ n * Complex.exp ((a : ℂ) / 4) := by
  rw [archPrimeMoment, iteratedDeriv_arch_sub_prime n (by simpa using ha)]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpow : (-1 / 4 : ℂ) ^ n = (-1) ^ n * (1 / 4) ^ n := by rw [← mul_pow]; norm_num
  have hsq : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [hpow, div_eq_iff hπ]
  linear_combination (Real.pi : ℂ) * xiHeatMoment n a * hsq

theorem summable_pow_mul_exp_xiHeatFrequency {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Summable fun q : XiZeroCopy =>
      xiHeatFrequency q ^ n * Complex.exp (-(a : ℂ) * xiHeatFrequency q) := by
  refine Summable.of_norm ((summable_one_add_norm_pow_mul_exp ha n).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun q => ?_)
  rw [norm_mul, norm_pow, Complex.norm_exp]
  have hre : (-(a : ℂ) * xiHeatFrequency q).re = -(a * (xiHeatFrequency q).re) := by simp
  rw [hre]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (by linarith) n)
    (Real.exp_pos _).le

/-- **The heat Hankel form is the Hankel form of the heat moments.** -/
theorem heatHankel_eq_moments {a : ℝ} (ha : 0 < a) (P R : ℂ[X]) :
    heatHankel a P R =
      P.sum fun k p => R.sum fun l r => p * (starRingEnd ℂ) r * xiHeatMoment (k + l) a := by
  have hterm : ∀ w : ℂ, heatHankelTermAt a P R w = P.sum fun k p => R.sum fun l r =>
      p * (starRingEnd ℂ) r * (w ^ (k + l) * Complex.exp (-(a : ℂ) * w)) := by
    intro w
    rw [heatHankelTermAt, Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def,
      Polynomial.sum_def, Polynomial.sum_def, map_sum, mul_assoc, Finset.sum_mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.sum_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_pow, Complex.conj_conj, pow_add]
    ring
  rw [heatHankel]
  simp only [hterm, Polynomial.sum_def]
  rw [Summable.tsum_finsetSum fun k _ => summable_sum fun l _ =>
    (summable_pow_mul_exp_xiHeatFrequency ha (k + l)).mul_left _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Summable.tsum_finsetSum fun l _ => (summable_pow_mul_exp_xiHeatFrequency ha (k + l)).mul_left _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tsum_mul_left, xiHeatMoment]

/-- The arch−prime Hankel form `W_a(P, R) = Σ_{k,l} p_k \overline{r_l} w_{k+l}(a)`. -/
def archPrimeHankel (a : ℝ) (P R : ℂ[X]) : ℂ :=
  P.sum fun k p => R.sum fun l r => p * (starRingEnd ℂ) r * archPrimeMoment (k + l) a

/-- **Pole decomposition.**  `W_a(P, R) = H_a(P, R) − 2 e^{a/4} P(−¼) \overline{R(−¼)}`. -/
theorem archPrimeHankel_eq {a : ℝ} (ha : 0 < a) (P R : ℂ[X]) :
    archPrimeHankel a P R = heatHankel a P R -
      2 * Complex.exp ((a : ℂ) / 4) * P.eval (-1 / 4) * (starRingEnd ℂ) (R.eval (-1 / 4)) := by
  have hc : (starRingEnd ℂ) (-1 / 4 : ℂ) = -1 / 4 := by
    rw [map_div₀, map_neg, map_one, map_ofNat]
  have hpole : 2 * Complex.exp ((a : ℂ) / 4) * P.eval (-1 / 4) * (starRingEnd ℂ) (R.eval (-1 / 4)) =
      ∑ k ∈ P.support, ∑ l ∈ R.support, P.coeff k * (starRingEnd ℂ) (R.coeff l) *
        (2 * (-1 / 4 : ℂ) ^ (k + l) * Complex.exp ((a : ℂ) / 4)) := by
    rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.sum_def,
      map_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_pow, hc, pow_add]
    ring
  rw [heatHankel_eq_moments ha, archPrimeHankel, hpole]
  simp only [Polynomial.sum_def, archPrimeMoment_eq ha]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ## The pole member -/

/-- `W_a` on a combination: the heat Hankel form minus the pole square. -/
theorem archPrimeHankel_sum_sum {a : ℝ} (ha : 0 < a) {ι : Type*} [Fintype ι] (P : ι → ℂ[X])
    (x : ι → ℂ) : archPrimeHankel a (∑ i, x i • P i) (∑ i, x i • P i) =
      (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * heatHankel a (P i) (P j)) -
        2 * Complex.exp ((a : ℂ) / 4) * ((∑ i, x i * (P i).eval (-1 / 4)) *
          (starRingEnd ℂ) (∑ i, x i * (P i).eval (-1 / 4))) := by
  rw [archPrimeHankel_eq ha, heatHankel_sum_sum ha, eval_sum_smul]
  ring

theorem re_exp_mul_normSq (a : ℝ) (z : ℂ) :
    (2 * Complex.exp ((a : ℂ) / 4) * (z * (starRingEnd ℂ) z)).re = 2 * Real.exp (a / 4) * ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    show Complex.exp ((a : ℂ) / 4) = ((Real.exp (a / 4) : ℝ) : ℂ) by push_cast; ring_nf]
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Cross terms with a polynomial vanishing below a level are bounded by the two tails. -/
theorem norm_heatHankel_le_tails {a : ℝ} (ha : 0 < a) (Λ : ℝ) (P R : ℂ[X])
    (hR : ∀ q : XiZeroCopy, (xiHeatFrequency q).re ≤ Λ →
      R.eval (xiHeatFrequency q) = 0 ∧ R.eval ((starRingEnd ℂ) (xiHeatFrequency q)) = 0)
    {θ : ℝ} (hθ : 0 < θ) :
    ‖heatHankel a P R‖ ≤ (θ * ∑' q, heatHankelTail a (-1) P q +
        (∑' q, heatHankelTail a Λ R q) / θ) / 2 ∧
      ‖heatHankel a R P‖ ≤ (θ * ∑' q, heatHankelTail a (-1) P q +
        (∑' q, heatHankelTail a Λ R q) / θ) / 2 := by
  have hlow : ∀ q : XiZeroCopy, -1 < (xiHeatFrequency q).re := fun q => by
    linarith [neg_quarter_lt_re_xiHeatFrequency q]
  have hP1 : ∀ q (z : ℂ), z = xiHeatFrequency q ∨ z = (starRingEnd ℂ) (xiHeatFrequency q) →
      Real.exp (-(a * (xiHeatFrequency q).re)) * ‖P.eval z‖ ^ 2 ≤ heatHankelTail a (-1) P q := by
    intro q z hz
    unfold heatHankelTail
    rw [if_pos (hlow q)]
    have := (Real.exp_pos (-(a * (xiHeatFrequency q).re))).le
    rcases hz with rfl | rfl <;> nlinarith [sq_nonneg ‖P.eval (xiHeatFrequency q)‖,
      sq_nonneg ‖P.eval ((starRingEnd ℂ) (xiHeatFrequency q))‖]
  have hR1 : ∀ q (z : ℂ), z = xiHeatFrequency q ∨ z = (starRingEnd ℂ) (xiHeatFrequency q) →
      Real.exp (-(a * (xiHeatFrequency q).re)) * ‖R.eval z‖ ^ 2 ≤ heatHankelTail a Λ R q := by
    intro q z hz
    unfold heatHankelTail
    split_ifs with h
    · have := (Real.exp_pos (-(a * (xiHeatFrequency q).re))).le
      rcases hz with rfl | rfl <;> nlinarith [sq_nonneg ‖R.eval (xiHeatFrequency q)‖,
        sq_nonneg ‖R.eval ((starRingEnd ℂ) (xiHeatFrequency q))‖]
    · push Not at h
      rcases hz with rfl | rfl
      · rw [(hR q h).1, norm_zero]; simp
      · rw [(hR q h).2, norm_zero]; simp
  have hpt : ∀ q (z₁ z₂ : ℂ), (z₁ = xiHeatFrequency q ∨ z₁ = (starRingEnd ℂ) (xiHeatFrequency q)) →
      (z₂ = xiHeatFrequency q ∨ z₂ = (starRingEnd ℂ) (xiHeatFrequency q)) →
      Real.exp (-(a * (xiHeatFrequency q).re)) * (‖P.eval z₁‖ * ‖R.eval z₂‖) ≤
        (θ * heatHankelTail a (-1) P q + heatHankelTail a Λ R q / θ) / 2 := by
    intro q z₁ z₂ h1 h2
    have e1 := hP1 q z₁ h1
    have e2 := hR1 q z₂ h2
    have he := (Real.exp_pos (-(a * (xiHeatFrequency q).re))).le
    have hamgm : ‖P.eval z₁‖ * ‖R.eval z₂‖ ≤ (θ * ‖P.eval z₁‖ ^ 2 + ‖R.eval z₂‖ ^ 2 / θ) / 2 := by
      have : 0 ≤ (θ * ‖P.eval z₁‖ - ‖R.eval z₂‖) ^ 2 / θ := by positivity
      have h3 : (θ * ‖P.eval z₁‖ - ‖R.eval z₂‖) ^ 2 / θ =
          θ * ‖P.eval z₁‖ ^ 2 + ‖R.eval z₂‖ ^ 2 / θ - 2 * (‖P.eval z₁‖ * ‖R.eval z₂‖) := by
        field_simp
        ring
      linarith
    calc Real.exp (-(a * (xiHeatFrequency q).re)) * (‖P.eval z₁‖ * ‖R.eval z₂‖)
        ≤ Real.exp (-(a * (xiHeatFrequency q).re)) *
            ((θ * ‖P.eval z₁‖ ^ 2 + ‖R.eval z₂‖ ^ 2 / θ) / 2) := mul_le_mul_of_nonneg_left hamgm he
      _ = (θ * (Real.exp (-(a * (xiHeatFrequency q).re)) * ‖P.eval z₁‖ ^ 2) +
            (Real.exp (-(a * (xiHeatFrequency q).re)) * ‖R.eval z₂‖ ^ 2) / θ) / 2 := by ring
      _ ≤ (θ * heatHankelTail a (-1) P q + heatHankelTail a Λ R q / θ) / 2 := by
          gcongr
  have hsT : Summable fun q => (θ * heatHankelTail a (-1) P q + heatHankelTail a Λ R q / θ) / 2 :=
    ((((summable_heatHankelTail ha (-1) P).mul_left θ).add
      ((summable_heatHankelTail ha Λ R).div_const θ)).div_const 2)
  have htot : ∑' q, (θ * heatHankelTail a (-1) P q + heatHankelTail a Λ R q / θ) / 2 =
      (θ * ∑' q, heatHankelTail a (-1) P q + (∑' q, heatHankelTail a Λ R q) / θ) / 2 := by
    rw [tsum_div_const, Summable.tsum_add ((summable_heatHankelTail ha (-1) P).mul_left θ)
      ((summable_heatHankelTail ha Λ R).div_const θ), tsum_mul_left, tsum_div_const]
  constructor
  · rw [heatHankel]
    refine (norm_tsum_le_tsum_norm (summable_heatHankelTermAt ha P R).norm).trans ?_
    rw [← htot]
    refine Summable.tsum_le_tsum (fun q => ?_) (summable_heatHankelTermAt ha P R).norm hsT
    rw [heatHankelTermAt, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_exp]
    have hre : (-(a : ℂ) * xiHeatFrequency q).re = -(a * (xiHeatFrequency q).re) := by simp
    rw [hre, mul_assoc]
    exact hpt q _ _ (Or.inl rfl) (Or.inr rfl)
  · rw [heatHankel]
    refine (norm_tsum_le_tsum_norm (summable_heatHankelTermAt ha R P).norm).trans ?_
    rw [← htot]
    refine Summable.tsum_le_tsum (fun q => ?_) (summable_heatHankelTermAt ha R P).norm hsT
    rw [heatHankelTermAt, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_exp]
    have hre : (-(a : ℂ) * xiHeatFrequency q).re = -(a * (xiHeatFrequency q).re) := by simp
    rw [hre, mul_assoc, mul_comm ‖R.eval (xiHeatFrequency q)‖]
    exact hpt q _ _ (Or.inr rfl) (Or.inl rfl)

/-- **The pole member.**  For every `ε > 0` there is a polynomial with value `1` at `−¼`, vanishing
at every frequency with real part `≤ Λ`, whose heat Hankel tail is at most `2ε`. -/
theorem exists_pole_member {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ Λ : ℝ, ∃ Pst : ℂ[X], Pst.eval (-1 / 4) = 1 ∧
      (∀ q : XiZeroCopy, (xiHeatFrequency q).re ≤ Λ →
        Pst.eval (xiHeatFrequency q) = 0 ∧ Pst.eval ((starRingEnd ℂ) (xiHeatFrequency q)) = 0) ∧
      ∑' q, heatHankelTail a Λ Pst q ≤ 2 * ε := by
  classical
  obtain ⟨d, hd, hdsep⟩ := exists_pos_le_norm_sub {(-1 / 4 : ℂ)} (heatFrequenciesBelow (2 * (1 / 4) + 2))
  set C₀ := 2 + (2 * (1 / 4) + 3) / d with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 0 ≤ (2 * (1 / 4 : ℝ) + 3) / d := by positivity
    rw [hC₀]; linarith
  have hnq : ‖(-1 / 4 : ℂ)‖ ≤ 1 / 4 := by norm_num
  have hfreq_ne : ∀ q : XiZeroCopy, xiHeatFrequency q ≠ -1 / 4 := fun q h => by
    have := neg_quarter_lt_re_xiHeatFrequency q
    rw [h] at this
    norm_num at this
  have hratio : ∀ v : ℂ, (∃ q : XiZeroCopy, xiHeatFrequency q = v) → ∀ w : ℂ,
      ‖w - v‖ ≤ C₀ * (1 + ‖w‖) * ‖(-1 / 4 : ℂ) - v‖ := by
    rintro v ⟨q, rfl⟩ w
    refine norm_sub_le_of_far_or_sep hd hnq fun hvn => ?_
    refine hdsep _ (Finset.mem_singleton_self _) _ (mem_heatFrequenciesBelow.2 ⟨q, rfl, ?_⟩)
      (hfreq_ne q) ?_
    · exact (Complex.re_le_norm _).trans hvn.le
    · rw [show (starRingEnd ℂ) (-1 / 4 : ℂ) = -1 / 4 by
        rw [map_div₀, map_neg, map_one, map_ofNat]]
      exact hfreq_ne q
  obtain ⟨Dc, hDc0, hDc⟩ := exists_card_heatFrequenciesBelow_le
  obtain ⟨Λ, -, hΛ0, hsmall⟩ := exists_level_tail_small ha hC₀1 hDc0 0 hε 0
  set S := heatFrequenciesBelow Λ with hS
  set K := heatRootPoly S with hK
  have hKq : K.eval (-1 / 4) ≠ 0 := eval_heatRootPoly_ne_zero fun h => by
    obtain ⟨q, hq, -⟩ := mem_heatFrequenciesBelow.1 h
    exact hfreq_ne q hq
  have hSconj : ∀ v ∈ S, (starRingEnd ℂ) v ∈ S := fun v hv => conj_mem_heatFrequenciesBelow hv
  set Pst := C (K.eval (-1 / 4))⁻¹ * K with hPst
  have hPeval : ∀ w, Pst.eval w = (K.eval (-1 / 4))⁻¹ * K.eval w := fun w => by
    rw [hPst, eval_mul, eval_C]
  refine ⟨Λ, Pst, by rw [hPeval, inv_mul_cancel₀ hKq], fun q hq => ?_, ?_⟩
  · have hmem : xiHeatFrequency q ∈ S := mem_heatFrequenciesBelow.2 ⟨q, rfl, hq⟩
    rw [hPeval, hPeval, eval_heatRootPoly_eq_zero hmem, eval_heatRootPoly_eq_zero (hSconj _ hmem),
      mul_zero]
    exact ⟨rfl, rfl⟩
  · have hk : ((S.card : ℕ) : ℝ) ≤ Dc * (Λ + 7) ^ (5 / 8 : ℝ) := hDc Λ hΛ0
    have htail := hsmall S.card hk
    have hbound : ∀ w : ℂ, ‖Pst.eval w‖ ≤ (C₀ * (1 + ‖w‖)) ^ S.card := by
      intro w
      rw [hPeval, norm_mul, norm_inv]
      have h := norm_eval_heatRootPoly_le (S := S) (u := -1 / 4) (w := w) (C₀ := C₀) fun v hv => by
        obtain ⟨q, hq, -⟩ := mem_heatFrequenciesBelow.1 hv
        exact hratio v ⟨q, hq⟩ w
      rw [inv_mul_le_iff₀ (norm_pos_iff.2 hKq)]
      linarith [mul_comm ‖K.eval (-1 / 4)‖ ((C₀ * (1 + ‖w‖)) ^ S.card)]
    have hpt : ∀ q : XiZeroCopy, heatHankelTail a Λ Pst q ≤ 2 *
        (if Λ < (xiHeatFrequency q).re then Real.exp (-(a * (xiHeatFrequency q).re)) *
          ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * S.card) * (1 + ‖xiHeatFrequency q‖) ^ 0)
          else 0) := by
      intro q
      unfold heatHankelTail
      split_ifs with h
      · have h1 := pow_le_pow_left₀ (norm_nonneg _) (hbound (xiHeatFrequency q)) 2
        have h2 := pow_le_pow_left₀ (norm_nonneg _) (hbound ((starRingEnd ℂ) (xiHeatFrequency q))) 2
        rw [Complex.norm_conj] at h2
        rw [← pow_mul, mul_comm S.card 2] at h1 h2
        have he := (Real.exp_pos (-(a * (xiHeatFrequency q).re))).le
        rw [pow_zero, mul_one]
        nlinarith
      · simp
    have hsum : Summable fun q : XiZeroCopy => (if Λ < (xiHeatFrequency q).re then
        Real.exp (-(a * (xiHeatFrequency q).re)) *
          ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * S.card) * (1 + ‖xiHeatFrequency q‖) ^ 0)
        else 0) := by
      refine ((summable_one_add_norm_pow_mul_exp ha (2 * S.card)).mul_left
        (C₀ ^ (2 * S.card))).of_nonneg_of_le (fun q => by split_ifs <;> positivity) fun q => ?_
      split_ifs
      · rw [mul_pow, pow_zero, mul_one]
        apply le_of_eq
        ring
      · positivity
    calc ∑' q, heatHankelTail a Λ Pst q ≤ ∑' q : XiZeroCopy, 2 * (if Λ < (xiHeatFrequency q).re then
          Real.exp (-(a * (xiHeatFrequency q).re)) *
            ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * S.card) * (1 + ‖xiHeatFrequency q‖) ^ 0)
          else 0) := Summable.tsum_le_tsum hpt (summable_heatHankelTail ha Λ Pst) (hsum.mul_left 2)
      _ = 2 * ∑' q : XiZeroCopy, (if Λ < (xiHeatFrequency q).re then
          Real.exp (-(a * (xiHeatFrequency q).re)) *
            ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * S.card) * (1 + ‖xiHeatFrequency q‖) ^ 0)
          else 0) := tsum_mul_left
      _ ≤ 2 * ε := by linarith

/-! ## One more negative square -/

/-- The scalar inequality behind the extra negative direction. -/
theorem quadratic_pole_neg {δ C η T E X s V : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (hη0 : 0 ≤ η) (hη : η ≤ δ / (4 * (C + 1))) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 8)
    (hT2 : T ≤ δ / (16 * (C + 1) ^ 2)) (hE : 2 ≤ E) (hX : 0 ≤ X) (hs : 0 ≤ s)
    (hV : s - C * X ≤ V) (hne : 0 < X ∨ 0 < s) :
    -(δ * X ^ 2) + η * s * X + T * s ^ 2 - E * V ^ 2 < 0 := by
  have hC1 : 0 < C + 1 := by linarith
  have hηC : η * C ≤ δ / 4 := by
    calc η * C ≤ δ / (4 * (C + 1)) * C := mul_le_mul_of_nonneg_right hη hC
      _ ≤ δ / (4 * (C + 1)) * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = δ / 4 := by field_simp
  have hTC : T * C ^ 2 ≤ δ / 16 := by
    calc T * C ^ 2 ≤ δ / (16 * (C + 1) ^ 2) * C ^ 2 := mul_le_mul_of_nonneg_right hT2 (sq_nonneg _)
      _ ≤ δ / (16 * (C + 1) ^ 2) * (C + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = δ / 16 := by field_simp
  have hEV : 0 ≤ E * V ^ 2 := by positivity
  by_cases hcase : s ≤ 2 * C * X
  · have hXpos : 0 < X := by
      rcases hne with h | h
      · exact h
      · by_contra hX0
        have : X = 0 := le_antisymm (not_lt.1 hX0) hX
        rw [this] at hcase
        linarith
    have h1 : η * s * X ≤ δ / 2 * X ^ 2 := by
      calc η * s * X ≤ η * (2 * C * X) * X :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcase hη0) hX
        _ = 2 * (η * C) * X ^ 2 := by ring
        _ ≤ 2 * (δ / 4) * X ^ 2 := by gcongr
        _ = δ / 2 * X ^ 2 := by ring
    have h2 : T * s ^ 2 ≤ δ / 4 * X ^ 2 := by
      calc T * s ^ 2 ≤ T * (2 * C * X) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hcase 2) hT0
        _ = 4 * (T * C ^ 2) * X ^ 2 := by ring
        _ ≤ 4 * (δ / 16) * X ^ 2 := by gcongr
        _ = δ / 4 * X ^ 2 := by ring
    have h3 : 0 < δ * X ^ 2 := by positivity
    linarith
  · push Not at hcase
    have hspos : 0 < s := by nlinarith
    have hVs : s / 2 ≤ V := by nlinarith
    have hEV2 : s ^ 2 / 2 ≤ E * V ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hVs 2
      nlinarith
    have hamgm : η * s * X ≤ δ * X ^ 2 + η ^ 2 / (4 * δ) * s ^ 2 := by
      have hsq : 0 ≤ (2 * δ * X - η * s) ^ 2 / (4 * δ) := by positivity
      have h : (2 * δ * X - η * s) ^ 2 / (4 * δ) =
          δ * X ^ 2 + η ^ 2 / (4 * δ) * s ^ 2 - η * s * X := by
        field_simp
        ring
      linarith
    have hη2 : η ^ 2 / (4 * δ) ≤ 1 / 64 := by
      have h1 : η ≤ δ / 4 := hη.trans (div_le_div_of_nonneg_left hδ.le (by norm_num)
        (by nlinarith))
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have : η ^ 2 / (4 * δ) * s ^ 2 ≤ 1 / 64 * s ^ 2 := mul_le_mul_of_nonneg_right hη2 (sq_nonneg _)
    have h5 : T * s ^ 2 ≤ 1 / 8 * s ^ 2 := mul_le_mul_of_nonneg_right hT1 (sq_nonneg _)
    have h6 : 0 < s ^ 2 := by positivity
    linarith

theorem heatHankelTail_neg_one_eq {a Λ : ℝ} {R : ℂ[X]}
    (hR : ∀ q : XiZeroCopy, (xiHeatFrequency q).re ≤ Λ →
      R.eval (xiHeatFrequency q) = 0 ∧ R.eval ((starRingEnd ℂ) (xiHeatFrequency q)) = 0)
    (q : XiZeroCopy) : heatHankelTail a (-1) R q = heatHankelTail a Λ R q := by
  have hlow : -1 < (xiHeatFrequency q).re := by linarith [neg_quarter_lt_re_xiHeatFrequency q]
  unfold heatHankelTail
  rw [if_pos hlow]
  split_ifs with h
  · rfl
  · push Not at h
    rw [(hR q h).1, (hR q h).2]
    simp

/-- **Augmentation.**  A negative definite family for the heat Hankel form, together with the pole
member, is a negative definite family for the arch−prime Hankel form. -/
theorem exists_archPrimeHankel_negative_family {a : ℝ} (ha : 0 < a) {ι : Type*} [Fintype ι]
    (P : ι → ℂ[X])
    (hP : ∀ x : ι → ℂ, x ≠ 0 → (heatHankel a (∑ i, x i • P i) (∑ i, x i • P i)).re < 0) :
    ∃ Q : Option ι → ℂ[X], ∀ y : Option ι → ℂ, y ≠ 0 →
      (archPrimeHankel a (∑ i, y i • Q i) (∑ i, y i • Q i)).re < 0 := by
  classical
  have hMneg : ∀ x : ι → ℂ, x ≠ 0 →
      (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * heatHankel a (P i) (P j)).re < 0 := by
    intro x hx
    have := hP x hx
    rwa [heatHankel_sum_sum ha] at this
  obtain ⟨δ₀, hδ₀, hbound⟩ := exists_neg_quadratic_bound _ hMneg
  set δ := min δ₀ 1 with hδdef
  have hδ : 0 < δ := lt_min hδ₀ one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hbound' : ∀ x : ι → ℂ,
      (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * heatHankel a (P i) (P j)).re ≤ -(δ * ‖x‖ ^ 2) :=
    fun x => (hbound x).trans (by nlinarith [min_le_left δ₀ 1, sq_nonneg ‖x‖])
  set CV := ∑ i, ‖(P i).eval (-1 / 4)‖ with hCV
  have hCV0 : 0 ≤ CV := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set Tot := ∑ i, ∑' q, heatHankelTail a (-1) (P i) q with hTot
  have hTot_i : ∀ i, ∑' q, heatHankelTail a (-1) (P i) q ≤ Tot := fun i =>
    Finset.single_le_sum (f := fun i => ∑' q, heatHankelTail a (-1) (P i) q)
      (fun i _ => tsum_nonneg (heatHankelTail_nonneg a (-1) (P i))) (Finset.mem_univ i)
  have hTot0 : 0 ≤ Tot := Finset.sum_nonneg fun i _ => tsum_nonneg (heatHankelTail_nonneg a (-1) (P i))
  set m : ℝ := (Fintype.card ι : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set η₀ := δ / (4 * (CV + 1)) with hη₀
  have hη₀0 : 0 < η₀ := by positivity
  set T₀ := min (1 / 8 : ℝ) (δ / (16 * (CV + 1) ^ 2)) with hT₀
  have hT₀0 : 0 < T₀ := lt_min (by norm_num) (by positivity)
  set θ := η₀ / (2 * (m + 1) * (Tot + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  set ε₁ := min (T₀ / 2) (θ * η₀ / (4 * (m + 1))) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (by positivity)
  obtain ⟨Λ, Pst, hPst1, hPstlow, hPsttail⟩ := exists_pole_member ha hε₁0
  -- cross terms
  have hcross : ∀ i, ‖heatHankel a (P i) Pst‖ ≤ η₀ / (2 * (m + 1)) ∧
      ‖heatHankel a Pst (P i)‖ ≤ η₀ / (2 * (m + 1)) := by
    intro i
    obtain ⟨h1, h2⟩ := norm_heatHankel_le_tails ha Λ (P i) Pst hPstlow hθ0
    have hb : (θ * ∑' q, heatHankelTail a (-1) (P i) q + (∑' q, heatHankelTail a Λ Pst q) / θ) / 2
        ≤ η₀ / (2 * (m + 1)) := by
      have e1 : θ * ∑' q, heatHankelTail a (-1) (P i) q ≤ η₀ / (2 * (m + 1)) := by
        calc θ * ∑' q, heatHankelTail a (-1) (P i) q ≤ θ * (Tot + 1) :=
              mul_le_mul_of_nonneg_left (by linarith [hTot_i i]) hθ0.le
          _ = η₀ / (2 * (m + 1)) := by rw [hθ]; field_simp
      have e2 : (∑' q, heatHankelTail a Λ Pst q) / θ ≤ η₀ / (2 * (m + 1)) := by
        rw [div_le_iff₀ hθ0]
        calc ∑' q, heatHankelTail a Λ Pst q ≤ 2 * ε₁ := hPsttail
          _ ≤ 2 * (θ * η₀ / (4 * (m + 1))) := by
              linarith [min_le_right (T₀ / 2) (θ * η₀ / (4 * (m + 1)))]
          _ = η₀ / (2 * (m + 1)) * θ := by field_simp; ring
      linarith
    exact ⟨h1.trans hb, h2.trans hb⟩
  have hself : ‖heatHankel a Pst Pst‖ ≤ T₀ := by
    obtain ⟨h1, -⟩ := norm_heatHankel_le_tails ha Λ Pst Pst hPstlow one_pos
    rw [tsum_congr (heatHankelTail_neg_one_eq hPstlow), one_mul, div_one] at h1
    calc ‖heatHankel a Pst Pst‖ ≤ (∑' q, heatHankelTail a Λ Pst q + ∑' q, heatHankelTail a Λ Pst q) / 2 := h1
      _ ≤ (2 * ε₁ + 2 * ε₁) / 2 := by linarith
      _ = 2 * ε₁ := by ring
      _ ≤ T₀ := by linarith [min_le_left (T₀ / 2) (θ * η₀ / (4 * (m + 1)))]
  refine ⟨fun o => o.elim Pst P, fun y hy => ?_⟩
  obtain ⟨x, hxdef⟩ : ∃ x : ι → ℂ, ∀ i, x i = y (some i) := ⟨_, fun _ => rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : ℂ, t = y none := ⟨_, rfl⟩
  set v := ∑ i, x i * (P i).eval (-1 / 4) with hv
  have hexp : archPrimeHankel a (∑ i, y i • (fun o => o.elim Pst P) i)
      (∑ i, y i • (fun o => o.elim Pst P) i) =
      ((∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * heatHankel a (P i) (P j)) +
        ((∑ j, t * (starRingEnd ℂ) (x j) * heatHankel a Pst (P j)) +
          (∑ i, x i * (starRingEnd ℂ) t * heatHankel a (P i) Pst)) +
        t * (starRingEnd ℂ) t * heatHankel a Pst Pst) -
      2 * Complex.exp ((a : ℂ) / 4) * ((t + v) * (starRingEnd ℂ) (t + v)) := by
    rw [archPrimeHankel_sum_sum ha]
    simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, hPst1, mul_one,
      Finset.sum_add_distrib, ← hxdef, ← htdef, hv]
    ring
  rw [hexp, sub_re, re_exp_mul_normSq, add_re, add_re, add_re]
  set X := ‖x‖ with hX
  set sN := ‖t‖ with hsN
  have hX0 : 0 ≤ X := norm_nonneg _
  have hs0 : 0 ≤ sN := norm_nonneg _
  have hxi : ∀ i, ‖x i‖ ≤ X := fun i => norm_le_pi_norm x i
  have hA := hbound' x
  have hfrac : m * (η₀ / (2 * (m + 1))) ≤ η₀ / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hsX : 0 ≤ sN * X := mul_nonneg hs0 hX0
  have hB1 : ‖∑ j, t * (starRingEnd ℂ) (x j) * heatHankel a Pst (P j)‖ ≤ sN * X * (η₀ / 2) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖t * (starRingEnd ℂ) (x j) * heatHankel a Pst (P j)‖
        ≤ ∑ _j : ι, sN * X * (η₀ / (2 * (m + 1))) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hxi j) hs0) (hcross j).2 (norm_nonneg _)
            (by positivity)
      _ = m * (sN * X * (η₀ / (2 * (m + 1)))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ sN * X * (η₀ / 2) := by nlinarith
  have hB2 : ‖∑ i, x i * (starRingEnd ℂ) t * heatHankel a (P i) Pst‖ ≤ sN * X * (η₀ / 2) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖x i * (starRingEnd ℂ) t * heatHankel a (P i) Pst‖
        ≤ ∑ _i : ι, sN * X * (η₀ / (2 * (m + 1))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, mul_comm ‖x i‖ sN]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hxi i) hs0) (hcross i).1 (norm_nonneg _)
            (by positivity)
      _ = m * (sN * X * (η₀ / (2 * (m + 1)))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ sN * X * (η₀ / 2) := by nlinarith
  have hBre1 := (Complex.re_le_norm _).trans hB1
  have hBre2 := (Complex.re_le_norm _).trans hB2
  set T := ‖heatHankel a Pst Pst‖ with hT
  have hD : (t * (starRingEnd ℂ) t * heatHankel a Pst Pst).re ≤ T * sN ^ 2 := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]
    ring
  have hvle : ‖v‖ ≤ CV * X := by
    rw [hv, hCV, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hxi i) (norm_nonneg _)
  have hV : sN - CV * X ≤ ‖t + v‖ := by
    have := norm_sub_norm_le t (-v)
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have hE : 2 ≤ 2 * Real.exp (a / 4) := by
    have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ a / 4)
    linarith
  have hne : 0 < X ∨ 0 < sN := by
    by_contra h
    push Not at h
    have hX' : x = 0 := norm_le_zero_iff.1 h.1
    have hs' : t = 0 := norm_le_zero_iff.1 h.2
    apply hy
    funext o
    cases o with
    | none => rw [← htdef, hs']; rfl
    | some i => rw [← hxdef, hX']; rfl
  have hkey := quadratic_pole_neg (η := η₀) (T := T) (E := 2 * Real.exp (a / 4)) (V := ‖t + v‖)
    hδ hδ1 hCV0 hη₀0.le le_rfl (norm_nonneg _) (hself.trans (min_le_left _ _))
    (hself.trans (min_le_right _ _)) hE hX0 hs0 hV hne
  linarith [hA, hBre1, hBre2, hD, hkey]

/-! ## The Hodge-index law -/

theorem archPrimeHankel_zero {a : ℝ} (ha : 0 < a) : archPrimeHankel a 0 0 = 0 := by
  rw [archPrimeHankel_eq ha]
  simp [heatHankel, heatHankelTermAt]

/-- A negative definite family spans a negative definite subspace of the same dimension. -/
theorem exists_archPrimeHankel_subspace_of_family {a : ℝ} (ha : 0 < a) {κ : Type*} [Fintype κ]
    (Q : κ → ℂ[X])
    (hQ : ∀ y : κ → ℂ, y ≠ 0 → (archPrimeHankel a (∑ i, y i • Q i) (∑ i, y i • Q i)).re < 0) :
    ∃ V : Submodule ℂ ℂ[X], Module.finrank ℂ V = Fintype.card κ ∧
      ∀ P ∈ V, P ≠ 0 → (archPrimeHankel a P P).re < 0 := by
  classical
  set Φ : (κ → ℂ) →ₗ[ℂ] ℂ[X] := Fintype.linearCombination ℂ Q with hΦ
  have hΦapp : ∀ y, Φ y = ∑ i, y i • Q i := fun y => Fintype.linearCombination_apply ℂ Q y
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hne
    have := hQ y hne
    rw [← hΦapp, hy, archPrimeHankel_zero ha, zero_re] at this
    exact lt_irrefl 0 this
  refine ⟨LinearMap.range Φ, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  · rintro c ⟨y, rfl⟩ hc
    have hy : y ≠ 0 := by
      rintro rfl
      exact hc (map_zero Φ)
    rw [hΦapp]
    exact hQ y hy

/-- **Lower bound.**  For every finite set `G` of upper off-line frequencies, `W_a` is negative
definite on a subspace of dimension `#G + 1`. -/
theorem exists_archPrimeHankel_negative_subspace {a : ℝ} (ha : 0 < a) (G : Finset ℂ)
    (hG : ∀ u ∈ G, u ∈ xiUpperFrequencies) :
    ∃ V : Submodule ℂ ℂ[X], Module.finrank ℂ V = G.card + 1 ∧
      ∀ P ∈ V, P ≠ 0 → (archPrimeHankel a P P).re < 0 := by
  classical
  rcases G.eq_empty_or_nonempty with hGe | hGne
  · obtain ⟨Q, hQ⟩ := exists_archPrimeHankel_negative_family ha (ι := Empty) Empty.elim
      fun x hx => absurd (_root_.funext fun i : Empty => Empty.elim i) hx
    obtain ⟨V, hV, hneg⟩ := exists_archPrimeHankel_subspace_of_family ha Q hQ
    refine ⟨V, ?_, hneg⟩
    rw [hV, hGe]
    simp
  · obtain ⟨P, hP⟩ := exists_heatHankel_negative_family ha G hGne hG
    obtain ⟨Q, hQ⟩ := exists_archPrimeHankel_negative_family ha P hP
    obtain ⟨V, hV, hneg⟩ := exists_archPrimeHankel_subspace_of_family ha Q hQ
    refine ⟨V, ?_, hneg⟩
    rw [hV, Fintype.card_option, Fintype.card_coe]

/-- **Upper bound.**  If `U` is finite, a subspace on which `W_a` is negative definite has
dimension at most `#U + 1`. -/
theorem finrank_le_of_archPrimeHankel_neg {a : ℝ} (ha : 0 < a) (hU : xiUpperFrequencies.Finite)
    (V : Submodule ℂ ℂ[X]) (hV : ∀ P ∈ V, P ≠ 0 → (archPrimeHankel a P P).re < 0) :
    Module.finrank ℂ V ≤ hU.toFinset.card + 1 := by
  classical
  set L : ℂ[X] →ₗ[ℂ] (Option hU.toFinset → ℂ) :=
    LinearMap.pi fun o => Polynomial.leval (o.elim (-1 / 4 : ℂ) fun w => (w : ℂ)) with hL
  have hinj : Function.Injective (L.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    by_contra hne
    have hP0 : (P : ℂ[X]) ≠ 0 := fun h => hne (Subtype.ext h)
    have hvan : ∀ w ∈ xiUpperFrequencies, (P : ℂ[X]).eval w = 0 := by
      intro w hw
      have := congrFun hP (some ⟨w, hU.mem_toFinset.2 hw⟩)
      simpa [hL] using this
    have hq : (P : ℂ[X]).eval (-1 / 4) = 0 := by
      have := congrFun hP none
      simpa [hL] using this
    have h1 := heatHankel_re_nonneg_of_eval_vanish ha (P : ℂ[X]) hvan
    have h2 := hV P P.2 hP0
    rw [archPrimeHankel_eq ha, hq] at h2
    simp only [mul_zero, zero_mul, sub_zero] at h2
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_coe] at h

/-- **The Hodge-index law, finite case.**  If `U` is finite, the negative index of the arch−prime
Hankel form `W_a` is exactly `#U + 1`, for every `a > 0`. -/
theorem archPrimeHankel_negativeIndex_eq_card_add_one {a : ℝ} (ha : 0 < a)
    (hU : xiUpperFrequencies.Finite) :
    (∀ V : Submodule ℂ ℂ[X], (∀ P ∈ V, P ≠ 0 → (archPrimeHankel a P P).re < 0) →
      Module.finrank ℂ V ≤ hU.toFinset.card + 1) ∧
    ∃ V : Submodule ℂ ℂ[X], Module.finrank ℂ V = hU.toFinset.card + 1 ∧
      ∀ P ∈ V, P ≠ 0 → (archPrimeHankel a P P).re < 0 :=
  ⟨fun V hV => finrank_le_of_archPrimeHankel_neg ha hU V hV,
    exists_archPrimeHankel_negative_subspace ha hU.toFinset fun _ hu => hU.mem_toFinset.1 hu⟩

/-- **The Hodge-index law, infinite case.** -/
theorem archPrimeHankel_negative_of_infinite {a : ℝ} (ha : 0 < a)
    (hU : xiUpperFrequencies.Infinite) (n : ℕ) :
    ∃ V : Submodule ℂ ℂ[X], Module.finrank ℂ V = n + 1 ∧
      ∀ P ∈ V, P ≠ 0 → (archPrimeHankel a P P).re < 0 := by
  obtain ⟨G, hGU, hGcard⟩ := hU.exists_subset_card_eq n
  obtain ⟨V, hV, hneg⟩ := exists_archPrimeHankel_negative_subspace ha G fun u hu => hGU hu
  exact ⟨V, by rw [hV, hGcard], hneg⟩

/-- **The pole is always seen.**  Unconditionally, the arch−prime Hankel form is not positive
semidefinite. -/
theorem exists_archPrimeHankel_neg {a : ℝ} (ha : 0 < a) :
    ∃ P : ℂ[X], (archPrimeHankel a P P).re < 0 := by
  obtain ⟨V, hV, hneg⟩ := exists_archPrimeHankel_negative_subspace ha ∅ (by simp)
  have hVbot : V ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hV
    simp at hV
  obtain ⟨P, hPV, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVbot
  exact ⟨P, hneg P hPV hP0⟩

/-- **RH as positivity on the pole hyperplane.**  For `a > 0`, RH holds iff the arch−prime Hankel
form `W_a` is nonnegative on every polynomial vanishing at `−¼`. -/
theorem riemannHypothesis_iff_archPrimeHankel_nonneg_of_eval_neg_quarter {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔
      ∀ P : ℂ[X], P.eval (-1 / 4) = 0 → 0 ≤ (archPrimeHankel a P P).re := by
  constructor
  · intro hRH P hP
    rw [archPrimeHankel_eq ha, hP]
    simp only [mul_zero, zero_mul, sub_zero]
    exact heatHankel_re_nonneg_of_riemannHypothesis ha hRH P
  · intro h
    by_contra hRH
    rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero] at hRH
    push Not at hRH
    obtain ⟨q, hq⟩ := hRH
    have hw := (xiHeatFrequency_im_ne_zero_iff q).2 hq
    obtain ⟨u, hu⟩ : ∃ u, u ∈ xiUpperFrequencies := by
      rcases lt_or_gt_of_ne hw with h' | h'
      · refine ⟨_, xiZeroCopyLineConjEquiv q, rfl, ?_⟩
        rw [xiHeatFrequency_lineConj, Complex.conj_im]
        linarith
      · exact ⟨_, q, rfl, h'⟩
    obtain ⟨V, hV, hneg⟩ := exists_archPrimeHankel_negative_subspace ha {u} (by simpa using hu)
    rw [Finset.card_singleton] at hV
    haveI : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (by rw [hV]; norm_num)
    set f : V →ₗ[ℂ] ℂ := (Polynomial.leval (-1 / 4 : ℂ)).domRestrict V with hf
    have hrank := LinearMap.finrank_range_add_finrank_ker f
    have hr : Module.finrank ℂ (LinearMap.range f) ≤ 1 := by
      calc Module.finrank ℂ (LinearMap.range f) ≤ Module.finrank ℂ ℂ := Submodule.finrank_le _
        _ = 1 := Module.finrank_self ℂ
    have hker : LinearMap.ker f ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hrank
      omega
    obtain ⟨P, hPker, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hPq : (P : ℂ[X]).eval (-1 / 4) = 0 := by
      have := LinearMap.mem_ker.1 hPker
      simpa [hf] using this
    have hPne : (P : ℂ[X]) ≠ 0 := fun h0 => hP0 (Subtype.ext h0)
    exact absurd (h P hPq) (not_le.2 (hneg P P.2 hPne))

end

end RHTower
