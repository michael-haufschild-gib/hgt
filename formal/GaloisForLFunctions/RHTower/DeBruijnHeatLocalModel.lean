import GaloisForLFunctions.RHTower.DeBruijnZeroMotion

/-!
# The local heat model of `H_t` at a zero of order `k`

Let `z₀` be a zero of order `k` of `H_s` (`s > 0`) and `a = H_s^{(k)}(z₀)`. Backward in time,
at the parabolic scale `z = z₀ + qσ`, `h = q²`,

`H_{s−q²}(z₀ + qσ) = (a/k!) q^k P_k(σ) + O(q^{k+1})`,   `P_k(σ) = Σ_{2m ≤ k} k!/(m!(k−2m)!) σ^{k−2m}`,

uniformly for `σ` in compact sets (`exists_norm_riemannHeat_sub_heatModel_le`); `P_k = e^{D²}σ^k`
is the backward heat evolution of the monomial.

Ingredients:
* `iteratedDeriv_riemannHeat`: `H_t^{(n)} = ∫ Φ e^{tx²} (ix)^n e^{izx} dx`;
* `norm_riemannHeat_time_taylor_le`: `H_{t+h} = Σ_{m<M} (−h)^m/m! · H_t^{(2m)} + O(|h|^M)`, from
  `‖e^w − Σ_{m<M} w^m/m!‖ ≤ ‖w‖^M e^{‖w‖}` with `w = hx²`;
* `exists_norm_sub_monomial_le`: an entire function whose derivatives of order `< n` vanish at `z₀`
  is `f^{(n)}(z₀)/n! · w^n + O(|w|^{n+1})` near `z₀`.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-! ## Derivatives and time expansion -/

theorem integrable_norm_heatWeight_mul_pow {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (c : ℝ) :
    Integrable (fun x => ‖heatWeight t x * (I * x) ^ n‖ * Real.exp (c * |x|)) := by
  refine (integrable_pow_mul_heatWeight ht n c).congr (Eventually.of_forall fun x => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- `H_t^{(n)}(z) = ∫ Φ(x) e^{tx²} (ix)^n e^{izx} dx`. -/
theorem iteratedDeriv_riemannHeat {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    iteratedDeriv n (riemannHeat t) = expTransform (fun x => heatWeight t x * (I * x) ^ n) := by
  induction n with
  | zero => simp [riemannHeat_eq_expTransform]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have hc : Continuous fun x : ℝ => heatWeight t x * (I * x) ^ n := by
      have := continuous_heatWeight t; fun_prop
    rw [(hasDerivAt_expTransform hc (integrable_norm_heatWeight_mul_pow ht n) z).deriv]
    congr 1
    funext x
    ring

theorem integrable_heatWeight_mul_pow_mul_exp {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ => heatWeight t x * (I * x) ^ n * Complex.exp (I * z * x)) := by
  refine (integrable_norm_heatWeight_mul_pow ht n |z.im|).mono'
    (((continuous_heatWeight t).mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  gcongr
  exact norm_exp_I_mul_le z x

/-- **Time expansion to order `M`.** For `t, t + h ≥ 0` and `|h| ≤ 1`,
`‖H_{t+h}(z) − Σ_{m<M} (−h)^m/m! · H_t^{(2m)}(z)‖ ≤ (∫ |x|^{2M} Φ e^{(t+1)x²} e^{|Im z||x|}) |h|^M`. -/
theorem norm_riemannHeat_time_taylor_le {t h : ℝ} (ht : 0 ≤ t) (hth : 0 ≤ t + h) (hh : |h| ≤ 1)
    (M : ℕ) (z : ℂ) :
    ‖riemannHeat (t + h) z - ∑ m ∈ Finset.range M,
        (-h : ℂ) ^ m / m.factorial * iteratedDeriv (2 * m) (riemannHeat t) z‖ ≤
      (∫ x, |x| ^ (2 * M) * ‖heatWeight (t + 1) x‖ * Real.exp (|z.im| * |x|)) * |h| ^ M := by
  have hself : Integrable (fun x : ℝ => heatWeight (t + h) x * Complex.exp (I * z * x)) :=
    integrable_heat_exp_mul hth _ (continuous_heatWeight _)
      (fun x => le_mul_of_one_le_right (norm_nonneg _)
        (by have := abs_nonneg x; rw [pow_one]; linarith)) z
  have hterm : ∀ m ∈ Finset.range M, Integrable (fun x : ℝ =>
      (-h : ℂ) ^ m / m.factorial * (heatWeight t x * (I * x) ^ (2 * m) *
        Complex.exp (I * z * x))) :=
    fun m _ => (integrable_heatWeight_mul_pow_mul_exp ht (2 * m) z).const_mul _
  simp_rw [iteratedDeriv_riemannHeat ht]
  simp only [riemannHeat_eq_expTransform, expTransform]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ hterm, ← integral_sub hself (integrable_finsetSum _ hterm)]
  refine (norm_integral_le_of_norm_le
    ((integrable_pow_mul_heatWeight (by linarith : (0 : ℝ) ≤ t + 1) (2 * M) |z.im|).mul_const
      (|h| ^ M)) (Eventually.of_forall fun x => ?_)).trans (le_of_eq (integral_mul_const _ _))
  set w : ℂ := ((h * x ^ 2 : ℝ) : ℂ) with hw
  have hsum : ∀ m : ℕ, (-h : ℂ) ^ m / m.factorial * (heatWeight t x * (I * x) ^ (2 * m) *
      Complex.exp (I * z * x)) = heatWeight t x * Complex.exp (I * z * x) *
        (w ^ m / m.factorial) := by
    intro m
    have e : (-(h : ℂ)) ^ m * ((I * x) ^ 2) ^ m = w ^ m := by
      rw [← mul_pow, hw]
      congr 1
      rw [mul_pow, I_sq]
      push_cast
      ring
    rw [pow_mul, ← e]
    ring
  simp_rw [hsum]
  rw [← Finset.mul_sum, heatWeight_add, show ((Real.exp (h * x ^ 2) : ℝ) : ℂ) = Complex.exp w by
    rw [hw]; push_cast; rfl]
  rw [show heatWeight t x * Complex.exp w * Complex.exp (I * z * x) -
      heatWeight t x * Complex.exp (I * z * x) *
        ∑ m ∈ Finset.range M, w ^ m / m.factorial =
      heatWeight t x * Complex.exp (I * z * x) *
        (Complex.exp w - ∑ m ∈ Finset.range M, w ^ m / m.factorial) by ring]
  rw [norm_mul, norm_mul]
  have h1 := Complex.norm_exp_sub_sum_le_norm_mul_exp w M
  have hwn : ‖w‖ = |h| * x ^ 2 := by
    rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg x)]
  have hwle : ‖w‖ ≤ x ^ 2 := by
    rw [hwn]; exact mul_le_of_le_one_left (sq_nonneg x) hh
  have h2 := norm_exp_I_mul_le z x
  have hmain := norm_heatWeight_mul_exp t x
  calc ‖heatWeight t x‖ * ‖Complex.exp (I * z * x)‖ *
        ‖Complex.exp w - ∑ m ∈ Finset.range M, w ^ m / m.factorial‖
      ≤ ‖heatWeight t x‖ * Real.exp (|z.im| * |x|) * (‖w‖ ^ M * Real.exp (x ^ 2)) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = |x| ^ (2 * M) * (‖heatWeight t x‖ * Real.exp (x ^ 2)) * Real.exp (|z.im| * |x|) *
          |h| ^ M := by
        rw [hwn, mul_pow, pow_mul, sq_abs]; ring
    _ = |x| ^ (2 * M) * ‖heatWeight (t + 1) x‖ * Real.exp (|z.im| * |x|) * |h| ^ M := by
        rw [hmain]

/-! ## Local structure at a zero of finite order -/

/-- An entire function whose derivatives of order `< n` vanish at `z₀` is
`f^{(n)}(z₀)/n! · w^n + O(|w|^{n+1})` near `z₀`. -/
theorem exists_norm_sub_monomial_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} {n : ℕ}
    (hvan : ∀ i < n, iteratedDeriv i f z₀ = 0) :
    ∃ C r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w‖ ≤ r →
      ‖f (z₀ + w) - iteratedDeriv n f z₀ / n.factorial * w ^ n‖ ≤ C * ‖w‖ ^ (n + 1) := by
  have hp := (hf.analyticAt z₀).hasFPowerSeriesAt
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (hp.isBigO_sub_partialSum_pow (n + 1))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hC
  refine ⟨C, r / 2, by positivity, fun w hw => ?_⟩
  have h := hball w (by rw [mem_ball, dist_zero_right]; linarith)
  have hsum : (FormalMultilinearSeries.ofScalars ℂ
      fun n => iteratedDeriv n f z₀ / n.factorial).partialSum (n + 1) w =
      iteratedDeriv n f z₀ / n.factorial * w ^ n := by
    simp only [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq,
      Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (fun i hi => by rw [hvan i (Finset.mem_range.mp hi)]; simp)]
    simp [smul_eq_mul]
  rw [hsum] at h
  simpa [norm_pow, Real.norm_eq_abs, abs_norm] using h

theorem iteratedDeriv_iteratedDeriv_eq (f : ℂ → ℂ) (i j : ℕ) :
    iteratedDeriv i (iteratedDeriv j f) = iteratedDeriv (i + j) f := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih, show i + 1 + j = (i + j) + 1 by ring, iteratedDeriv_succ]

theorem differentiable_iteratedDeriv_riemannHeat {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n (riemannHeat t)) := by
  rw [iteratedDeriv_riemannHeat ht]
  have hc : Continuous fun x : ℝ => heatWeight t x * (I * x) ^ n := by
    have := continuous_heatWeight t; fun_prop
  exact fun z => (hasDerivAt_expTransform hc (integrable_norm_heatWeight_mul_pow ht n) z).differentiableAt

/-! ## The local heat model -/

/-- The backward heat evolution `e^{D²}σ^k = Σ_{2m ≤ k} k!/(m!(k−2m)!) σ^{k−2m}` of `σ^k`. -/
def heatModel (k : ℕ) (σ : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (k / 2 + 1),
    ((k.factorial : ℂ) / ((m.factorial : ℂ) * ((k - 2 * m).factorial : ℂ))) * σ ^ (k - 2 * m)

/-- The part of `H^{(2m)}` near `z₀` of exact order `k − 2m`. -/
def jetPart (k : ℕ) (a : ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  if 2 * m ≤ k then a / ((k - 2 * m).factorial : ℂ) * w ^ (k - 2 * m) else 0

theorem sum_jetPart_eq (k : ℕ) (a : ℂ) (q : ℝ) (σ : ℂ) :
    ∑ m ∈ Finset.range (k + 1), ((q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) *
        jetPart k a m (q * σ) = a / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModel k σ := by
  have hsub : Finset.range (k / 2 + 1) ⊆ Finset.range (k + 1) := by
    intro m hm
    simp only [Finset.mem_range] at hm ⊢
    omega
  rw [← Finset.sum_subset hsub (fun m hm hm' => by
    simp only [Finset.mem_range] at hm hm'
    simp [jetPart, show ¬ 2 * m ≤ k by omega])]
  rw [heatModel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  have hm2 : 2 * m ≤ k := by omega
  simp only [jetPart, hm2, if_true]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hmf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hkm : ((k - 2 * m).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hq : ((q : ℂ) ^ 2) ^ m * (q : ℂ) ^ (k - 2 * m) = (q : ℂ) ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [mul_pow, ← hq]
  field_simp

/-- **The local heat model.** Let the derivatives of `H_s` (`s ≥ 0`) of order `< k` vanish at `z₀`
and `a = H_s^{(k)}(z₀)`. For every `S ≥ 0` there are `C` and `q₀ > 0` with
`‖H_{s−q²}(z₀ + qσ) − (a/k!) q^k P_k(σ)‖ ≤ C q^{k+1}` for `0 ≤ q ≤ q₀`, `q² ≤ s`, `‖σ‖ ≤ S`. -/
theorem exists_norm_riemannHeat_sub_heatModel_le {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) z₀ = 0) {S : ℝ} (hS : 0 ≤ S) :
    ∃ C q₀ : ℝ, 0 < q₀ ∧ ∀ q : ℝ, 0 ≤ q → q ≤ q₀ → q ^ 2 ≤ s → ∀ σ : ℂ, ‖σ‖ ≤ S →
      ‖riemannHeat (s - q ^ 2) (z₀ + q * σ) -
        iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModel k σ‖ ≤
        C * q ^ (k + 1) := by
  set H := riemannHeat s
  set a := iteratedDeriv k H z₀
  -- each even derivative is its jet part up to `O(|w|^{k+1−2m})`
  have hjet : ∀ m : ℕ, ∃ C r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w‖ ≤ r →
      ‖iteratedDeriv (2 * m) H (z₀ + w) - jetPart k a m w‖ ≤ C * ‖w‖ ^ (k + 1 - 2 * m) := by
    intro m
    have hd := differentiable_iteratedDeriv_riemannHeat hs (2 * m)
    by_cases hm : 2 * m ≤ k
    · have hv : ∀ i < k - 2 * m, iteratedDeriv i (iteratedDeriv (2 * m) H) z₀ = 0 := by
        intro i hi
        rw [iteratedDeriv_iteratedDeriv_eq]
        exact hvan _ (by omega)
      obtain ⟨C, r, hr, hb⟩ := exists_norm_sub_monomial_le hd hv
      refine ⟨C, r, hr, fun w hw => ?_⟩
      have h := hb w hw
      rw [iteratedDeriv_iteratedDeriv_eq, show k - 2 * m + 2 * m = k by omega] at h
      simp only [jetPart, hm, if_true]
      rw [show k + 1 - 2 * m = k - 2 * m + 1 by omega]
      exact h
    · obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
        hd.continuous.continuousOn
      refine ⟨B, 1, one_pos, fun w hw => ?_⟩
      simp only [jetPart, hm, if_false, sub_zero]
      rw [show k + 1 - 2 * m = 0 by omega, pow_zero, mul_one]
      exact hB _ (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hw)
  choose Cj rj hrj hjb using hjet
  set M := k + 1
  have hne : (Finset.range M).Nonempty := ⟨0, by simp [M]⟩
  set r₀ := (Finset.range M).inf' hne rj
  have hr₀ : 0 < r₀ := (Finset.lt_inf'_iff hne).mpr fun m _ => hrj m
  set S₁ := S + 1
  have hS₁ : 1 ≤ S₁ := by simp only [S₁]; linarith
  set q₀ := min 1 (min r₀ 1 / S₁)
  have hq₀ : 0 < q₀ := lt_min one_pos (div_pos (lt_min hr₀ one_pos) (by positivity))
  set K := ∫ x, |x| ^ (2 * M) * ‖heatWeight (s + 1) x‖ * Real.exp ((|z₀.im| + 1) * |x|)
  refine ⟨∑ m ∈ Finset.range M, |Cj m| * S₁ ^ (k + 1) + K, q₀, hq₀,
    fun q hq0 hq hqs σ hσ => ?_⟩
  have hq1 : q ≤ 1 := hq.trans (min_le_left _ _)
  set w : ℂ := q * σ with hw
  have hwn : ‖w‖ ≤ q * S₁ := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    gcongr
    simp only [S₁]; linarith
  have hwmin : ‖w‖ ≤ min r₀ 1 := by
    refine hwn.trans ?_
    have : q ≤ min r₀ 1 / S₁ := hq.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hwr : ‖w‖ ≤ r₀ := hwmin.trans (min_le_left _ _)
  have hw1 : ‖w‖ ≤ 1 := hwmin.trans (min_le_right _ _)
  -- the time expansion at `h = −q²`
  have hT := norm_riemannHeat_time_taylor_le hs (h := -(q ^ 2)) (by linarith)
    (by rw [abs_neg, abs_of_nonneg (sq_nonneg q)]; nlinarith) M (z₀ + w)
  rw [← sub_eq_add_neg] at hT
  have hcast : (-(((-(q ^ 2) : ℝ)) : ℂ)) = (q : ℂ) ^ 2 := by push_cast; ring
  rw [hcast, abs_neg, abs_of_nonneg (sq_nonneg q)] at hT
  have hKle : (∫ x, |x| ^ (2 * M) * ‖heatWeight (s + 1) x‖ *
      Real.exp (|(z₀ + w).im| * |x|)) ≤ K := by
    refine integral_mono (integrable_pow_mul_heatWeight (by linarith) _ _)
      (integrable_pow_mul_heatWeight (by linarith) _ _) fun x => ?_
    have him : |(z₀ + w).im| ≤ |z₀.im| + 1 := by
      rw [Complex.add_im]
      refine (abs_add_le _ _).trans ?_
      have := (Complex.abs_im_le_norm w).trans hw1
      linarith
    dsimp only
    gcongr
  have hK0 : 0 ≤ K := integral_nonneg fun x => by positivity
  have hq2M : (q ^ 2) ^ M ≤ q ^ (k + 1) := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hq0 hq1 (by simp only [M]; omega)
  -- the jet expansion of each even derivative
  have hpow : ∀ m : ℕ, q ^ (2 * m) * (q * S₁) ^ (M - 2 * m) ≤ S₁ ^ (k + 1) * q ^ (k + 1) := by
    intro m
    simp only [M]
    rw [mul_pow]
    by_cases hm : 2 * m ≤ k + 1
    · have e : q ^ (2 * m) * (q ^ (k + 1 - 2 * m) * S₁ ^ (k + 1 - 2 * m)) =
          q ^ (k + 1) * S₁ ^ (k + 1 - 2 * m) := by
        rw [← mul_assoc, ← pow_add, show 2 * m + (k + 1 - 2 * m) = k + 1 by omega]
      rw [e, mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS₁ (by omega)) (by positivity)
    · rw [show k + 1 - 2 * m = 0 by omega, pow_zero, pow_zero, mul_one, mul_one]
      calc q ^ (2 * m) ≤ q ^ (k + 1) := pow_le_pow_of_le_one hq0 hq1 (by omega)
        _ = 1 * q ^ (k + 1) := (one_mul _).symm
        _ ≤ S₁ ^ (k + 1) * q ^ (k + 1) := by gcongr; exact one_le_pow₀ hS₁
  have hjetsum : ‖∑ m ∈ Finset.range M, ((q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) *
      (iteratedDeriv (2 * m) H (z₀ + w) - jetPart k a m w)‖ ≤
        (∑ m ∈ Finset.range M, |Cj m| * S₁ ^ (k + 1)) * q ^ (k + 1) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    have hwm : ‖w‖ ≤ rj m := hwr.trans (Finset.inf'_le _ hm)
    have hb := hjb m w hwm
    have hfac : (1 : ℝ) ≤ m.factorial := by
      have : 1 ≤ m.factorial := Nat.factorial_pos m
      exact_mod_cast this
    rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq0, Complex.norm_natCast, ← pow_mul]
    calc q ^ (2 * m) / (m.factorial : ℝ) *
          ‖iteratedDeriv (2 * m) H (z₀ + w) - jetPart k a m w‖
        ≤ q ^ (2 * m) * (|Cj m| * (q * S₁) ^ (M - 2 * m)) := by
          gcongr
          · exact div_le_self (by positivity) hfac
          · exact hb.trans (by gcongr; exact le_abs_self _)
      _ = |Cj m| * (q ^ (2 * m) * (q * S₁) ^ (M - 2 * m)) := by ring
      _ ≤ |Cj m| * (S₁ ^ (k + 1) * q ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left (hpow m) (abs_nonneg _)
      _ = |Cj m| * S₁ ^ (k + 1) * q ^ (k + 1) := by ring
  -- assemble
  rw [← sum_jetPart_eq k a q σ, ← hw]
  have hsplit : riemannHeat (s - q ^ 2) (z₀ + w) -
      ∑ m ∈ Finset.range (k + 1), ((q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) * jetPart k a m w =
      (riemannHeat (s - q ^ 2) (z₀ + w) - ∑ m ∈ Finset.range M,
        ((q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) * iteratedDeriv (2 * m) H (z₀ + w)) +
      ∑ m ∈ Finset.range M, ((q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) *
        (iteratedDeriv (2 * m) H (z₀ + w) - jetPart k a m w) := by
    simp only [M, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc _ ≤ ‖riemannHeat (s - q ^ 2) (z₀ + w) - ∑ m ∈ Finset.range M,
        ((q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) * iteratedDeriv (2 * m) H (z₀ + w)‖ +
      ‖∑ m ∈ Finset.range M, ((q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) *
        (iteratedDeriv (2 * m) H (z₀ + w) - jetPart k a m w)‖ := norm_add_le _ _
    _ ≤ K * q ^ (k + 1) + (∑ m ∈ Finset.range M, |Cj m| * S₁ ^ (k + 1)) * q ^ (k + 1) := by
        gcongr
        refine hT.trans ?_
        calc _ ≤ K * (q ^ 2) ^ M := by gcongr
          _ ≤ K * q ^ (k + 1) := by gcongr
    _ = _ := by ring

end

end RHTower.DeBruijn
