import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard
import GaloisForLFunctions.HTGeometry.IteratedExponentialGrowthHeight
import GaloisForLFunctions.HTGeometry.TranscendentalEntireOrderOne

/-!
# Growth of Laurent polynomials in an exponential

For `a ≠ 0`, `p ∈ ℂ[X]` and `m ∈ ℕ` let `F(z) = p(e^{az}) / e^{maz}`.

* `F` has order at most one: `‖F z‖ ≤ exp(C (1 + ‖z‖))`.
* If `F` is nonconstant it has positive lower order.  If `deg p > m`, along the ray `az ∈ ℝ₊` the
  leading term gives `‖F z‖ ≥ κ e^{‖a‖ ‖z‖}`.  If `deg p ≤ m`, then `F(z) = p̃(e^{-az})` for the
  polynomial `p̃ = Σ c_k X^{m-k}`, and the same estimate holds along the opposite ray unless `p̃` is
  constant, in which case `F` is constant.
-/

open Filter Topology Metric Set Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

/-- The Laurent polynomial `p(t)/t^m` evaluated at `t = e^{az}`. -/
noncomputable def laurentExp (a : ℂ) (p : Polynomial ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  p.eval (Complex.exp (a * z)) / Complex.exp (a * z) ^ m

theorem differentiable_laurentExp (a : ℂ) (p : Polynomial ℂ) (m : ℕ) :
    Differentiable ℂ (laurentExp a p m) := by
  intro z
  have h1 : DifferentiableAt ℂ (fun z => Complex.exp (a * z)) z :=
    (differentiableAt_id.const_mul a).cexp
  exact ((p.differentiable.differentiableAt).comp z h1).div (h1.pow m)
    (pow_ne_zero m (Complex.exp_ne_zero _))

/-- A crude polynomial bound. -/
theorem norm_eval_le_sum_mul_max_pow (p : Polynomial ℂ) (t : ℂ) :
    ‖p.eval t‖ ≤ (∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖) *
      (max 1 ‖t‖) ^ p.natDegree := by
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_pow]
  have hk' : k ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖t‖ ^ k ≤ (max 1 ‖t‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k
    _ ≤ (max 1 ‖t‖) ^ p.natDegree := pow_le_pow_right₀ (le_max_left _ _) hk'

/-- **The leading term dominates far out.** -/
theorem exists_leading_lower_bound {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℂ, T ≤ ‖t‖ →
      ‖p.leadingCoeff‖ / 2 * ‖t‖ ^ p.natDegree ≤ ‖p.eval t‖ := by
  set d := p.natDegree
  set c := p.leadingCoeff
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp)
  rcases Nat.eq_zero_or_pos d with hd | hd
  · refine ⟨1, le_refl _, fun t _ => ?_⟩
    have hc0 : c = p.coeff 0 := by
      simp only [c, leadingCoeff]; rw [show p.natDegree = 0 from hd]
    rw [hd, pow_zero, mul_one, eq_C_of_natDegree_eq_zero hd, eval_C, ← hc0]
    linarith
  set S := ∑ k ∈ Finset.range d, ‖p.coeff k‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨max 1 (2 * S / ‖c‖), le_max_left _ _, fun t ht => ?_⟩
  have ht1 : 1 ≤ ‖t‖ := le_trans (le_max_left _ _) ht
  have htS : 2 * S / ‖c‖ ≤ ‖t‖ := le_trans (le_max_right _ _) ht
  have hsplit : p.eval t = c * t ^ d + ∑ k ∈ Finset.range d, p.coeff k * t ^ k := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, add_comm]
    rfl
  have hlow : ‖∑ k ∈ Finset.range d, p.coeff k * t ^ k‖ ≤ S * ‖t‖ ^ (d - 1) := by
    rw [hS, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1
      (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk))) (norm_nonneg _)
  have hpow : ‖t‖ ^ d = ‖t‖ * ‖t‖ ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  have hSt : S ≤ ‖c‖ / 2 * ‖t‖ := by
    rw [div_le_iff₀ hc] at htS
    linarith
  have htd1 : 0 ≤ ‖t‖ ^ (d - 1) := by positivity
  have hmain : ‖c‖ * ‖t‖ ^ d - S * ‖t‖ ^ (d - 1) ≤ ‖p.eval t‖ := by
    rw [hsplit]
    have := norm_sub_norm_le (c * t ^ d) (-(∑ k ∈ Finset.range d, p.coeff k * t ^ k))
    rw [sub_neg_eq_add, norm_neg, norm_mul, norm_pow] at this
    linarith
  calc ‖c‖ / 2 * ‖t‖ ^ d = ‖c‖ * ‖t‖ ^ d - ‖c‖ / 2 * ‖t‖ * ‖t‖ ^ (d - 1) := by rw [hpow]; ring
    _ ≤ ‖c‖ * ‖t‖ ^ d - S * ‖t‖ ^ (d - 1) := by nlinarith
    _ ≤ ‖p.eval t‖ := hmain

/-- **Exponential-type upper bound.** -/
theorem exists_norm_laurentExp_le (a : ℂ) (p : Polynomial ℂ) (m : ℕ) :
    ∃ S K : ℝ, 0 ≤ S ∧ 0 ≤ K ∧ ∀ z, ‖laurentExp a p m z‖ ≤ S * Real.exp (K * ‖z‖) := by
  set S := ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set K := ((p.natDegree + m : ℕ) : ℝ) * ‖a‖ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨S, K, hS0, hK0, fun z => ?_⟩
  set E := Complex.exp (a * z)
  have hEre : |(a * z).re| ≤ ‖a‖ * ‖z‖ := by
    calc |(a * z).re| ≤ ‖a * z‖ := abs_re_le_norm _
      _ = ‖a‖ * ‖z‖ := norm_mul _ _
  have hEle : max 1 ‖E‖ ≤ Real.exp (‖a‖ * ‖z‖) := by
    rw [Complex.norm_exp]
    refine max_le (Real.one_le_exp (by positivity)) (Real.exp_le_exp.mpr (le_of_abs_le hEre))
  have hEinv : ‖E‖⁻¹ ≤ Real.exp (‖a‖ * ‖z‖) := by
    rw [Complex.norm_exp, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (a * z).re])
  have hp := norm_eval_le_sum_mul_max_pow p E
  rw [laurentExp, norm_div, norm_pow, div_eq_mul_inv, ← inv_pow]
  have hA : (max 1 ‖E‖) ^ p.natDegree ≤ Real.exp (‖a‖ * ‖z‖) ^ p.natDegree :=
    pow_le_pow_left₀ (by positivity) hEle _
  have hB : (‖E‖⁻¹) ^ m ≤ Real.exp (‖a‖ * ‖z‖) ^ m :=
    pow_le_pow_left₀ (by positivity) hEinv _
  calc ‖p.eval E‖ * (‖E‖⁻¹) ^ m
      ≤ (S * (max 1 ‖E‖) ^ p.natDegree) * (‖E‖⁻¹) ^ m :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ (S * Real.exp (‖a‖ * ‖z‖) ^ p.natDegree) * Real.exp (‖a‖ * ‖z‖) ^ m := by
        gcongr
    _ = S * Real.exp (K * ‖z‖) := by
        rw [mul_assoc, ← pow_add, ← Real.exp_nat_mul, hK]
        push_cast
        ring_nf

/-- **Order at most one.** -/
theorem finiteOrderEnvelope_laurentExp (a : ℂ) (p : Polynomial ℂ) (m : ℕ) :
    FiniteOrderEnvelope (laurentExp a p m) := by
  obtain ⟨S, K, hS0, hK0, h1⟩ := exists_norm_laurentExp_le a p m
  refine ⟨S + K, 1, by positivity, fun z => ?_⟩
  calc ‖laurentExp a p m z‖ ≤ S * Real.exp (K * ‖z‖) := h1 z
    _ ≤ Real.exp S * Real.exp (K * ‖z‖) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp S]) (by positivity)
    _ = Real.exp (S + K * ‖z‖) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((S + K) * (1 + ‖z‖) ^ 1) := by
        rw [pow_one]
        exact Real.exp_le_exp.mpr (by nlinarith [norm_nonneg z])

/-- **Order at most one, sharp form**: for every `δ > 1` the maximum modulus is eventually at most
`exp(r^δ)`. -/
theorem eventually_norm_laurentExp_le_exp_rpow (a : ℂ) (p : Polynomial ℂ) (m : ℕ) {δ : ℝ}
    (hδ : 1 < δ) : ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r →
      ‖laurentExp a p m z‖ ≤ Real.exp (r ^ δ) := by
  obtain ⟨S, K, hS0, hK0, h1⟩ := exists_norm_laurentExp_le a p m
  have hlin : ∀ᶠ r : ℝ in atTop, S + K * r ≤ r ^ δ := by
    have ht : Tendsto (fun r : ℝ => r ^ (δ - 1)) atTop atTop := tendsto_rpow_atTop (by linarith)
    filter_upwards [ht.eventually_ge_atTop (S + K + 1), eventually_ge_atTop (1 : ℝ)] with r hr hr1
    have hr0 : 0 < r := by linarith
    have hsplit : r ^ δ = r * r ^ (δ - 1) := by
      rw [show δ = 1 + (δ - 1) by ring, Real.rpow_add hr0, Real.rpow_one]
      ring_nf
    rw [hsplit]
    nlinarith
  filter_upwards [hlin] with r hr z hz
  calc ‖laurentExp a p m z‖ ≤ S * Real.exp (K * ‖z‖) := h1 z
    _ ≤ Real.exp S * Real.exp (K * r) := mul_le_mul (by linarith [Real.add_one_le_exp S])
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hK0)) (by positivity) (by positivity)
    _ = Real.exp (S + K * r) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (r ^ δ) := Real.exp_le_exp.mpr hr

/-- The ray on which `a z = r ‖a‖`. -/
theorem mul_ray_eq {a : ℂ} (ha : a ≠ 0) (r : ℝ) :
    a * ((r : ℂ) * ((starRingEnd ℂ) a / (‖a‖ : ℂ))) = ((r * ‖a‖ : ℝ) : ℂ) := by
  have hna : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr ha).ne'
  have h : a * (starRingEnd ℂ) a = (‖a‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  calc a * ((r : ℂ) * ((starRingEnd ℂ) a / (‖a‖ : ℂ)))
      = (r : ℂ) * (a * (starRingEnd ℂ) a) / (‖a‖ : ℂ) := by ring
    _ = (r : ℂ) * (‖a‖ : ℂ) ^ 2 / (‖a‖ : ℂ) := by rw [h]
    _ = ((r * ‖a‖ : ℝ) : ℂ) := by push_cast; field_simp

theorem norm_ray {a : ℂ} (ha : a ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    ‖(r : ℂ) * ((starRingEnd ℂ) a / (‖a‖ : ℂ))‖ = r := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [norm_mul, norm_div, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_pos hna, div_self hna.ne', mul_one]

/-- **Exponential growth on a ray beats every `exp(r^δ)` with `δ < 1`.** -/
theorem eventually_exp_rpow_le_of_ray_bound {F : ℂ → ℂ} {κ b δ : ℝ} (hκ : 0 < κ) (hb : 0 < b)
    (hδ : δ < 1) (h : ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖ ≤ r ∧ κ * Real.exp (b * r) ≤ ‖F z‖) :
    ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖ ≤ r ∧ Real.exp (r ^ δ) ≤ ‖F z‖ := by
  have hlog : ∀ᶠ r : ℝ in atTop, Real.log (1 / κ) ≤ b * r / 2 := by
    have : Tendsto (fun r : ℝ => b * r / 2) atTop atTop :=
      (tendsto_id.const_mul_atTop hb).atTop_div_const (by norm_num)
    exact this.eventually_ge_atTop _
  have hpow : ∀ᶠ r : ℝ in atTop, r ^ δ ≤ b * r / 2 := by
    have ht : Tendsto (fun r : ℝ => r ^ (-(1 - δ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    filter_upwards [ht.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < b / 2)),
      eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hsplit : r ^ δ = r * r ^ (-(1 - δ)) := by
      rw [show δ = 1 + -(1 - δ) by ring, Real.rpow_add hr0, Real.rpow_one]
      ring_nf
    rw [hsplit]
    nlinarith
  filter_upwards [h, hlog, hpow] with r hr hl hs
  obtain ⟨z, hz, hFz⟩ := hr
  refine ⟨z, hz, le_trans ?_ hFz⟩
  have hk : Real.exp (Real.log (1 / κ)) = 1 / κ := Real.exp_log (by positivity)
  calc Real.exp (r ^ δ) ≤ Real.exp (b * r - Real.log (1 / κ)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = κ * Real.exp (b * r) := by
        rw [Real.exp_sub, hk]
        field_simp

/-- **Exponential growth on a ray gives positive lower order.** -/
theorem positiveLowerOrder_of_ray_bound {F : ℂ → ℂ} {κ b : ℝ} (hκ : 0 < κ) (hb : 0 < b)
    (h : ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖ ≤ r ∧ κ * Real.exp (b * r) ≤ ‖F z‖) :
    PositiveLowerOrder F := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [eventually_exp_rpow_le_of_ray_bound hκ hb (by norm_num : (1 / 2 : ℝ) < 1) h]
    with r hr
  simpa [iterExp] using hr

/-- **Exponential growth along a ray.**  A nonconstant `p(e^{az}) / e^{maz}` has modulus at least
`κ e^{‖a‖ r}` at some point of every disc of large radius `r`. -/
theorem exists_ray_bound_laurentExp {a : ℂ} (ha : a ≠ 0) {p : Polynomial ℂ} {m : ℕ}
    (hnc : ∃ z w, laurentExp a p m z ≠ laurentExp a p m w) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖ ≤ r ∧
      κ * Real.exp (‖a‖ * r) ≤ ‖laurentExp a p m z‖ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hp : p ≠ 0 := by
    rintro rfl
    obtain ⟨z, w, h⟩ := hnc
    simp [laurentExp] at h
  by_cases hdm : m < p.natDegree
  · -- the leading term along `a z ∈ ℝ₊`
    obtain ⟨T, hT1, hT⟩ := exists_leading_lower_bound hp
    have hc : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp)
    refine ⟨‖p.leadingCoeff‖ / 2, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (Real.log T / ‖a‖), eventually_ge_atTop (0 : ℝ)] with r hr
      hr0
    refine ⟨(r : ℂ) * ((starRingEnd ℂ) a / (‖a‖ : ℂ)), (norm_ray ha hr0).le, ?_⟩
    rw [laurentExp, mul_ray_eq ha r, ← Complex.ofReal_exp]
    set t := Real.exp (r * ‖a‖) with ht
    have ht1 : 1 ≤ t := Real.one_le_exp (by positivity)
    have htT : T ≤ ‖(t : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc T = Real.exp (Real.log T) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (r * ‖a‖) := Real.exp_le_exp.mpr (by
            rw [div_le_iff₀ hna] at hr; linarith)
    have hlow := hT (t : ℂ) htT
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hlow
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have htm : 0 < t ^ m := by positivity
    rw [le_div_iff₀ htm]
    have hdeg : t ^ m * t ≤ t ^ p.natDegree := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ ht1 hdm
    have : ‖a‖ * r = r * ‖a‖ := mul_comm _ _
    rw [this, ← ht]
    calc ‖p.leadingCoeff‖ / 2 * t * t ^ m = ‖p.leadingCoeff‖ / 2 * (t ^ m * t) := by ring
      _ ≤ ‖p.leadingCoeff‖ / 2 * t ^ p.natDegree := by gcongr
      _ ≤ ‖p.eval (t : ℂ)‖ := hlow
  · -- the reflected polynomial along `a z ∈ ℝ₋`
    push Not at hdm
    set q : Polynomial ℂ := ∑ k ∈ Finset.range (p.natDegree + 1), C (p.coeff k) * X ^ (m - k)
      with hq
    have hqeval : ∀ s : ℂ, s ≠ 0 → q.eval s = p.eval s⁻¹ / s⁻¹ ^ m := by
      intro s hs
      rw [hq, eval_finsetSum, eval_eq_sum_range, Finset.sum_div]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkm : k ≤ m := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hdm
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      rw [mul_div_assoc]
      congr 1
      rw [inv_pow, inv_pow, pow_sub₀ _ hs hkm]
      field_simp
    have hFq : ∀ z, laurentExp a p m z = q.eval (Complex.exp (-(a * z))) := by
      intro z
      rw [hqeval _ (Complex.exp_ne_zero _), Complex.exp_neg, inv_inv, laurentExp]
    by_cases hq0 : q.natDegree = 0
    · exfalso
      obtain ⟨z, w, h⟩ := hnc
      rw [hFq, hFq, eq_C_of_natDegree_eq_zero hq0, eval_C, eval_C] at h
      exact h rfl
    have hqne : q ≠ 0 := by
      intro h; rw [h] at hq0; exact hq0 natDegree_zero
    obtain ⟨T, hT1, hT⟩ := exists_leading_lower_bound hqne
    have hc : 0 < ‖q.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hqne)
    refine ⟨‖q.leadingCoeff‖ / 2, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (Real.log T / ‖a‖), eventually_ge_atTop (0 : ℝ)] with r hr
      hr0
    refine ⟨-((r : ℂ) * ((starRingEnd ℂ) a / (‖a‖ : ℂ))), by rw [norm_neg]; exact (norm_ray ha hr0).le,
      ?_⟩
    rw [hFq, mul_neg, neg_neg, mul_ray_eq ha r, ← Complex.ofReal_exp]
    set t := Real.exp (r * ‖a‖) with ht
    have ht1 : 1 ≤ t := Real.one_le_exp (by positivity)
    have htT : T ≤ ‖(t : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc T = Real.exp (Real.log T) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (r * ‖a‖) := Real.exp_le_exp.mpr (by
            rw [div_le_iff₀ hna] at hr; linarith)
    have hlow := hT (t : ℂ) htT
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hlow
    have : ‖a‖ * r = r * ‖a‖ := mul_comm _ _
    rw [this, ← ht]
    have hdeg : t ≤ t ^ q.natDegree := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ q.natDegree := pow_le_pow_right₀ ht1 (Nat.one_le_iff_ne_zero.mpr hq0)
    calc ‖q.leadingCoeff‖ / 2 * t ≤ ‖q.leadingCoeff‖ / 2 * t ^ q.natDegree := by gcongr
      _ ≤ ‖q.eval (t : ℂ)‖ := hlow

/-- **Positive lower order.** -/
theorem positiveLowerOrder_laurentExp {a : ℂ} (ha : a ≠ 0) {p : Polynomial ℂ} {m : ℕ}
    (hnc : ∃ z w, laurentExp a p m z ≠ laurentExp a p m w) :
    PositiveLowerOrder (laurentExp a p m) := by
  obtain ⟨κ, hκ, h⟩ := exists_ray_bound_laurentExp ha hnc
  exact positiveLowerOrder_of_ray_bound hκ (norm_pos_iff.mpr ha) h

/-- **Lower order at least one**: for every `δ < 1` the maximum modulus eventually exceeds
`exp(r^δ)`. -/
theorem eventually_exp_rpow_le_norm_laurentExp {a : ℂ} (ha : a ≠ 0) {p : Polynomial ℂ} {m : ℕ}
    (hnc : ∃ z w, laurentExp a p m z ≠ laurentExp a p m w) {δ : ℝ} (hδ : δ < 1) :
    ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖ ≤ r ∧ Real.exp (r ^ δ) ≤ ‖laurentExp a p m z‖ := by
  obtain ⟨κ, hκ, h⟩ := exists_ray_bound_laurentExp ha hnc
  exact eventually_exp_rpow_le_of_ray_bound hκ (norm_pos_iff.mpr ha) hδ h

end GaloisForLFunctions.HTGeometry
