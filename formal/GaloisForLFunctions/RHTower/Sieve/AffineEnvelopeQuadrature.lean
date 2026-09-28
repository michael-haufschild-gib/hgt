import Mathlib

/-!
# Affine envelopes and polynomial integrals

Upper bounds for integrals of products of logarithms and reciprocals by products of affine
envelopes: the tangent line above the concave `log`, the chord above the convex `-log` and the
convex `x ↦ 1/x`.  The integral of a product of affine functions is a polynomial in the
endpoints.  Together with two-sided series bounds for `log` near `1`, this bounds such integrals
by explicit rational numbers.
-/

namespace RHTower.Sieve

open Real intervalIntegral

/-- The tangent line of `log` at `m` lies above `log`. -/
theorem log_le_tangent {t m : ℝ} (ht : 0 < t) (hm : 0 < m) : log t ≤ log m + (t - m) / m := by
  have h := Real.log_le_sub_one_of_pos (div_pos ht hm)
  rw [Real.log_div ht.ne' hm.ne'] at h
  have e : t / m - 1 = (t - m) / m := by field_simp
  linarith

/-- The tangent line with an upper bound for the value at the contact point. -/
theorem log_le_tangent_of_le {t m U : ℝ} (ht : 0 < t) (hm : 0 < m) (hU : log m ≤ U) :
    log t ≤ U + (t - m) / m := by
  linarith [log_le_tangent ht hm]

/-- The chord of `log` on `[a, b]` lies below `log` (concavity). -/
theorem chord_le_log {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) (hab : a < b) :
    ((b - x) * log a + (x - a) * log b) / (b - a) ≤ log x := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hc := strictConcaveOn_log_Ioi.concaveOn
  have h := hc.2 (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 (ha.trans hab))
    (div_nonneg (sub_nonneg.2 hxb) hba.le) (div_nonneg (sub_nonneg.2 hax) hba.le)
    (by field_simp; ring)
  simp only [smul_eq_mul] at h
  have hx : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp; ring
  rw [hx] at h
  calc ((b - x) * log a + (x - a) * log b) / (b - a)
      = (b - x) / (b - a) * log a + (x - a) / (b - a) * log b := by field_simp
    _ ≤ log x := h

/-- The chord of the convex `-log`, with lower bounds for `log` at the endpoints. -/
theorem neg_log_le_chord_of_le {a b x La Lb : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (hab : a < b) (hLa : La ≤ log a) (hLb : Lb ≤ log b) :
    -log x ≤ -((b - x) * La + (x - a) * Lb) / (b - a) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h := chord_le_log ha hax hxb hab
  have h2 : (b - x) * La + (x - a) * Lb ≤ (b - x) * log a + (x - a) * log b := by
    have := mul_le_mul_of_nonneg_left hLa (sub_nonneg.2 hxb)
    have := mul_le_mul_of_nonneg_left hLb (sub_nonneg.2 hax)
    linarith
  have h3 : ((b - x) * La + (x - a) * Lb) / (b - a) ≤ log x :=
    (div_le_div_of_nonneg_right h2 hba.le).trans h
  rw [neg_div]
  linarith

/-- The chord of `1/x` on `[a, b] ⊂ (0, ∞)` lies above it. -/
theorem one_div_le_chord {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    1 / x ≤ (a + b - x) / (a * b) := by
  have hx : 0 < x := ha.trans_le hax
  have hb : 0 < b := hx.trans_le hxb
  rw [div_le_div_iff₀ hx (mul_pos ha hb)]
  nlinarith [mul_nonneg (sub_nonneg.2 hax) (sub_nonneg.2 hxb)]

/-- The integral of a product of two affine functions. -/
theorem integral_affine_mul_affine (a b p q r s : ℝ) :
    ∫ x in a..b, (p + q * x) * (r + s * x) =
      p * r * (b - a) + (p * s + q * r) * (b ^ 2 - a ^ 2) / 2 + q * s * (b ^ 3 - a ^ 3) / 3 := by
  have e : (fun x : ℝ => (p + q * x) * (r + s * x)) =
      fun x => (p * r + (p * s + q * r) * x ^ 1) + q * s * x ^ 2 := by
    funext x; ring
  rw [e, integral_add ((by fun_prop : Continuous fun x : ℝ => p * r + (p * s + q * r) * x ^ 1).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => q * s * x ^ 2).intervalIntegrable _ _),
    integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => (p * s + q * r) * x ^ 1).intervalIntegrable _ _)]
  simp only [integral_const, integral_const_mul, integral_pow, smul_eq_mul]
  ring

/-- The integral of a product of three affine functions. -/
theorem integral_affine_mul_affine_mul_affine (a b p q r s u v : ℝ) :
    ∫ x in a..b, (p + q * x) * (r + s * x) * (u + v * x) =
      p * r * u * (b - a) + (p * r * v + p * s * u + q * r * u) * (b ^ 2 - a ^ 2) / 2
        + (p * s * v + q * r * v + q * s * u) * (b ^ 3 - a ^ 3) / 3
        + q * s * v * (b ^ 4 - a ^ 4) / 4 := by
  have e : (fun x : ℝ => (p + q * x) * (r + s * x) * (u + v * x)) =
      fun x => ((p * r * u + (p * r * v + p * s * u + q * r * u) * x ^ 1)
        + (p * s * v + q * r * v + q * s * u) * x ^ 2) + q * s * v * x ^ 3 := by
    funext x; ring
  rw [e, integral_add ((by fun_prop : Continuous fun x : ℝ => (p * r * u + (p * r * v + p * s * u + q * r * u) * x ^ 1)
        + (p * s * v + q * r * v + q * s * u) * x ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => q * s * v * x ^ 3).intervalIntegrable _ _),
    integral_add ((by fun_prop : Continuous fun x : ℝ => p * r * u + (p * r * v + p * s * u + q * r * u) * x ^ 1).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => (p * s * v + q * r * v + q * s * u) * x ^ 2).intervalIntegrable _ _),
    integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => (p * r * v + p * s * u + q * r * u) * x ^ 1).intervalIntegrable _ _)]
  simp only [integral_const, integral_const_mul, integral_pow, smul_eq_mul]
  ring

/-- Series lower bound for `log` above `1`: with `y = (x-1)/(x+1)`,
`2(y + y³/3 + y⁵/5 + y⁷/7) ≤ log x`. -/
theorem log_ge_series {x : ℝ} (hx : 1 ≤ x) :
    2 * (((x - 1) / (x + 1)) + ((x - 1) / (x + 1)) ^ 3 / 3 + ((x - 1) / (x + 1)) ^ 5 / 5
      + ((x - 1) / (x + 1)) ^ 7 / 7) ≤ log x := by
  set y := (x - 1) / (x + 1) with hy
  have hx1 : 0 < x + 1 := by linarith
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hx1.le
  have hy1 : y < 1 := (div_lt_one hx1).2 (by linarith)
  have habs : |y| < 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hxy : log (1 + y) - log (1 - y) = log x := by
    have h1 : 1 + y = 2 * x / (x + 1) := by rw [hy]; field_simp; ring
    have h2 : 1 - y = 2 / (x + 1) := by rw [hy]; field_simp; ring
    rw [h1, h2, ← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  rw [hxy] at hS
  have hle := sum_le_hasSum (Finset.range 4) (fun i _ => by positivity) hS
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  norm_num at hle
  linarith

/-- Series upper bound for `log` above `1`: with `y = (x-1)/(x+1)`,
`log x ≤ 2(y + y³/3 + y⁵/5 + y⁷/7) + 2y⁹/(9(1-y²))`. -/
theorem log_le_series {x : ℝ} (hx : 1 ≤ x) :
    log x ≤ 2 * (((x - 1) / (x + 1)) + ((x - 1) / (x + 1)) ^ 3 / 3
      + ((x - 1) / (x + 1)) ^ 5 / 5 + ((x - 1) / (x + 1)) ^ 7 / 7)
      + 2 * ((x - 1) / (x + 1)) ^ 9 / (9 * (1 - ((x - 1) / (x + 1)) ^ 2)) := by
  set y := (x - 1) / (x + 1) with hy
  have hx1 : 0 < x + 1 := by linarith
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hx1.le
  have hy1 : y < 1 := (div_lt_one hx1).2 (by linarith)
  have habs : |y| < 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hxy : log (1 + y) - log (1 - y) = log x := by
    have h1 : 1 + y = 2 * x / (x + 1) := by rw [hy]; field_simp; ring
    have h2 : 1 - y = 2 / (x + 1) := by rw [hy]; field_simp; ring
    rw [h1, h2, ← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  rw [hxy] at hS
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  -- tail comparison with a geometric series
  have htail := (hasSum_nat_add_iff' 4).2 hS
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at htail
  have hgeo : HasSum (fun k : ℕ => 2 * (1 / 9) * y ^ 9 * (y ^ 2) ^ k)
      (2 * (1 / 9) * y ^ 9 * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  have hcmp := hasSum_le (fun k => by
      have hk : (9 : ℝ) ≤ 2 * ((k + 4 : ℕ) : ℝ) + 1 := by push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
      have hpow : y ^ (2 * (k + 4) + 1) = y ^ 9 * (y ^ 2) ^ k := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      rw [hpow]
      have h9 : 0 ≤ y ^ 9 * (y ^ 2) ^ k := by positivity
      have : 1 / (2 * ((k + 4 : ℕ) : ℝ) + 1) ≤ 1 / 9 :=
        one_div_le_one_div_of_le (by norm_num) hk
      nlinarith) htail hgeo
  have e : 2 / 9 * y ^ 9 * (1 - y ^ 2)⁻¹ = 2 * y ^ 9 / (9 * (1 - y ^ 2)) := by
    field_simp
  norm_num at hcmp
  linarith

/-- The chord of `x ↦ log (p + q x)` on `[a, b]` lies below it (concavity). -/
theorem chord_le_log_affine {p q a b x : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b)
    (hpa : 0 < p + q * a) (hpb : 0 < p + q * b) :
    ((b - x) * log (p + q * a) + (x - a) * log (p + q * b)) / (b - a) ≤ log (p + q * x) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hpa) (Set.mem_Ioi.2 hpb)
    (div_nonneg (sub_nonneg.2 hxb) hba.le) (div_nonneg (sub_nonneg.2 hax) hba.le)
    (by field_simp; ring)
  simp only [smul_eq_mul] at h
  have hx : (b - x) / (b - a) * (p + q * a) + (x - a) / (b - a) * (p + q * b) = p + q * x := by
    field_simp; ring
  rw [hx] at h
  calc ((b - x) * log (p + q * a) + (x - a) * log (p + q * b)) / (b - a)
      = (b - x) / (b - a) * log (p + q * a) + (x - a) / (b - a) * log (p + q * b) := by
        field_simp
    _ ≤ log (p + q * x) := h

/-- The chord above `x ↦ -log (p + q x)` on `[a, b]`, with lower bounds for `log` at the ends. -/
theorem neg_log_affine_le_chord {p q a b x La Lb : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b)
    (hpa : 0 < p + q * a) (hpb : 0 < p + q * b)
    (hLa : La ≤ log (p + q * a)) (hLb : Lb ≤ log (p + q * b)) :
    -log (p + q * x) ≤ -((b - x) * La + (x - a) * Lb) / (b - a) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h := chord_le_log_affine hab hax hxb hpa hpb
  have h2 : (b - x) * La + (x - a) * Lb ≤ (b - x) * log (p + q * a) + (x - a) * log (p + q * b) := by
    have := mul_le_mul_of_nonneg_left hLa (sub_nonneg.2 hxb)
    have := mul_le_mul_of_nonneg_left hLb (sub_nonneg.2 hax)
    linarith
  have h3 := (div_le_div_of_nonneg_right h2 hba.le).trans h
  rw [neg_div]
  linarith

/-- The tangent line above `x ↦ log (p + q x)` at `m`, with an upper bound for the value there. -/
theorem log_affine_le_tangent {p q m x U : ℝ} (hx : 0 < p + q * x) (hm : 0 < p + q * m)
    (hU : log (p + q * m) ≤ U) :
    log (p + q * x) ≤ U + q * (x - m) / (p + q * m) := by
  have h := log_le_tangent_of_le hx hm hU
  have e : (p + q * x - (p + q * m)) / (p + q * m) = q * (x - m) / (p + q * m) := by ring
  linarith

/-- The chord coefficients of `x ↦ 1/x + 1/(1-x)` on `[a, b] ⊂ (0,1)`. -/
noncomputable def logitWeightConst (a b : ℝ) : ℝ :=
  (a + b) / (a * b) + (1 - a - b) / ((1 - a) * (1 - b))

/-- The slope of the chord of `x ↦ 1/x + 1/(1-x)` on `[a, b]`. -/
noncomputable def logitWeightSlope (a b : ℝ) : ℝ :=
  1 / ((1 - a) * (1 - b)) - 1 / (a * b)

theorem logit_weight_le_chord {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) (hb : b < 1) :
    1 / x + 1 / (1 - x) ≤ logitWeightConst a b + logitWeightSlope a b * x := by
  have h1 := one_div_le_chord ha hax hxb
  have h2 := one_div_le_chord (a := 1 - b) (b := 1 - a) (x := 1 - x) (by linarith)
    (by linarith) (by linarith)
  have hab : 0 < a * b := mul_pos ha (by linarith)
  have hab' : 0 < (1 - a) * (1 - b) := mul_pos (by linarith) (by linarith)
  have e1 : (a + b - x) / (a * b) = (a + b) / (a * b) - 1 / (a * b) * x := by ring
  have e2 : (1 - b + (1 - a) - (1 - x)) / ((1 - b) * (1 - a))
      = (1 - a - b) / ((1 - a) * (1 - b)) + 1 / ((1 - a) * (1 - b)) * x := by
    rw [mul_comm (1 - b)]; ring
  unfold logitWeightConst logitWeightSlope
  rw [e1] at h1
  rw [e2] at h2
  linarith

/-- A cell bound: if `Φ ≤ A + B x` on `[a, b] ⊂ (0,1)` and the affine envelope is nonnegative at
both ends, the integral of `Φ · (1/x + 1/(1-x))` is at most an explicit polynomial expression. -/
theorem integral_mul_logit_weight_le {Φ : ℝ → ℝ} {a b A B : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < 1) (hΦc : ContinuousOn Φ (Set.Icc a b)) (hΦ : ∀ x ∈ Set.Icc a b, Φ x ≤ A + B * x)
    (hA : 0 ≤ A + B * a) (hB : 0 ≤ A + B * b) :
    ∫ x in a..b, Φ x * (1 / x + 1 / (1 - x)) ≤
      A * logitWeightConst a b * (b - a)
        + (A * logitWeightSlope a b + B * logitWeightConst a b) * (b ^ 2 - a ^ 2) / 2
        + B * logitWeightSlope a b * (b ^ 3 - a ^ 3) / 3 := by
  rw [← integral_affine_mul_affine]
  have hcont : ContinuousOn (fun x => Φ x * (1 / x + 1 / (1 - x))) (Set.Icc a b) := by
    refine hΦc.mul (ContinuousOn.add ?_ ?_)
    · exact continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')
    · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
        (fun x hx => by have := hx.2; linarith)
  refine integral_mono_on hab.le (hcont.intervalIntegrable_of_Icc hab.le)
    ((by fun_prop : Continuous fun x : ℝ =>
      (A + B * x) * (logitWeightConst a b + logitWeightSlope a b * x)).intervalIntegrable _ _) ?_
  intro x hx
  have hx0 : 0 < x := ha.trans_le hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hw0 : 0 ≤ 1 / x + 1 / (1 - x) := by positivity
  have hAB : 0 ≤ A + B * x := by
    have hba : 0 < b - a := sub_pos.2 hab
    have e : A + B * x = ((b - x) * (A + B * a) + (x - a) * (A + B * b)) / (b - a) := by
      field_simp; ring
    rw [e]
    exact div_nonneg (add_nonneg (mul_nonneg (sub_nonneg.2 hx.2) hA)
      (mul_nonneg (sub_nonneg.2 hx.1) hB)) hba.le
  have hw := logit_weight_le_chord ha hx.1 hx.2 hb
  calc Φ x * (1 / x + 1 / (1 - x)) ≤ (A + B * x) * (1 / x + 1 / (1 - x)) :=
        mul_le_mul_of_nonneg_right (hΦ x hx) hw0
    _ ≤ (A + B * x) * (logitWeightConst a b + logitWeightSlope a b * x) :=
        mul_le_mul_of_nonneg_left hw hAB

/-- The lower series polynomial for `log`, in the variable `y = (x-1)/(x+1)`. -/
noncomputable def logSeriesLower (x : ℝ) : ℝ :=
  2 * (((x - 1) / (x + 1)) + ((x - 1) / (x + 1)) ^ 3 / 3 + ((x - 1) / (x + 1)) ^ 5 / 5
    + ((x - 1) / (x + 1)) ^ 7 / 7)

/-- The upper series bound for `log`, in the variable `y = (x-1)/(x+1)`. -/
noncomputable def logSeriesUpper (x : ℝ) : ℝ :=
  logSeriesLower x + 2 * ((x - 1) / (x + 1)) ^ 9 / (9 * (1 - ((x - 1) / (x + 1)) ^ 2))

theorem logSeriesLower_le_log {x : ℝ} (hx : 1 ≤ x) : logSeriesLower x ≤ log x :=
  log_ge_series hx

theorem log_le_logSeriesUpper {x : ℝ} (hx : 1 ≤ x) : log x ≤ logSeriesUpper x := by
  unfold logSeriesUpper logSeriesLower
  exact log_le_series hx

/-- Lower bound for `log v` from `log 2 > 0.6931471803` and the series at `v / 2^k`. -/
noncomputable def logLower (k : ℕ) (v : ℝ) : ℝ := k * (6931471803 / 10 ^ 10) + logSeriesLower (v / 2 ^ k)

/-- Upper bound for `log v` from `log 2 < 0.6931471808` and the series at `v / 2^k`. -/
noncomputable def logUpper (k : ℕ) (v : ℝ) : ℝ := k * (6931471808 / 10 ^ 10) + logSeriesUpper (v / 2 ^ k)

/-- Lower bound for `log v`, `v ≤ 1`, through `log v = -log (1/v)`. -/
noncomputable def logLowerInv (k : ℕ) (v : ℝ) : ℝ := -logUpper k (1 / v)

/-- Upper bound for `log v`, `v ≤ 1`, through `log v = -log (1/v)`. -/
noncomputable def logUpperInv (k : ℕ) (v : ℝ) : ℝ := -logLower k (1 / v)

theorem logLower_le_log (k : ℕ) {v : ℝ} (h : 2 ^ k ≤ v) : logLower k v ≤ log v := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hv : 0 < v := h2k.trans_le h
  have e : log v = k * log 2 + log (v / 2 ^ k) := by
    rw [Real.log_div hv.ne' h2k.ne', Real.log_pow]; ring
  have h1 : 1 ≤ v / 2 ^ k := (one_le_div h2k).2 h
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hk
  unfold logLower
  rw [e]
  nlinarith [logSeriesLower_le_log h1]

theorem log_le_logUpper (k : ℕ) {v : ℝ} (h : 2 ^ k ≤ v) : log v ≤ logUpper k v := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hv : 0 < v := h2k.trans_le h
  have e : log v = k * log 2 + log (v / 2 ^ k) := by
    rw [Real.log_div hv.ne' h2k.ne', Real.log_pow]; ring
  have h1 : 1 ≤ v / 2 ^ k := (one_le_div h2k).2 h
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hk
  unfold logUpper
  rw [e]
  nlinarith [log_le_logSeriesUpper h1]

theorem logLowerInv_le_log (k : ℕ) {v : ℝ} (h : 2 ^ k ≤ 1 / v) : logLowerInv k v ≤ log v := by
  have e : log v = -log (1 / v) := by rw [one_div, Real.log_inv]; ring
  unfold logLowerInv
  rw [e]
  linarith [log_le_logUpper k h]

theorem log_le_logUpperInv (k : ℕ) {v : ℝ} (h : 2 ^ k ≤ 1 / v) : log v ≤ logUpperInv k v := by
  have e : log v = -log (1 / v) := by rw [one_div, Real.log_inv]; ring
  unfold logUpperInv
  rw [e]
  linarith [logLower_le_log k h]

/-- Constant term of the chord through `(a, La)` and `(b, Lb)`. -/
noncomputable def chordConst (La Lb a b : ℝ) : ℝ := (b * La - a * Lb) / (b - a)

/-- Slope of the chord through `(a, La)` and `(b, Lb)`. -/
noncomputable def chordSlope (La Lb a b : ℝ) : ℝ := (Lb - La) / (b - a)

/-- Constant term of the tangent of `x ↦ log (p + q x)` at `m`, with value bound `U`. -/
noncomputable def tangentConst (U p q m : ℝ) : ℝ := U - q * m / (p + q * m)

/-- Slope of the tangent of `x ↦ log (p + q x)` at `m`. -/
noncomputable def tangentSlope (p q m : ℝ) : ℝ := q / (p + q * m)

/-- The chord envelope of `-log (p + q x)` in affine form. -/
theorem neg_log_affine_le_chord' {p q a b x La Lb : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b)
    (hpa : 0 < p + q * a) (hpb : 0 < p + q * b)
    (hLa : La ≤ log (p + q * a)) (hLb : Lb ≤ log (p + q * b)) :
    -log (p + q * x) ≤ -chordConst La Lb a b - chordSlope La Lb a b * x := by
  have h := neg_log_affine_le_chord hab hax hxb hpa hpb hLa hLb
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have e : -((b - x) * La + (x - a) * Lb) / (b - a)
      = -chordConst La Lb a b - chordSlope La Lb a b * x := by
    unfold chordConst chordSlope; field_simp; ring
  linarith

/-- The tangent envelope of `log (p + q x)` in affine form. -/
theorem log_affine_le_tangent' {p q m x U : ℝ} (hx : 0 < p + q * x) (hm : 0 < p + q * m)
    (hU : log (p + q * m) ≤ U) :
    log (p + q * x) ≤ tangentConst U p q m + tangentSlope p q m * x := by
  have h := log_affine_le_tangent hx hm hU
  have e : U + q * (x - m) / (p + q * m) = tangentConst U p q m + tangentSlope p q m * x := by
    unfold tangentConst tangentSlope; field_simp; ring
  linarith

/-- The cell bound of `integral_mul_logit_weight_le` as a function of the envelope. -/
noncomputable def logitCellBound (A B a b : ℝ) : ℝ :=
  A * logitWeightConst a b * (b - a)
    + (A * logitWeightSlope a b + B * logitWeightConst a b) * (b ^ 2 - a ^ 2) / 2
    + B * logitWeightSlope a b * (b ^ 3 - a ^ 3) / 3

/-- The integral of `(A + B x)/x` over `[a, b] ⊂ (0, ∞)`, bounded through the chord of `1/x`. -/
theorem integral_affine_div_le_chord {a b A B : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hA : 0 ≤ A + B * a) (hB : 0 ≤ A + B * b) :
    ∫ x in a..b, (A + B * x) / x ≤
      A * ((a + b) / (a * b)) * (b - a)
        + (A * (-1 / (a * b)) + B * ((a + b) / (a * b))) * (b ^ 2 - a ^ 2) / 2
        + B * (-1 / (a * b)) * (b ^ 3 - a ^ 3) / 3 := by
  rw [← integral_affine_mul_affine]
  have hb : 0 < b := ha.trans_le hab
  refine integral_mono_on hab ?_ ((by fun_prop : Continuous fun x : ℝ =>
    (A + B * x) * ((a + b) / (a * b) + -1 / (a * b) * x)).intervalIntegrable _ _) ?_
  · refine ContinuousOn.intervalIntegrable_of_Icc hab ?_
    exact (by fun_prop : Continuous fun x : ℝ => A + B * x).continuousOn.div continuousOn_id
      (fun x hx => (ha.trans_le hx.1).ne')
  · intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    have hAB : 0 ≤ A + B * x := by
      rcases eq_or_lt_of_le hab with h | h
      · have : x = a := le_antisymm (h ▸ hx.2) hx.1
        rw [this]; exact hA
      · have hba : 0 < b - a := sub_pos.2 h
        have e : A + B * x = ((b - x) * (A + B * a) + (x - a) * (A + B * b)) / (b - a) := by
          field_simp; ring
        rw [e]
        exact div_nonneg (add_nonneg (mul_nonneg (sub_nonneg.2 hx.2) hA)
          (mul_nonneg (sub_nonneg.2 hx.1) hB)) hba.le
    have hch := one_div_le_chord ha hx.1 hx.2
    have e : (a + b - x) / (a * b) = (a + b) / (a * b) + -1 / (a * b) * x := by ring
    rw [e] at hch
    calc (A + B * x) / x = (A + B * x) * (1 / x) := by ring
      _ ≤ (A + B * x) * ((a + b) / (a * b) + -1 / (a * b) * x) :=
          mul_le_mul_of_nonneg_left hch hAB

end RHTower.Sieve
