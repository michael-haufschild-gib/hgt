import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCrossErrorOfTheBulkEntries

/-!
# The rows of a near pair sum

Pairs of atoms at log-distance `L = log(j/n) ∈ (αw, βw]` are organised by rows: the smaller index
`m` and the offset `h = j − m`, with `ℓ = log(1 + h/m)/w`. For a kernel `K` bounded by `A` and
`L_K`-Lipschitz on `[α, β]` and a `q`-periodic weight `p` bounded by `B`, one row is a Riemann sum:

`Σ_{h} p(m + h) K(ℓ)/√(m(m + h)) = p̄ · w ∫_α^β K(ℓ) e^{wℓ/2} dℓ + O(1/m)`,

uniformly in rows with local overlap `wm ≥ 1` (`abs_rowWindow_sub_le`). The proof averages the
periodic weight by Abel summation against its bounded mean-free primitive, compares the sum with
the integral on unit intervals, and substitutes `x = m(e^{wℓ} − 1)`, for which
`dx/√(m(m + x)) = w e^{wℓ/2} dℓ`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology Set
open scoped Real

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-! ### Periodic weights -/

/-- The mean of a `q`-periodic sequence. -/
def periodicMean (p : ℕ → ℝ) (q : ℕ) : ℝ := (∑ r ∈ range q, p r) / q

theorem sum_range_shift_of_periodic {p : ℕ → ℝ} {q : ℕ} (hper : ∀ n, p (n + q) = p n) (a : ℕ) :
    ∑ i ∈ range q, p (a + i) = ∑ i ∈ range q, p i := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun i => p (a + i)) q
    have h2 := Finset.sum_range_succ' (fun i => p (a + i)) q
    have e : ∑ i ∈ range q, p (a + 1 + i) = ∑ i ∈ range q, p (a + (i + 1)) :=
      Finset.sum_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]
    rw [e]
    have hq : p (a + q) = p (a + 0) := by rw [hper a, add_zero]
    linarith only [h1, h2, hq]

/-- The mean-free primitive of a shifted periodic sequence is bounded by `2qB`. -/
theorem abs_sum_range_shift_sub_mean_le {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hper : ∀ n, p (n + q) = p n) {B : ℝ} (hB : ∀ n, |p n| ≤ B) (a k : ℕ) :
    |∑ i ∈ range k, (p (a + i) - periodicMean p q)| ≤ 2 * q * B := by
  set v : ℕ → ℝ := fun i => p (a + i) - periodicMean p q with hv
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hvper : ∀ i, v (i + q) = v i := fun i => by
    simp only [hv, ← add_assoc, hper]
  have hvmean : ∑ i ∈ range q, v i = 0 := by
    simp only [hv, Finset.sum_sub_distrib, sum_range_shift_of_periodic hper, sum_const, card_range,
      nsmul_eq_mul, periodicMean]
    field_simp
    ring
  have hmul : ∀ t r : ℕ, ∑ i ∈ range (q * t + r), v i = ∑ i ∈ range r, v i := fun t r => by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show q * (t + 1) + r = (q * t + r) + q by ring, Finset.sum_range_add, ih]
      have hs : ∑ i ∈ range q, v (q * t + r + i) = ∑ i ∈ range q, v i := by
        have hvp : ∀ n, v (n + q) = v n := hvper
        exact sum_range_shift_of_periodic (p := v) hvp (q * t + r)
      rw [hs, hvmean, add_zero]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hvB : ∀ i, |v i| ≤ 2 * B := fun i => by
    have hm : |periodicMean p q| ≤ B := by
      rw [periodicMean, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ r ∈ range q, |p r| ≤ ∑ _r ∈ range q, B := Finset.sum_le_sum fun r _ => hB r
        _ = B * q := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    calc |v i| ≤ |p (a + i)| + |periodicMean p q| := abs_sub _ _
      _ ≤ 2 * B := by linarith only [hB (a + i), hm]
  rw [← Nat.div_add_mod k q, hmul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ range (k % q), |v i| ≤ ∑ _i ∈ range (k % q), 2 * B :=
        Finset.sum_le_sum fun i _ => hvB i
    _ = (k % q : ℕ) * (2 * B) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ q * (2 * B) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact_mod_cast (Nat.mod_lt k hq).le
    _ = 2 * q * B := by ring

/-- **Periodic averaging.** Against a weight of bounded variation a shifted periodic sequence is its
mean, up to `2qB` times the variation and the last value. -/
theorem abs_sum_range_mul_shift_sub_mean_le {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hper : ∀ n, p (n + q) = p n) {B : ℝ} (hB : ∀ n, |p n| ≤ B) (a : ℕ) (f : ℕ → ℝ) (M : ℕ) :
    |∑ i ∈ range (M + 1), f i * p (a + i) - periodicMean p q * ∑ i ∈ range (M + 1), f i| ≤
      2 * q * B * (|f M| + ∑ i ∈ range M, |f (i + 1) - f i|) := by
  have h := abs_sum_range_mul_le_real f (fun i => p (a + i) - periodicMean p q) M
    (B := 2 * q * B) (fun k _ => abs_sum_range_shift_sub_mean_le hq hper hB a (k + 1))
  have e : ∑ i ∈ range (M + 1), f i * (p (a + i) - periodicMean p q) =
      ∑ i ∈ range (M + 1), f i * p (a + i) - periodicMean p q * ∑ i ∈ range (M + 1), f i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rwa [e] at h

/-! ### Sums against integrals -/

/-- A Lipschitz function on `[a, a + M]` has Riemann sum within `λM` of its integral. -/
theorem abs_sum_range_sub_integral_le {f : ℝ → ℝ} {lam : ℝ} (a : ℝ) (M : ℕ)
    (hf : ∀ x ∈ Icc a (a + M), ∀ y ∈ Icc a (a + M), |f x - f y| ≤ lam * |x - y|) :
    |∑ i ∈ range M, f (a + i) - ∫ x in a..a + M, f x| ≤ lam * M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hsub : ∀ x ∈ Icc a (a + M), ∀ y ∈ Icc a (a + M), |f x - f y| ≤ lam * |x - y| :=
      fun x hx y hy => hf x ⟨hx.1, by push_cast; linarith [hx.2]⟩ y
        ⟨hy.1, by push_cast; linarith [hy.2]⟩
    have hlam : 0 ≤ lam := by
      have h := hf a ⟨le_rfl, by push_cast; linarith⟩ (a + 1) ⟨by linarith, by push_cast; linarith⟩
      have h1 : |a - (a + 1)| = 1 := by norm_num
      rw [h1, mul_one] at h
      exact (abs_nonneg _).trans h
    have hcont : ContinuousOn f (Icc a (a + (M + 1 : ℕ))) := by
      intro x hx
      refine Metric.continuousWithinAt_iff.mpr fun ε hε => ⟨ε / (lam + 1), by positivity,
        fun y hy hxy => ?_⟩
      rw [Real.dist_eq] at hxy ⊢
      calc |f y - f x| ≤ lam * |y - x| := hf y hy x hx
        _ ≤ lam * (ε / (lam + 1)) := mul_le_mul_of_nonneg_left hxy.le hlam
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
            nlinarith
    have hint : ∀ u v, u ∈ Icc a (a + (M + 1 : ℕ)) → v ∈ Icc a (a + (M + 1 : ℕ)) →
        IntervalIntegrable f volume u v := fun u v hu hv =>
      (hcont.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
    have hM : (a + M : ℝ) ∈ Icc a (a + (M + 1 : ℕ)) := ⟨by linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)],
      by push_cast; linarith⟩
    have ha : a ∈ Icc a (a + (M + 1 : ℕ)) := ⟨le_rfl, by push_cast; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]⟩
    have hM1 : (a + (M + 1 : ℕ) : ℝ) ∈ Icc a (a + (M + 1 : ℕ)) :=
      ⟨by push_cast; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)], le_rfl⟩
    rw [Finset.sum_range_succ, ← intervalIntegral.integral_add_adjacent_intervals
      (hint a (a + M) ha hM) (hint (a + M) (a + (M + 1 : ℕ)) hM hM1)]
    have hlast : |f (a + M) - ∫ x in a + M..a + (M + 1 : ℕ), f x| ≤ lam := by
      have hlen : (a + (M + 1 : ℕ) : ℝ) - (a + M) = 1 := by push_cast; ring
      have hconst : f (a + M) = ∫ _x in a + M..a + (M + 1 : ℕ), f (a + M) := by
        rw [intervalIntegral.integral_const, hlen, one_smul]
      rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
        (hint (a + M) (a + (M + 1 : ℕ)) hM hM1)]
      have hle : a + (M : ℝ) ≤ a + (M + 1 : ℕ) := by push_cast; linarith
      refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
      calc ∫ x in a + M..a + (M + 1 : ℕ), |f (a + M) - f x|
          ≤ ∫ _x in a + M..a + (M + 1 : ℕ), lam := by
            refine intervalIntegral.integral_mono_on hle ?_ intervalIntegrable_const fun x hx => ?_
            · exact ((continuousOn_const.sub hcont).abs.mono
                (Set.Icc_subset_Icc hM.1 le_rfl)).intervalIntegrable_of_Icc hle
            · have hxm : x ∈ Icc a (a + (M + 1 : ℕ)) := ⟨hM.1.trans hx.1, hx.2⟩
              calc |f (a + M) - f x| ≤ lam * |(a + M) - x| := hf _ hM _ hxm
                _ ≤ lam * 1 := by
                    refine mul_le_mul_of_nonneg_left ?_ hlam
                    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hlen]
                _ = lam := mul_one _
        _ = lam := by rw [intervalIntegral.integral_const, hlen, one_smul]
    have hih := ih hsub
    calc |∑ i ∈ range M, f (a + i) + f (a + M) - ((∫ x in a..a + M, f x) +
          ∫ x in a + M..a + (M + 1 : ℕ), f x)|
        ≤ |∑ i ∈ range M, f (a + i) - ∫ x in a..a + M, f x| +
          |f (a + M) - ∫ x in a + M..a + (M + 1 : ℕ), f x| := by
          rw [show ∑ i ∈ range M, f (a + i) + f (a + M) - ((∫ x in a..a + M, f x) +
            ∫ x in a + M..a + (M + 1 : ℕ), f x) = (∑ i ∈ range M, f (a + i) -
              ∫ x in a..a + M, f x) + (f (a + M) - ∫ x in a + M..a + (M + 1 : ℕ), f x) by ring]
          exact abs_add_le _ _
      _ ≤ lam * M + lam := add_le_add hih hlast
      _ = lam * (M + 1 : ℕ) := by push_cast; ring

/-! ### The row kernel -/

/-- The kernel of one row: `K(log(1 + x/m)/w)/√(m(m + x))`. -/
def rowKernel (K : ℝ → ℝ) (w : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  K (Real.log (1 + x / m) / w) / Real.sqrt (m * (m + x))

theorem abs_inv_sqrt_sub_le {m : ℝ} (hm : 0 < m) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |1 / Real.sqrt (m * (m + x)) - 1 / Real.sqrt (m * (m + y))| ≤ |x - y| / (2 * m ^ 2) := by
  have hX : m ≤ Real.sqrt (m * (m + x)) := by
    rw [Real.le_sqrt hm.le (by positivity)]; nlinarith
  have hY : m ≤ Real.sqrt (m * (m + y)) := by
    rw [Real.le_sqrt hm.le (by positivity)]; nlinarith
  have hX0 : 0 < Real.sqrt (m * (m + x)) := lt_of_lt_of_le hm hX
  have hY0 : 0 < Real.sqrt (m * (m + y)) := lt_of_lt_of_le hm hY
  have hdiff : Real.sqrt (m * (m + y)) - Real.sqrt (m * (m + x)) =
      m * (y - x) / (Real.sqrt (m * (m + y)) + Real.sqrt (m * (m + x))) := by
    rw [eq_div_iff (by positivity)]
    have h1 := Real.sq_sqrt (show 0 ≤ m * (m + y) by positivity)
    have h2 := Real.sq_sqrt (show 0 ≤ m * (m + x) by positivity)
    nlinarith
  rw [div_sub_div _ _ hX0.ne' hY0.ne', one_mul, mul_one, abs_div, abs_of_pos (mul_pos hX0 hY0),
    hdiff, abs_div, abs_mul, abs_of_pos hm, abs_of_pos (by positivity : (0:ℝ) <
      Real.sqrt (m * (m + y)) + Real.sqrt (m * (m + x))), abs_sub_comm y x,
    div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : 2 * m ≤ Real.sqrt (m * (m + y)) + Real.sqrt (m * (m + x)) := by linarith
  have h4 : m * m ≤ Real.sqrt (m * (m + x)) * Real.sqrt (m * (m + y)) := mul_le_mul hX hY hm.le
    hX0.le
  have hxy := abs_nonneg (x - y)
  calc m * |x - y| * (2 * m ^ 2) = |x - y| * (2 * m) * (m * m) := by ring
    _ ≤ |x - y| * (Real.sqrt (m * (m + y)) + Real.sqrt (m * (m + x))) *
        (Real.sqrt (m * (m + x)) * Real.sqrt (m * (m + y))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h3 hxy) h4 (by positivity) (by positivity)
    _ = _ := by ring

theorem abs_log_one_add_div_sub_le {m : ℝ} (hm : 0 < m) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.log (1 + x / m) - Real.log (1 + y / m)| ≤ |x - y| / m := by
  wlog hxy : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x y]; exact this hy hx (by linarith)
  have hpos : 0 < 1 + y / m := by positivity
  have hq : 0 < (1 + x / m) / (1 + y / m) := by positivity
  rw [← Real.log_div (by positivity) hpos.ne', abs_of_nonneg (Real.log_nonneg ?_),
    abs_of_nonneg (by linarith)]
  · refine (Real.log_le_sub_one_of_pos hq).trans ?_
    rw [div_sub_one hpos.ne', div_le_div_iff₀ hpos hm]
    have : (1 + x / m - (1 + y / m)) * m = x - y := by field_simp; ring
    rw [this]
    nlinarith [div_nonneg hy hm.le]
  · rw [le_div_iff₀ hpos, one_mul]
    exact add_le_add_left (div_le_div_of_nonneg_right hxy hm.le) 1

/-- **The row kernel is Lipschitz** on `x ≥ 0` whenever `K` is, on the range it reads. -/
theorem abs_rowKernel_sub_le {K : ℝ → ℝ} {A L w : ℝ} (hw : 0 < w) {m : ℕ} (hm : 1 ≤ m)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hKy : |K (Real.log (1 + y / m) / w)| ≤ A)
    (hKL : |K (Real.log (1 + x / m) / w) - K (Real.log (1 + y / m) / w)| ≤
      L * |Real.log (1 + x / m) / w - Real.log (1 + y / m) / w|) (hL : 0 ≤ L) :
    |rowKernel K w m x - rowKernel K w m y| ≤ (L / w + A / 2) / (m : ℝ) ^ 2 * |x - y| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hA : 0 ≤ A := (abs_nonneg _).trans hKy
  set gx := 1 / Real.sqrt (m * (m + x))
  set gy := 1 / Real.sqrt (m * (m + y))
  have hgx0 : 0 ≤ gx := by positivity
  have hgx : gx ≤ 1 / m := by
    apply one_div_le_one_div_of_le hm0
    rw [Real.le_sqrt hm0.le (by positivity)]; nlinarith
  have e : rowKernel K w m x - rowKernel K w m y =
      (K (Real.log (1 + x / m) / w) - K (Real.log (1 + y / m) / w)) * gx +
        K (Real.log (1 + y / m) / w) * (gx - gy) := by
    simp only [rowKernel, gx, gy]; ring
  rw [e]
  have hl : |Real.log (1 + x / m) / w - Real.log (1 + y / m) / w| ≤ |x - y| / (m * w) := by
    rw [← sub_div, abs_div, abs_of_pos hw, div_le_div_iff₀ hw (by positivity)]
    have := abs_log_one_add_div_sub_le hm0 hx hy
    rw [le_div_iff₀ hm0] at this
    nlinarith
  have hg := abs_inv_sqrt_sub_le hm0 hx hy
  calc |(K (Real.log (1 + x / m) / w) - K (Real.log (1 + y / m) / w)) * gx +
        K (Real.log (1 + y / m) / w) * (gx - gy)|
      ≤ |K (Real.log (1 + x / m) / w) - K (Real.log (1 + y / m) / w)| * gx +
          A * (|x - y| / (2 * (m : ℝ) ^ 2)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg hgx0]
        · rw [abs_mul]; exact mul_le_mul hKy hg (abs_nonneg _) hA
    _ ≤ L * (|x - y| / (m * w)) * (1 / m) + A * (|x - y| / (2 * (m : ℝ) ^ 2)) := by
        gcongr
        exact hKL.trans (mul_le_mul_of_nonneg_left hl hL)
    _ = (L / w + A / 2) / (m : ℝ) ^ 2 * |x - y| := by field_simp; ring

/-- **The logarithmic substitution**: `∫_a^b K(log(1 + x/m)/w)/√(m(m+x)) dx = w ∫_α^β K(ℓ) e^{wℓ/2} dℓ`
for `a = m(e^{αw} − 1)`, `b = m(e^{βw} − 1)`. -/
theorem integral_rowKernel_eq {K : ℝ → ℝ} {α β w : ℝ} (hw : 0 < w) (hαβ : α ≤ β)
    (hK : ContinuousOn K (Icc α β)) {m : ℕ} (hm : 1 ≤ m) :
    ∫ x in (m * (Real.exp (α * w) - 1))..(m * (Real.exp (β * w) - 1)), rowKernel K w m x =
      ∫ ℓ in α..β, K ℓ * (w * Real.exp (w * ℓ / 2)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set f : ℝ → ℝ := fun ℓ => m * (Real.exp (w * ℓ) - 1) with hf
  have hfα : f α = m * (Real.exp (α * w) - 1) := by simp only [hf, mul_comm w α]
  have hfβ : f β = m * (Real.exp (β * w) - 1) := by simp only [hf, mul_comm w β]
  have hderiv : ∀ ℓ ∈ uIcc α β, HasDerivAt f (m * (w * Real.exp (w * ℓ))) ℓ := by
    intro ℓ _
    have h := ((hasDerivAt_id ℓ).const_mul w).exp.sub_const 1 |>.const_mul (m : ℝ)
    simpa only [id, mul_one, mul_comm (Real.exp (w * ℓ)) w, hf] using h
  have hcont' : ContinuousOn (fun ℓ => m * (w * Real.exp (w * ℓ))) (uIcc α β) :=
    (continuous_const.mul (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)))).continuousOn
  have hpt : ∀ ℓ, rowKernel K w m (f ℓ) = K ℓ / (m * Real.exp (w * ℓ / 2)) := by
    intro ℓ
    have h1 : 1 + f ℓ / m = Real.exp (w * ℓ) := by simp only [hf]; field_simp; ring
    have h2 : (m : ℝ) * (m + f ℓ) = (m * Real.exp (w * ℓ / 2)) ^ 2 := by
      simp only [hf]
      rw [mul_pow, ← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (w * ℓ / 2) = w * ℓ by ring]
      ring
    rw [rowKernel, h1, Real.log_exp, mul_div_cancel_left₀ ℓ hw.ne', h2,
      Real.sqrt_sq (by positivity)]
  have hlogf : ∀ ℓ, Real.log (1 + f ℓ / m) / w = ℓ := by
    intro ℓ
    have h1 : 1 + f ℓ / m = Real.exp (w * ℓ) := by simp only [hf]; field_simp; ring
    rw [h1, Real.log_exp, mul_div_cancel_left₀ ℓ hw.ne']
  have hgcont : ContinuousOn (rowKernel K w m) (f '' uIcc α β) := by
    have hpos : ∀ x ∈ f '' uIcc α β, 0 < 1 + x / m := by
      rintro _ ⟨ℓ, -, rfl⟩
      have h1 : 1 + f ℓ / m = Real.exp (w * ℓ) := by simp only [hf]; field_simp; ring
      rw [h1]; exact Real.exp_pos _
    have hlog : ContinuousOn (fun x : ℝ => Real.log (1 + x / m) / w) (f '' uIcc α β) := by
      refine ContinuousOn.div_const (ContinuousOn.log ?_ fun x hx => (hpos x hx).ne') w
      exact (continuous_const.add (continuous_id.div_const _)).continuousOn
    have hmaps : MapsTo (fun x : ℝ => Real.log (1 + x / m) / w) (f '' uIcc α β) (Icc α β) := by
      rintro _ ⟨ℓ, hℓ, rfl⟩
      rw [uIcc_of_le hαβ] at hℓ
      simp only [hlogf]; exact hℓ
    have hsq : ContinuousOn (fun x : ℝ => Real.sqrt (m * (m + x))) (f '' uIcc α β) :=
      (continuous_const.mul (continuous_const.add continuous_id)).sqrt.continuousOn
    refine (hK.comp hlog hmaps).div hsq fun x hx => ?_
    have h := hpos x hx
    have : 0 < (m : ℝ) * (m + x) := by
      have : 0 < (m : ℝ) + x := by
        have := mul_pos hm0 h
        rwa [mul_add, mul_one, mul_div_cancel₀ x hm0.ne'] at this
      positivity
    exact (Real.sqrt_pos.mpr this).ne'
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hgcont
  rw [hfα, hfβ] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun ℓ _ => ?_
  simp only [Function.comp, hpt]
  have hE : Real.exp (w * ℓ) = Real.exp (w * ℓ / 2) * Real.exp (w * ℓ / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [hE]
  field_simp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
