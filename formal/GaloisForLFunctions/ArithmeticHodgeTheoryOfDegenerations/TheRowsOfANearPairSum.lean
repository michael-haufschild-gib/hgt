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
    linarith [div_le_div_of_nonneg_right hxy hm.le]

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
    _ = (L / w + A / 2) / (m : ℝ) ^ 2 * |x - y| := by field_simp

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

/-! ### One row -/

/-- One row: the offsets `1 ≤ h ≤ N − m` with `log(1 + h/m) ∈ (αw, βw]`, weighted by `p(m + h)`. -/
def rowWindow (K : ℝ → ℝ) (α β w : ℝ) (N m : ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Icc 1 (N - m), if α * w < Real.log (1 + h / m) ∧ Real.log (1 + h / m) ≤ β * w then
    p (m + h) * rowKernel K w m h else 0

theorem log_window_iff {α β w : ℝ} {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 0 ≤ x) :
    (α * w < Real.log (1 + x / m) ∧ Real.log (1 + x / m) ≤ β * w) ↔
      (m * (Real.exp (α * w) - 1) < x ∧ x ≤ m * (Real.exp (β * w) - 1)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < 1 + x / m := by positivity
  rw [Real.lt_log_iff_exp_lt hpos, Real.log_le_iff_le_exp hpos]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : Real.exp (α * w) - 1 < x / m := by linarith
      rwa [lt_div_iff₀ hm0, mul_comm] at this
    · have : x / m ≤ Real.exp (β * w) - 1 := by linarith
      rwa [div_le_iff₀ hm0, mul_comm] at this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : Real.exp (α * w) - 1 < x / m := by rw [lt_div_iff₀ hm0, mul_comm]; exact h1
      linarith
    · have : x / m ≤ Real.exp (β * w) - 1 := by rw [div_le_iff₀ hm0, mul_comm]; exact h2
      linarith

theorem log_div_mem_Icc {α β w : ℝ} (hw : 0 < w) {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ Icc (m * (Real.exp (α * w) - 1)) (m * (Real.exp (β * w) - 1))) :
    Real.log (1 + x / m) / w ∈ Icc α β := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < 1 + x / m := by
    have : -m < x := lt_of_lt_of_le (by nlinarith [Real.exp_pos (α * w)]) hx.1
    have : -1 < x / m := by rw [lt_div_iff₀ hm0]; linarith
    linarith
  constructor
  · rw [le_div_iff₀ hw, Real.le_log_iff_exp_le hpos]
    have : Real.exp (α * w) - 1 ≤ x / m := by rw [le_div_iff₀ hm0, mul_comm]; exact hx.1
    linarith
  · rw [div_le_iff₀ hw, Real.log_le_iff_le_exp hpos]
    have : x / m ≤ Real.exp (β * w) - 1 := by rw [div_le_iff₀ hm0, mul_comm]; exact hx.2
    linarith

/-- **One row is a Riemann sum.** For a kernel bounded by `A` and `L`-Lipschitz on `[α, β]` and a
`q`-periodic weight bounded by `B`, a row that fits below the horizon is
`p̄ · w ∫_α^β K(ℓ) e^{wℓ/2} dℓ` up to `(2q + 1)B(4A + 2βL)/m`. -/
theorem abs_rowWindow_sub_le {K : ℝ → ℝ} {α β A L w : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hw : 0 < w)
    (hβw : β * w ≤ 1) (hA : ∀ ℓ ∈ Icc α β, |K ℓ| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|) (hL0 : 0 ≤ L)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hper : ∀ n, p (n + q) = p n) {B : ℝ} (hB : ∀ n, |p n| ≤ B)
    {N m : ℕ} (hm : 1 ≤ m) (htop : (m : ℝ) * (Real.exp (β * w) - 1) ≤ (N - m : ℕ)) :
    |rowWindow K α β w N m p - periodicMean p q * ∫ ℓ in α..β, K ℓ * (w * Real.exp (w * ℓ / 2))| ≤
      (2 * q + 1) * B * (4 * A + 2 * β * L) / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA α ⟨le_rfl, hαβ⟩)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hβ0 : 0 ≤ β := hα.trans hαβ
  set a : ℝ := m * (Real.exp (α * w) - 1) with ha
  set b : ℝ := m * (Real.exp (β * w) - 1) with hb
  have ha0 : 0 ≤ a := mul_nonneg hm0.le (by
    have := Real.add_one_le_exp (α * w); nlinarith [mul_nonneg hα hw.le])
  have hab : a ≤ b := mul_le_mul_of_nonneg_left (by
    have := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hαβ hw.le); linarith) hm0.le
  have hbw : b ≤ 2 * β * w * m := by
    have h := Real.abs_exp_sub_one_le (x := β * w) (by
      rw [abs_of_nonneg (mul_nonneg hβ0 hw.le)]; exact hβw)
    rw [abs_of_nonneg (mul_nonneg hβ0 hw.le)] at h
    have h' : Real.exp (β * w) - 1 ≤ 2 * (β * w) := (le_abs_self _).trans h
    calc b = m * (Real.exp (β * w) - 1) := rfl
      _ ≤ m * (2 * (β * w)) := mul_le_mul_of_nonneg_left h' hm0.le
      _ = 2 * β * w * m := by ring
  -- the mean, the kernel and its constants
  have hmean : |periodicMean p q| ≤ B := by
    rw [periodicMean, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ range q, |p r| ≤ ∑ _r ∈ range q, B := Finset.sum_le_sum fun r _ => hB r
      _ = B * q := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  set lam : ℝ := (L / w + A / 2) / (m : ℝ) ^ 2 with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hfl : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |rowKernel K w m x - rowKernel K w m y| ≤ lam * |x - y| := by
    intro x hx y hy
    have hx0 : 0 ≤ x := ha0.trans hx.1
    have hy0 : 0 ≤ y := ha0.trans hy.1
    exact abs_rowKernel_sub_le hw hm hx0 hy0 (hA _ (log_div_mem_Icc hw hm hy))
      (hL _ (log_div_mem_Icc hw hm hx) _ (log_div_mem_Icc hw hm hy)) hL0
  have hfA : ∀ x ∈ Icc a b, |rowKernel K w m x| ≤ A / m := by
    intro x hx
    have hx0 : 0 ≤ x := ha0.trans hx.1
    have hK := hA _ (log_div_mem_Icc hw hm hx)
    have hs : (m : ℝ) ≤ Real.sqrt (m * (m + x)) := by
      rw [Real.le_sqrt hm0.le (by positivity)]; nlinarith
    rw [rowKernel, abs_div, abs_of_pos (lt_of_lt_of_le hm0 hs)]
    exact div_le_div₀ hA0 hK hm0 hs
  have hKcont : ContinuousOn K (Icc α β) := continuousOn_of_abs_sub_le hL
  have hint : ∫ x in a..b, rowKernel K w m x = ∫ ℓ in α..β, K ℓ * (w * Real.exp (w * ℓ / 2)) :=
    integral_rowKernel_eq hw hαβ hKcont hm
  have hfcont : ContinuousOn (rowKernel K w m) (Icc a b) := continuousOn_of_abs_sub_le hfl
  -- the row is a sum over an integer interval
  have hfilter : (Finset.Icc 1 (N - m)).filter (fun h : ℕ => α * w < Real.log (1 + h / m) ∧
      Real.log (1 + h / m) ≤ β * w) = Finset.Icc (⌊a⌋₊ + 1) ⌊b⌋₊ := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Icc, log_window_iff hm (Nat.cast_nonneg h)]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨Nat.succ_le_of_lt ((Nat.floor_lt ha0).mpr h1), Nat.le_floor h2⟩
    · rintro ⟨h1, h2⟩
      have hb0 : 0 ≤ b := ha0.trans hab
      have h2' : (h : ℝ) ≤ b := (Nat.le_floor_iff hb0).mp h2
      refine ⟨⟨by omega, ?_⟩, (Nat.floor_lt ha0).mp (by omega), h2'⟩
      exact_mod_cast h2'.trans htop
  have hrow : rowWindow K α β w N m p =
      ∑ h ∈ Finset.Icc (⌊a⌋₊ + 1) ⌊b⌋₊, p (m + h) * rowKernel K w m h := by
    rw [rowWindow, ← Finset.sum_filter, hfilter]
  have hbound : (2 * q + 1) * B * (4 * A + 2 * β * L) / m =
      (2 * q + 1) * B * (4 * A + 2 * β * L) * (1 / m) := by ring
  rw [hrow, ← hint]
  rcases lt_or_ge ⌊b⌋₊ (⌊a⌋₊ + 1) with hempty | hne
  · -- an empty row: the window is shorter than one
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, zero_sub, abs_neg, abs_mul]
    have hba : b - a < 1 := by
      have h1 := Nat.lt_floor_add_one b
      have h2 := Nat.floor_le ha0
      have h3 : (⌊b⌋₊ : ℝ) + 1 ≤ ⌊a⌋₊ + 1 := by exact_mod_cast hempty
      linarith
    have hI : |∫ x in a..b, rowKernel K w m x| ≤ A / m * (b - a) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
        (f := rowKernel K w m) (C := A / m) (fun x hx => by
          rw [uIoc_of_le hab] at hx
          exact hfA x ⟨hx.1.le, hx.2⟩)
      rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at this
    calc |periodicMean p q| * |∫ x in a..b, rowKernel K w m x|
        ≤ B * (A / m * 1) := mul_le_mul hmean (hI.trans (mul_le_mul_of_nonneg_left hba.le
          (by positivity))) (abs_nonneg _) hB0
      _ ≤ (2 * q + 1) * B * (4 * A + 2 * β * L) / m := by
          rw [mul_one, mul_div_assoc', hbound]
          have hq1 : (1 : ℝ) ≤ 2 * q + 1 := by linarith
          have hAA : A ≤ (2 * q + 1) * (4 * A + 2 * β * L) := by
            nlinarith [mul_nonneg hβ0 hL0]
          calc B * A / m = B * A * (1 / m) := by ring
            _ ≤ B * ((2 * q + 1) * (4 * A + 2 * β * L)) * (1 / m) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAA hB0) (by positivity)
            _ = (2 * q + 1) * B * (4 * A + 2 * β * L) * (1 / m) := by ring
  · -- a nonempty row
    set A₀ := ⌊a⌋₊ + 1 with hA₀
    set M := ⌊b⌋₊ - A₀ with hM
    have hA₀a : a < A₀ := by rw [hA₀]; push_cast; exact Nat.lt_floor_add_one a
    have hA₀a1 : (A₀ : ℝ) ≤ a + 1 := by rw [hA₀]; push_cast; linarith [Nat.floor_le ha0]
    have hb0 : 0 ≤ b := ha0.trans hab
    have hBb : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb0
    have hBb1 : b < ⌊b⌋₊ + 1 := Nat.lt_floor_add_one b
    have hMeq : ⌊b⌋₊ = A₀ + M := by omega
    have hMba : (M : ℝ) ≤ b - a := by
      have : (⌊b⌋₊ : ℝ) = A₀ + M := by exact_mod_cast hMeq
      linarith
    have hIcc : Finset.Icc A₀ ⌊b⌋₊ =
        (range (M + 1)).map ⟨fun i => A₀ + i, fun _ _ h => Nat.add_left_cancel h⟩ := by
      ext h
      simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h - A₀, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩; omega
    rw [hIcc, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    set f : ℕ → ℝ := fun i => rowKernel K w m ((A₀ + i : ℕ) : ℝ) with hf
    have hmem : ∀ i ≤ M, ((A₀ + i : ℕ) : ℝ) ∈ Icc a b := by
      intro i hi
      push_cast
      have : (i : ℝ) ≤ M := by exact_mod_cast hi
      have : (⌊b⌋₊ : ℝ) = A₀ + M := by exact_mod_cast hMeq
      constructor <;> linarith
    have hsum_eq : ∑ i ∈ range (M + 1), p (m + (A₀ + i)) * rowKernel K w m ((A₀ + i : ℕ) : ℝ) =
        ∑ i ∈ range (M + 1), f i * p (m + A₀ + i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf, ← add_assoc]; ring
    rw [hsum_eq]
    -- periodic averaging
    have havg := abs_sum_range_mul_shift_sub_mean_le hq hper hB (m + A₀) f M
    have hfM : |f M| ≤ A / m := hfA _ (hmem M le_rfl)
    have hvar : ∑ i ∈ range M, |f (i + 1) - f i| ≤ lam * M := by
      calc ∑ i ∈ range M, |f (i + 1) - f i| ≤ ∑ _i ∈ range M, lam := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : i < M := Finset.mem_range.mp hi
            have h := hfl _ (hmem (i + 1) hi') _ (hmem i hi'.le)
            have hd : |((A₀ + (i + 1) : ℕ) : ℝ) - ((A₀ + i : ℕ) : ℝ)| = 1 := by
              push_cast; ring_nf; norm_num
            rw [hd, mul_one] at h
            exact h
        _ = lam * M := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    -- the sum against the integral
    have hEM : |∑ i ∈ range (M + 1), f i - ∫ x in a..b, rowKernel K w m x| ≤ lam * M + 3 * (A / m) := by
      have hsplit : ∑ i ∈ range (M + 1), f i = ∑ i ∈ range M, rowKernel K w m ((A₀ : ℝ) + i) + f M := by
        rw [Finset.sum_range_succ]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [hf]; push_cast; ring_nf
      have hR := abs_sum_range_sub_integral_le (f := rowKernel K w m) (lam := lam) (A₀ : ℝ) M
        (fun x hx y hy => hfl x ⟨hA₀a.le.trans hx.1, hx.2.trans (by
          have : (⌊b⌋₊ : ℝ) = A₀ + M := by exact_mod_cast hMeq
          linarith)⟩ y ⟨hA₀a.le.trans hy.1, hy.2.trans (by
          have : (⌊b⌋₊ : ℝ) = A₀ + M := by exact_mod_cast hMeq
          linarith)⟩)
      have hBM : ((A₀ : ℝ) + M) = ⌊b⌋₊ := by exact_mod_cast hMeq.symm
      have hii : ∀ u v, u ∈ Icc a b → v ∈ Icc a b → IntervalIntegrable (rowKernel K w m) volume u v :=
        fun u v hu hv => (hfcont.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
      have hA₀mem : (A₀ : ℝ) ∈ Icc a b := ⟨hA₀a.le, by rw [← hBM] at hBb; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]⟩
      have hBmem : (⌊b⌋₊ : ℝ) ∈ Icc a b := ⟨by rw [← hBM]; linarith [hA₀mem.1, (Nat.cast_nonneg M : (0:ℝ) ≤ M)], hBb⟩
      have hamem : a ∈ Icc a b := ⟨le_rfl, hab⟩
      have hbmem : b ∈ Icc a b := ⟨hab, le_rfl⟩
      have hthree : ∫ x in a..b, rowKernel K w m x = (∫ x in a..(A₀ : ℝ), rowKernel K w m x) +
          (∫ x in (A₀ : ℝ)..(A₀ : ℝ) + M, rowKernel K w m x) +
          ∫ x in (⌊b⌋₊ : ℝ)..b, rowKernel K w m x := by
        rw [hBM, intervalIntegral.integral_add_adjacent_intervals (hii _ _ hamem hA₀mem)
          (hii _ _ hA₀mem hBmem), intervalIntegral.integral_add_adjacent_intervals
          (hii _ _ hamem hBmem) (hii _ _ hBmem hbmem)]
      have hlow : |∫ x in a..(A₀ : ℝ), rowKernel K w m x| ≤ A / m := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := (A₀ : ℝ))
          (f := rowKernel K w m) (C := A / m) (fun x hx => by
            rw [uIoc_of_le hA₀a.le] at hx
            exact hfA x ⟨hx.1.le, hx.2.trans hA₀mem.2⟩)
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hA₀a.le)] at this
        calc _ ≤ A / m * ((A₀ : ℝ) - a) := this
          _ ≤ A / m * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = A / m := mul_one _
      have hhigh : |∫ x in (⌊b⌋₊ : ℝ)..b, rowKernel K w m x| ≤ A / m := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (⌊b⌋₊ : ℝ)) (b := b)
          (f := rowKernel K w m) (C := A / m) (fun x hx => by
            rw [uIoc_of_le hBb] at hx
            exact hfA x ⟨hBmem.1.trans hx.1.le, hx.2⟩)
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hBb)] at this
        calc _ ≤ A / m * (b - ⌊b⌋₊) := this
          _ ≤ A / m * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = A / m := mul_one _
      rw [hsplit, hthree]
      have e : ∑ i ∈ range M, rowKernel K w m ((A₀ : ℝ) + i) + f M -
          ((∫ x in a..(A₀ : ℝ), rowKernel K w m x) +
            (∫ x in (A₀ : ℝ)..(A₀ : ℝ) + M, rowKernel K w m x) +
            ∫ x in (⌊b⌋₊ : ℝ)..b, rowKernel K w m x) =
          (∑ i ∈ range M, rowKernel K w m ((A₀ : ℝ) + i) -
            ∫ x in (A₀ : ℝ)..(A₀ : ℝ) + M, rowKernel K w m x) + f M -
          (∫ x in a..(A₀ : ℝ), rowKernel K w m x) - ∫ x in (⌊b⌋₊ : ℝ)..b, rowKernel K w m x := by
        ring
      rw [e]
      have hX := abs_sub ((∑ i ∈ range M, rowKernel K w m ((A₀ : ℝ) + i) -
            ∫ x in (A₀ : ℝ)..(A₀ : ℝ) + M, rowKernel K w m x) + f M -
          (∫ x in a..(A₀ : ℝ), rowKernel K w m x)) (∫ x in (⌊b⌋₊ : ℝ)..b, rowKernel K w m x)
      have hY := abs_sub ((∑ i ∈ range M, rowKernel K w m ((A₀ : ℝ) + i) -
            ∫ x in (A₀ : ℝ)..(A₀ : ℝ) + M, rowKernel K w m x) + f M)
          (∫ x in a..(A₀ : ℝ), rowKernel K w m x)
      have hZ := abs_add_le (∑ i ∈ range M, rowKernel K w m ((A₀ : ℝ) + i) -
            ∫ x in (A₀ : ℝ)..(A₀ : ℝ) + M, rowKernel K w m x) (f M)
      calc _ ≤ |∑ i ∈ range M, rowKernel K w m ((A₀ : ℝ) + i) -
              ∫ x in (A₀ : ℝ)..(A₀ : ℝ) + M, rowKernel K w m x| + |f M| +
            |∫ x in a..(A₀ : ℝ), rowKernel K w m x| +
            |∫ x in (⌊b⌋₊ : ℝ)..b, rowKernel K w m x| := by linarith only [hX, hY, hZ]
        _ ≤ lam * M + A / m + A / m + A / m := by gcongr
        _ = lam * M + 3 * (A / m) := by ring
    have hlamM : lam * M ≤ (2 * β * L + A) / m := by
      calc lam * M ≤ lam * (2 * β * w * m) :=
            mul_le_mul_of_nonneg_left (hMba.trans ((sub_le_self _ ha0).trans hbw)) hlam0
        _ = (2 * β * L + A * (β * w)) / m := by rw [hlam]; field_simp
        _ ≤ (2 * β * L + A) / m :=
            div_le_div_of_nonneg_right (add_le_add le_rfl (mul_le_of_le_one_right hA0 hβw)) hm0.le
    have hmain : |∑ i ∈ range (M + 1), f i * p (m + A₀ + i) -
        periodicMean p q * ∫ x in a..b, rowKernel K w m x| ≤
        2 * q * B * (A / m + lam * M) + B * (lam * M + 3 * (A / m)) := by
      have e : ∑ i ∈ range (M + 1), f i * p (m + A₀ + i) -
          periodicMean p q * ∫ x in a..b, rowKernel K w m x =
          (∑ i ∈ range (M + 1), f i * p (m + A₀ + i) - periodicMean p q * ∑ i ∈ range (M + 1), f i) +
            periodicMean p q * (∑ i ∈ range (M + 1), f i - ∫ x in a..b, rowKernel K w m x) := by ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add (havg.trans ?_) ?_)
      · exact mul_le_mul_of_nonneg_left (add_le_add hfM hvar) (by positivity)
      · rw [abs_mul]; exact mul_le_mul hmean hEM (abs_nonneg _) hB0
    refine hmain.trans ?_
    rw [hbound]
    have h1 : A / m + lam * M ≤ (2 * A + 2 * β * L) * (1 / m) := by
      calc A / m + lam * M ≤ A / m + (2 * β * L + A) / m := add_le_add le_rfl hlamM
        _ = (2 * A + 2 * β * L) * (1 / m) := by ring
    have h2 : lam * M + 3 * (A / m) ≤ (4 * A + 2 * β * L) * (1 / m) := by
      calc lam * M + 3 * (A / m) ≤ (2 * β * L + A) / m + 3 * (A / m) := add_le_add hlamM le_rfl
        _ = (4 * A + 2 * β * L) * (1 / m) := by ring
    have hm1 : (0 : ℝ) ≤ 1 / m := by positivity
    calc 2 * q * B * (A / m + lam * M) + B * (lam * M + 3 * (A / m))
        ≤ 2 * q * B * ((2 * A + 2 * β * L) * (1 / m)) + B * ((4 * A + 2 * β * L) * (1 / m)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
            (mul_le_mul_of_nonneg_left h2 hB0)
      _ ≤ (2 * q + 1) * B * (4 * A + 2 * β * L) * (1 / m) := by
          have h3 : 2 * q * B * ((2 * A + 2 * β * L) * (1 / m)) ≤
              2 * q * B * ((4 * A + 2 * β * L) * (1 / m)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right (by linarith) hm1
          calc 2 * q * B * ((2 * A + 2 * β * L) * (1 / m)) + B * ((4 * A + 2 * β * L) * (1 / m))
              ≤ 2 * q * B * ((4 * A + 2 * β * L) * (1 / m)) + B * ((4 * A + 2 * β * L) * (1 / m)) :=
                add_le_add h3 le_rfl
            _ = (2 * q + 1) * B * (4 * A + 2 * β * L) * (1 / m) := by ring

/-! ### Counting rows -/

theorem card_filter_lt_le (N : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    (((Finset.Icc 1 N).filter (fun m : ℕ => (m : ℝ) < X)).card : ℝ) ≤ X := by
  have hsub : (Finset.Icc 1 N).filter (fun m : ℕ => (m : ℝ) < X) ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1.1, Nat.le_floor hm.2.le⟩
  calc (((Finset.Icc 1 N).filter (fun m : ℕ => (m : ℝ) < X)).card : ℝ)
      ≤ ((Finset.Icc 1 ⌊X⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = ⌊X⌋₊ := by simp
    _ ≤ X := Nat.floor_le hX

theorem card_filter_gt_le (N : ℕ) {Y : ℝ} (hY : 0 ≤ Y) (hYN : Y ≤ N) :
    (((Finset.Icc 1 N).filter (fun m : ℕ => Y < m)).card : ℝ) ≤ N - Y + 1 := by
  have hsub : (Finset.Icc 1 N).filter (fun m : ℕ => Y < m) ⊆ Finset.Icc (⌊Y⌋₊ + 1) N := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨Nat.succ_le_of_lt ((Nat.floor_lt hY).mpr hm.2), hm.1.2⟩
  calc (((Finset.Icc 1 N).filter (fun m : ℕ => Y < m)).card : ℝ)
      ≤ ((Finset.Icc (⌊Y⌋₊ + 1) N).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = ((N + 1 - (⌊Y⌋₊ + 1) : ℕ) : ℝ) := by rw [Nat.card_Icc]
    _ ≤ N - Y + 1 := by
        rcases le_or_gt (⌊Y⌋₊ + 1) (N + 1) with h | h
        · rw [Nat.cast_sub h]; push_cast
          linarith [Nat.lt_floor_add_one Y]
        · rw [Nat.sub_eq_zero_of_le h.le]; push_cast
          linarith

/-- The harmonic tail from `X`: `Σ_{X ≤ m ≤ N} 1/m ≤ 1 + log(N/X)`. -/
theorem sum_filter_le_inv_le {N : ℕ} (hN : 1 ≤ N) {X : ℝ} (hX : 0 < X) (hXN : X ≤ N) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => X ≤ m), (1 / (m : ℝ)) ≤
      1 + Real.log (N / X) := by
  set m₀ := max 1 ⌈X⌉₊ with hm₀
  have hm₀1 : 1 ≤ m₀ := le_max_left _ _
  have hsub : (Finset.Icc 1 N).filter (fun m : ℕ => X ≤ m) ⊆ Finset.Icc m₀ N := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨max_le hm.1.1 (Nat.ceil_le.mpr hm.2), hm.1.2⟩
  have hle : ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => X ≤ m), (1 / (m : ℝ)) ≤
      ∑ m ∈ Finset.Icc m₀ N, (1 / (m : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  refine hle.trans ?_
  rcases le_or_gt m₀ N with hmN | hmN
  · have hsplit : ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) = ∑ m ∈ Finset.Icc 1 (m₀ - 1), (1 / (m : ℝ)) +
        ∑ m ∈ Finset.Icc m₀ N, (1 / (m : ℝ)) := by
      have h := Finset.sum_Ioc_consecutive (fun m : ℕ => 1 / (m : ℝ)) (Nat.zero_le (m₀ - 1))
        (show m₀ - 1 ≤ N by omega)
      have e1 : Finset.Ioc 0 N = Finset.Icc 1 N := by ext; simp; omega
      have e2 : Finset.Ioc 0 (m₀ - 1) = Finset.Icc 1 (m₀ - 1) := by ext; simp; omega
      have e3 : Finset.Ioc (m₀ - 1) N = Finset.Icc m₀ N := by ext; simp; omega
      rw [e1, e2, e3] at h
      exact h.symm
    have hH : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, (1 / (m : ℝ)) = harmonic n := fun n => by
      rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    have h1 := harmonic_le_one_add_log N
    have h2 := log_add_one_le_harmonic (m₀ - 1)
    rw [hH] at hsplit
    rw [hH] at hsplit
    rw [Nat.sub_add_cancel hm₀1] at h2
    have hlogm : Real.log X ≤ Real.log m₀ := by
      apply Real.log_le_log hX
      exact (Nat.le_ceil X).trans (by exact_mod_cast le_max_right 1 ⌈X⌉₊)
    rw [Real.log_div (by positivity) hX.ne']
    have : ∑ m ∈ Finset.Icc m₀ N, (1 / (m : ℝ)) = harmonic N - harmonic (m₀ - 1) := by
      linarith only [hsplit]
    rw [this]
    linarith only [h1, h2, hlogm]
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have h1 : 0 ≤ Real.log (N / X) := Real.log_nonneg (by rw [le_div_iff₀ hX]; linarith)
    linarith

/-! ### Pairs as rows -/

/-- A pair sum over the logarithmic window `(αw, βw]`, with a row weight `ρ` at the smaller index:
`Σ_{n,j} ρ(min(n,j)) u(n) v(j) K(|log(j/n)|/w)/√(nj)`. -/
def nearPairSum (K : ℝ → ℝ) (α β w : ℝ) (N : ℕ) (u v ρ : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
    if α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w then
      ρ (min n j) * u n * v j * K (|Real.log j - Real.log n| / w) / (Real.sqrt n * Real.sqrt j)
    else 0

theorem sum_Icc_ite_lt_eq (g : ℕ → ℝ) (n N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (if n < j then g j else 0) = ∑ h ∈ Finset.Icc 1 (N - n), g (n + h) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun j => j - n) (fun h => n + h) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    omega
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    omega
  · intro h _; omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    congr 1; omega

theorem log_add_sub_log {n h : ℕ} (hn : 1 ≤ n) :
    Real.log ((n + h : ℕ) : ℝ) - Real.log n = Real.log (1 + h / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn0.ne']
  congr 1; push_cast; field_simp

theorem sqrt_mul_sqrt_add {n h : ℕ} :
    Real.sqrt n * Real.sqrt ((n + h : ℕ) : ℝ) = Real.sqrt (n * (n + h)) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg n)]; push_cast; ring_nf

/-- **Pairs as rows.** Each unordered pair is read from its smaller index `m` with offset
`h = j − m`. -/
theorem nearPairSum_eq_rows (K : ℝ → ℝ) {α β w : ℝ} (hα : 0 ≤ α) (hw : 0 < w) (N : ℕ)
    (u v ρ : ℕ → ℝ) :
    nearPairSum K α β w N u v ρ = ∑ m ∈ Finset.Icc 1 N,
      ρ m * (u m * rowWindow K α β w N m v + v m * rowWindow K α β w N m u) := by
  set T : ℕ → ℕ → ℝ := fun n j =>
    if α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w then
      ρ (min n j) * u n * v j * K (|Real.log j - Real.log n| / w) / (Real.sqrt n * Real.sqrt j)
    else 0 with hT
  have hdiag : ∀ n, T n n = 0 := fun n => by
    simp only [hT, sub_self, abs_zero]
    rw [if_neg (fun h => absurd h.1 (not_lt.mpr (mul_nonneg hα hw.le)))]
  have hsplit : ∀ n j, T n j = (if n < j then T n j else 0) + (if j < n then T n j else 0) :=
    fun n j => by
      rcases lt_trichotomy n j with h | h | h
      · rw [if_pos h, if_neg (by omega), add_zero]
      · subst h; rw [hdiag, if_neg (lt_irrefl _), add_zero]
      · rw [if_neg (by omega), if_pos h, zero_add]
  have hup : ∀ n ∈ Finset.Icc 1 N, ∑ h ∈ Finset.Icc 1 (N - n), T n (n + h) =
      ρ n * (u n * rowWindow K α β w N n v) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [rowWindow, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hlog : |Real.log ((n + h : ℕ) : ℝ) - Real.log n| = Real.log (1 + h / n) := by
      rw [log_add_sub_log hn1]
      exact abs_of_nonneg (Real.log_nonneg (by linarith [show (0:ℝ) ≤ h / n by positivity]))
    simp only [hT, hlog, min_eq_left (Nat.le_add_right n h), sqrt_mul_sqrt_add]
    split_ifs <;> simp [rowKernel]; ring
  have hdown : ∀ j ∈ Finset.Icc 1 N, ∑ h ∈ Finset.Icc 1 (N - j), T (j + h) j =
      ρ j * (v j * rowWindow K α β w N j u) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [rowWindow, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hlog : |Real.log j - Real.log ((j + h : ℕ) : ℝ)| = Real.log (1 + h / j) := by
      rw [abs_sub_comm, log_add_sub_log hj1]
      exact abs_of_nonneg (Real.log_nonneg (by linarith [show (0:ℝ) ≤ h / j by positivity]))
    simp only [hT, hlog, min_eq_right (Nat.le_add_right j h)]
    rw [mul_comm (Real.sqrt ((j + h : ℕ) : ℝ)), sqrt_mul_sqrt_add]
    split_ifs <;> simp [rowKernel]; ring
  calc nearPairSum K α β w N u v ρ = ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, T n j := rfl
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (if n < j then T n j else 0) +
        ∑ j ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (if j < n then T n j else 0) := by
        rw [Finset.sum_comm (s := Finset.Icc 1 N) (t := Finset.Icc 1 N)
          (f := fun j n => if j < n then T n j else 0), ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun n _ => by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => hsplit n j
    _ = ∑ m ∈ Finset.Icc 1 N, ρ m * (u m * rowWindow K α β w N m v) +
        ∑ m ∈ Finset.Icc 1 N, ρ m * (v m * rowWindow K α β w N m u) := by
        congr 1
        · refine Finset.sum_congr rfl fun n hn => ?_
          rw [sum_Icc_ite_lt_eq (fun j => T n j) n N, hup n hn]
        · refine Finset.sum_congr rfl fun j hj => ?_
          rw [sum_Icc_ite_lt_eq (fun n => T n j) j N, hdown j hj]
    _ = _ := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun m _ => by ring

/-! ### The pair sum -/

theorem rowWindow_eq_zero_of_lt {K : ℝ → ℝ} {α β w : ℝ} {N m : ℕ} (hm : 1 ≤ m)
    (h : (m : ℝ) * (Real.exp (β * w) - 1) < 1) (p : ℕ → ℝ) : rowWindow K α β w N m p = 0 := by
  refine Finset.sum_eq_zero fun h' hh => ?_
  rw [if_neg]
  intro hw
  have h1 : (1 : ℝ) ≤ h' := by exact_mod_cast (Finset.mem_Icc.mp hh).1
  have := ((log_window_iff hm (Nat.cast_nonneg h')).mp hw).2
  linarith

theorem abs_rowWindow_le {K : ℝ → ℝ} {α β A w : ℝ} (hw : 0 < w) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hA : ∀ ℓ ∈ Icc α β, |K ℓ| ≤ A) {p : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |p n| ≤ B) {N m : ℕ}
    (hm : 1 ≤ m) : |rowWindow K α β w N m p| ≤ B * A * (Real.exp (β * w) - 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set b : ℝ := m * (Real.exp (β * w) - 1)
  have hterm : ∀ h ∈ Finset.Icc 1 (N - m), |(if α * w < Real.log (1 + h / m) ∧
      Real.log (1 + h / m) ≤ β * w then p (m + h) * rowKernel K w m h else 0)| ≤
      if (h : ℝ) ≤ b then B * (A / m) else 0 := by
    intro h _
    split_ifs with hw' hb
    · have hmem := (log_window_iff hm (Nat.cast_nonneg h)).mp hw'
      have ha0 : 0 ≤ (m : ℝ) * (Real.exp (α * w) - 1) := mul_nonneg hm0.le (by
        have := Real.add_one_le_exp (α * w); nlinarith [mul_nonneg hα hw.le])
      have hK := hA _ (log_div_mem_Icc hw hm ⟨hmem.1.le, hmem.2⟩)
      have hs : (m : ℝ) ≤ Real.sqrt (m * (m + h)) := by
        rw [Real.le_sqrt hm0.le (by positivity)]; nlinarith [(Nat.cast_nonneg h : (0:ℝ) ≤ h)]
      rw [abs_mul, rowKernel, abs_div, abs_of_pos (lt_of_lt_of_le hm0 hs)]
      exact mul_le_mul (hB _) (div_le_div₀ ((abs_nonneg _).trans hK) hK hm0 hs) (by positivity) hB0
    · exact absurd ((log_window_iff hm (Nat.cast_nonneg h)).mp hw').2 hb
    · simp
    · simp
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA α ⟨le_rfl, hαβ⟩)
  have hb0 : 0 ≤ b := mul_nonneg hm0.le (by
    have := Real.add_one_le_exp (β * w); nlinarith [mul_nonneg (hα.trans hαβ) hw.le])
  have hcard : (((Finset.Icc 1 (N - m)).filter (fun h : ℕ => (h : ℝ) ≤ b)).card : ℝ) ≤ b := by
    have hsub : (Finset.Icc 1 (N - m)).filter (fun h : ℕ => (h : ℝ) ≤ b) ⊆ Finset.Icc 1 ⌊b⌋₊ := by
      intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
      exact ⟨hh.1.1, Nat.le_floor hh.2⟩
    calc (((Finset.Icc 1 (N - m)).filter (fun h : ℕ => (h : ℝ) ≤ b)).card : ℝ)
        ≤ ((Finset.Icc 1 ⌊b⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = ⌊b⌋₊ := by simp
      _ ≤ b := Nat.floor_le hb0
  calc |rowWindow K α β w N m p|
      ≤ ∑ h ∈ Finset.Icc 1 (N - m), (if (h : ℝ) ≤ b then B * (A / m) else 0) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (((Finset.Icc 1 (N - m)).filter (fun h : ℕ => (h : ℝ) ≤ b)).card : ℝ) * (B * (A / m)) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ b * (B * (A / m)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = B * A * (Real.exp (β * w) - 1) := by simp only [b]; field_simp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
