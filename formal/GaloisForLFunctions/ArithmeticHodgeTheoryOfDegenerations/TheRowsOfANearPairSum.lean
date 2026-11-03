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

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
