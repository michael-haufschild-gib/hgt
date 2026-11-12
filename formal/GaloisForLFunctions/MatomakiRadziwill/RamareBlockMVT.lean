import GaloisForLFunctions.MatomakiRadziwill.RamareBlockError

/-!
# Mean square of the Ramaré decomposition error

For a scale `Pr` of primes `≥ P ≥ 2`, `X ≥ 1`, `H ≥ 2`, `W ≥ 1`
(`integral_normSq_rough_sub_pairPoly_le`):

`∫_{|w| ≤ W} |Σ_{n ∈ S} f(n)/n · n^{2πiw} − pairPoly(w)|² ≤ (5πW/2 + 20eX)(4/X²)(10X/H + 16X/P)`.

The block decomposition is reindexed by `n = pm` (`pairPoly_eq_sum`), so the difference is the
single polynomial `Σ_{n ≤ 8X} e(n) n^{2πiw}` (`rough_sub_pairPoly_eq`), and the mean value theorem
(`Sieve.integral_normSq_sum_unitLogPhase_le`) leaves `Σ |e(n)|²`.  By `errCoef_eq_zero` only
`X < n ≤ Xe^{1/H}`, `4X < n < 4Xe^{1/H}` and `p² ∣ n` contribute, each at most `(2/n)² ≤ 4/X²`;
their number is `≤ 2X/H + 8X/H + 8X Σ_p p^{-2} ≤ 10X/H + 16X/P`.
-/

open Finset MeasureTheory RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem exp_inv_le_two {H : ℝ} (hH : 2 ≤ H) : Real.exp (1 / H) ≤ 2 := by
  have h1 : 1 / H ≤ Real.log 2 := by
    have h2 := Real.log_two_gt_d9
    have h3 : 1 / H ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hH
    linarith
  calc Real.exp (1 / H) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h1
    _ = 2 := Real.exp_log (by norm_num)

theorem exp_inv_sub_one_le {H : ℝ} (hH : 1 ≤ H) : Real.exp (1 / H) - 1 ≤ 2 / H := by
  have hx0 : 0 < 1 / H := by positivity
  have hx1 : 1 / H ≤ 1 := by rw [div_le_one (by linarith)]; exact hH
  have h := Real.abs_exp_sub_one_sub_id_le (x := 1 / H) (by rw [abs_of_pos hx0]; exact hx1)
  have h2 := (abs_le.mp h).2
  have hsq : (1 / H) ^ 2 ≤ 1 / H := by
    rw [sq]; exact mul_le_of_le_one_left hx0.le hx1
  have e : 2 / H = 1 / H + 1 / H := by ring
  linarith

/-- `#(X, y] ≤ y − X` for natural `X ≤ y`. -/
theorem card_Ioc_floor_le {X : ℕ} {y : ℝ} (hy : (X : ℝ) ≤ y) :
    ((Ioc X ⌊y⌋₊).card : ℝ) ≤ y - X := by
  rw [Nat.card_Ioc]
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg X) hy
  rcases le_total X ⌊y⌋₊ with h | h
  · rw [Nat.cast_sub h]
    linarith [Nat.floor_le hy0]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    linarith

/-- `Σ_{P ≤ k < P+L} 1/k² ≤ 1/(P−1) − 1/(P+L−1)`. -/
theorem sum_Ico_inv_sq_le {P : ℕ} (hP : 2 ≤ P) (L : ℕ) :
    ∑ k ∈ Ico P (P + L), (1 : ℝ) / (k : ℝ) ^ 2
      ≤ 1 / ((P : ℝ) - 1) - 1 / ((P : ℝ) + L - 1) := by
  have hP' : (2 : ℝ) ≤ P := by exact_mod_cast hP
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show P + (L + 1) = (P + L) + 1 by ring, sum_Ico_succ_top (by omega), ← add_sub_cancel_left
      (1 / ((P : ℝ) - 1)) (1 / ((P : ℝ) + ↑(L + 1) - 1))]
    have hk : (1 : ℝ) / ((P + L : ℕ) : ℝ) ^ 2
        ≤ 1 / ((P : ℝ) + L - 1) - 1 / ((P : ℝ) + ↑(L + 1) - 1) := by
      push_cast
      have ha : (0 : ℝ) < (P : ℝ) + L - 1 := by linarith
      have hb : (P : ℝ) + (L + 1) - 1 = (P : ℝ) + L := by ring
      rw [hb, div_sub_div _ _ ha.ne' (by linarith), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- `Σ_{p ∈ Pr} 1/p² ≤ 2/P` when every `p ∈ Pr` is `≥ P ≥ 2`. -/
theorem sum_inv_sq_le {Pr : Finset ℕ} {P : ℕ} (hP : 2 ≤ P) (hmin : ∀ p ∈ Pr, P ≤ p) :
    ∑ p ∈ Pr, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 2 / P := by
  have hP' : (2 : ℝ) ≤ P := by exact_mod_cast hP
  set M : ℕ := Pr.sup id with hM
  have hsub : Pr ⊆ Ico P (P + (M + 1)) := by
    intro p hp
    rw [mem_Ico]
    refine ⟨hmin p hp, ?_⟩
    have : p ≤ M := Finset.le_sup (f := id) hp
    omega
  calc ∑ p ∈ Pr, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ k ∈ Ico P (P + (M + 1)), (1 : ℝ) / (k : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 1 / ((P : ℝ) - 1) - 1 / ((P : ℝ) + ↑(M + 1) - 1) := sum_Ico_inv_sq_le hP _
    _ ≤ 1 / ((P : ℝ) - 1) := by
        have : 0 ≤ 1 / ((P : ℝ) + ↑(M + 1) - 1) := by
          have : (0 : ℝ) < (P : ℝ) + ↑(M + 1) - 1 := by push_cast; linarith
          positivity
        linarith
    _ ≤ 2 / P := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith

/-- Exchanging a sum over `n` with a filtered sum over `p`. -/
theorem sum_sum_filter_comm {A B : Finset ℕ} (R : ℕ → ℕ → Prop) [∀ n p, Decidable (R n p)]
    (F : ℕ → ℕ → ℂ) :
    ∑ n ∈ A, ∑ p ∈ B.filter (R n), F n p = ∑ p ∈ B, ∑ n ∈ A.filter (fun n => R n p), F n p := by
  simp_rw [sum_filter]
  exact sum_comm

/-- **The block decomposition reindexed by `n = pm`.** -/
theorem pairPoly_eq_sum (f : ℕ → ℂ) {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime)
    (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) {H : ℝ} (hH : 2 ≤ H) (w : ℝ) :
    pairPoly f Pr rest X H w
      = ∑ n ∈ Icc 1 (8 * X), (∑ p ∈ seenBy Pr rest X H n, coefA f p * coefC f Pr (n / p))
          * unitLogPhase w n := by
  classical
  have hH0 : (0 : ℝ) < H := by linarith
  simp_rw [sum_mul]
  rw [show (∑ n ∈ Icc 1 (8 * X), ∑ p ∈ seenBy Pr rest X H n,
        coefA f p * coefC f Pr (n / p) * unitLogPhase w n)
      = ∑ p ∈ Pr, ∑ n ∈ (Icc 1 (8 * X)).filter
          (fun n => p ∣ n ∧ n / p ∈ cof rest X H (blk H p)),
          coefA f p * coefC f Pr (n / p) * unitLogPhase w n from
    sum_sum_filter_comm (R := fun n p => p ∣ n ∧ n / p ∈ cof rest X H (blk H p)) _]
  rw [pairPoly]
  refine sum_congr rfl fun p hp => ?_
  have hp0 : 0 < p := (hPr p hp).pos
  symm
  refine sum_nbij' (fun n => n / p) (fun m => p * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    exact (mem_filter.mp hn).2.2
  · intro m hm
    have hm' := mem_cof.mp hm
    have hm0 : 0 < m := by
      have : (0 : ℝ) < m := lt_of_le_of_lt (cofLo_nonneg X H _) hm'.1
      exact_mod_cast this
    have hlt := mul_lt_of_mem_cof hH0 hp0 hm
    have h8 : ((p * m : ℕ) : ℝ) ≤ ((8 * X : ℕ) : ℝ) := by
      push_cast at hlt ⊢
      have := exp_inv_le_two hH
      have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
      nlinarith
    rw [mem_filter, mem_Icc]
    refine ⟨⟨Nat.mul_pos hp0 hm0, by exact_mod_cast h8⟩, dvd_mul_right p m, ?_⟩
    rw [Nat.mul_div_cancel_left m hp0]
    exact hm
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2.1
  · intro m _
    exact Nat.mul_div_cancel_left m hp0
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2.1]

theorem roughSet_subset_Icc (rest : ℕ → Prop) [DecidablePred rest] (Pr : Finset ℕ) (X : ℕ) :
    roughSet rest Pr X ⊆ Icc 1 (8 * X) := by
  intro n hn
  rw [roughSet, mem_filter, mem_Ioc] at hn
  rw [mem_Icc]
  omega

/-- **The decomposition error as one polynomial.** -/
theorem rough_sub_pairPoly_eq (f : ℕ → ℂ) {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime)
    (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) {H : ℝ} (hH : 2 ≤ H) (w : ℝ) :
    logPoly (coefA f) (roughSet rest Pr X) w - pairPoly f Pr rest X H w
      = ∑ n ∈ Icc 1 (8 * X), errCoef f Pr rest X H n * unitLogPhase w n := by
  classical
  rw [pairPoly_eq_sum f hPr rest X hH w, logPoly_eq_sum_mul_unitLogPhase]
  have hS : ∑ n ∈ roughSet rest Pr X, coefA f n * unitLogPhase w n
      = ∑ n ∈ Icc 1 (8 * X),
          (if n ∈ roughSet rest Pr X then coefA f n else 0) * unitLogPhase w n := by
    simp_rw [ite_mul, zero_mul]
    rw [← sum_filter]
    congr 1
    ext n
    rw [mem_filter]
    exact ⟨fun h => ⟨roughSet_subset_Icc rest Pr X h, h⟩, fun h => h.2⟩
  rw [hS, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [errCoef, sub_mul]

/-- **The decomposition error coefficients carry mass `≤ (4/X²)(10X/H + 16X/P)`.** -/
theorem sum_normSq_errCoef_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b, f (a * b) = f a * f b) {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime) {P : ℕ}
    (hP : 2 ≤ P) (hmin : ∀ p ∈ Pr, P ≤ p) {rest : ℕ → Prop} [DecidablePred rest]
    (hrest : ∀ p ∈ Pr, ∀ m, rest (p * m) ↔ rest m) {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 2 ≤ H) :
    ∑ n ∈ Icc 1 (8 * X), ‖errCoef f Pr rest X H n‖ ^ 2
      ≤ 4 / (X : ℝ) ^ 2 * (10 * X / H + 16 * X / P) := by
  classical
  have hH0 : (0 : ℝ) < H := by linarith
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  set E : ℝ := Real.exp (1 / H) with hEdef
  set bad : ℕ → Prop := fun n => (X : ℝ) < n ∧ ((n : ℝ) ≤ X * E ∨
    ((4 * X : ℝ) < n ∧ (n : ℝ) < 4 * X * E) ∨ ∃ p ∈ Pr, p ^ 2 ∣ n) with hbad
  -- off `bad` the coefficient vanishes
  have hzero : ∀ n ∈ Icc 1 (8 * X), ¬ bad n → errCoef f Pr rest X H n = 0 := by
    intro n hn hb
    have hn0 : 0 < n := (mem_Icc.mp hn).1
    refine errCoef_eq_zero hmul hPr hrest hH0 hn0 ?_
    by_cases hXn : (X : ℝ) < n
    · have hb' : ¬ ((n : ℝ) ≤ X * E ∨ ((4 * X : ℝ) < n ∧ (n : ℝ) < 4 * X * E) ∨
          ∃ p ∈ Pr, p ^ 2 ∣ n) := fun h => hb ⟨hXn, h⟩
      push Not at hb'
      obtain ⟨h1, h2, h3⟩ := hb'
      by_cases h4 : (n : ℝ) ≤ 4 * X
      · exact Or.inr (Or.inl ⟨h1, h4, h3⟩)
      · exact Or.inr (Or.inr (h2 (lt_of_not_ge h4)))
    · exact Or.inl (le_of_not_gt hXn)
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 (8 * X)) bad
    (fun n => ‖errCoef f Pr rest X H n‖ ^ 2)
  have hnot : ∑ n ∈ (Icc 1 (8 * X)).filter (fun n => ¬ bad n),
      ‖errCoef f Pr rest X H n‖ ^ 2 = 0 := by
    refine sum_eq_zero fun n hn => ?_
    rw [mem_filter] at hn
    rw [hzero n hn.1 hn.2, norm_zero]
    ring
  -- each bad term is at most `4/X²`
  have hterm : ∀ n ∈ (Icc 1 (8 * X)).filter bad, ‖errCoef f Pr rest X H n‖ ^ 2 ≤ 4 / (X : ℝ) ^ 2 := by
    intro n hn
    rw [mem_filter] at hn
    have hn0 : 0 < n := (mem_Icc.mp hn.1).1
    have hXn : (X : ℝ) < n := hn.2.1
    have h := norm_errCoef_le hf hPr rest X H hn0
    have h2 : 2 / (n : ℝ) ≤ 2 / X := div_le_div_of_nonneg_left (by norm_num) hX0 hXn.le
    have h3 : ‖errCoef f Pr rest X H n‖ ≤ 2 / X := le_trans h h2
    calc ‖errCoef f Pr rest X H n‖ ^ 2 ≤ (2 / (X : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = 4 / (X : ℝ) ^ 2 := by ring
  -- the number of bad integers
  have hsub : (Icc 1 (8 * X)).filter bad ⊆ Ioc X ⌊(X : ℝ) * E⌋₊ ∪ Ioc (4 * X) ⌊4 * (X : ℝ) * E⌋₊
      ∪ Pr.biUnion (fun p => (Icc 1 (8 * X)).filter (fun n => p ^ 2 ∣ n)) := by
    intro n hn
    rw [mem_filter] at hn
    obtain ⟨hnI, hXn, hcase⟩ := hn
    have hXn' : X < n := by exact_mod_cast hXn
    rw [mem_union, mem_union]
    rcases hcase with h1 | ⟨h2, h3⟩ | ⟨p, hp, hpn⟩
    · left; left
      rw [mem_Ioc]
      exact ⟨hXn', Nat.le_floor h1⟩
    · left; right
      rw [mem_Ioc]
      exact ⟨by exact_mod_cast h2, Nat.le_floor h3.le⟩
    · right
      rw [mem_biUnion]
      exact ⟨p, hp, mem_filter.mpr ⟨hnI, hpn⟩⟩
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hEsub : E - 1 ≤ 2 / H := exp_inv_sub_one_le (by linarith)
  have hc1 : ((Ioc X ⌊(X : ℝ) * E⌋₊).card : ℝ) ≤ 2 * X / H := by
    have h := card_Ioc_floor_le (X := X) (y := (X : ℝ) * E) (by nlinarith)
    have : (X : ℝ) * E - X = X * (E - 1) := by ring
    rw [this] at h
    calc _ ≤ (X : ℝ) * (E - 1) := h
      _ ≤ X * (2 / H) := mul_le_mul_of_nonneg_left hEsub hX0.le
      _ = 2 * X / H := by ring
  have hc2 : ((Ioc (4 * X) ⌊4 * (X : ℝ) * E⌋₊).card : ℝ) ≤ 8 * X / H := by
    have h := card_Ioc_floor_le (X := 4 * X) (y := 4 * (X : ℝ) * E) (by push_cast; nlinarith)
    push_cast at h
    have : 4 * (X : ℝ) * E - 4 * X = 4 * X * (E - 1) := by ring
    rw [this] at h
    calc _ ≤ 4 * (X : ℝ) * (E - 1) := h
      _ ≤ 4 * X * (2 / H) := mul_le_mul_of_nonneg_left hEsub (by positivity)
      _ = 8 * X / H := by ring
  have hc3 : ((Pr.biUnion (fun p => (Icc 1 (8 * X)).filter (fun n => p ^ 2 ∣ n))).card : ℝ)
      ≤ 16 * X / P := by
    have hb := card_biUnion_le (s := Pr) (t := fun p => (Icc 1 (8 * X)).filter (fun n => p ^ 2 ∣ n))
    have hb' : ((Pr.biUnion (fun p => (Icc 1 (8 * X)).filter (fun n => p ^ 2 ∣ n))).card : ℝ)
        ≤ ∑ p ∈ Pr, (((Icc 1 (8 * X)).filter (fun n => p ^ 2 ∣ n)).card : ℝ) := by
      exact_mod_cast hb
    have hone : ∀ p ∈ Pr, (((Icc 1 (8 * X)).filter (fun n => p ^ 2 ∣ n)).card : ℝ)
        ≤ ((8 * X : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ) := by
      intro p hp
      have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (hPr p hp).pos
      exact card_filter_dvd_le (fun m hm => mem_Icc.mp hm) hp1
    calc _ ≤ ∑ p ∈ Pr, (((Icc 1 (8 * X)).filter (fun n => p ^ 2 ∣ n)).card : ℝ) := hb'
      _ ≤ ∑ p ∈ Pr, ((8 * X : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ) := sum_le_sum hone
      _ = 8 * X * ∑ p ∈ Pr, (1 : ℝ) / (p : ℝ) ^ 2 := by
          rw [mul_sum]
          refine sum_congr rfl fun p _ => ?_
          push_cast
          ring
      _ ≤ 8 * X * (2 / P) := mul_le_mul_of_nonneg_left (sum_inv_sq_le hP hmin) (by positivity)
      _ = 16 * X / P := by ring
  have hcard : (((Icc 1 (8 * X)).filter bad).card : ℝ) ≤ 10 * X / H + 16 * X / P := by
    have h1 := card_le_card hsub
    have h2 := card_union_le (Ioc X ⌊(X : ℝ) * E⌋₊ ∪ Ioc (4 * X) ⌊4 * (X : ℝ) * E⌋₊)
      (Pr.biUnion (fun p => (Icc 1 (8 * X)).filter (fun n => p ^ 2 ∣ n)))
    have h3 := card_union_le (Ioc X ⌊(X : ℝ) * E⌋₊) (Ioc (4 * X) ⌊4 * (X : ℝ) * E⌋₊)
    have h123 : (((Icc 1 (8 * X)).filter bad).card : ℝ)
        ≤ ((Ioc X ⌊(X : ℝ) * E⌋₊).card : ℝ) + ((Ioc (4 * X) ⌊4 * (X : ℝ) * E⌋₊).card : ℝ)
          + ((Pr.biUnion (fun p => (Icc 1 (8 * X)).filter (fun n => p ^ 2 ∣ n))).card : ℝ) := by
      exact_mod_cast h1.trans (h2.trans (Nat.add_le_add_right h3 _))
    have e : 10 * (X : ℝ) / H = 2 * X / H + 8 * X / H := by ring
    linarith
  calc ∑ n ∈ Icc 1 (8 * X), ‖errCoef f Pr rest X H n‖ ^ 2
      = ∑ n ∈ (Icc 1 (8 * X)).filter bad, ‖errCoef f Pr rest X H n‖ ^ 2 := by
        rw [← hsplit, hnot, add_zero]
    _ ≤ ∑ _n ∈ (Icc 1 (8 * X)).filter bad, 4 / (X : ℝ) ^ 2 := sum_le_sum hterm
    _ = (((Icc 1 (8 * X)).filter bad).card : ℝ) * (4 / (X : ℝ) ^ 2) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (10 * X / H + 16 * X / P) * (4 / (X : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 / (X : ℝ) ^ 2 * (10 * X / H + 16 * X / P) := by ring

/-- **Ramaré's block decomposition, with its error.** -/
theorem integral_normSq_rough_sub_pairPoly_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b, f (a * b) = f a * f b) {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime) {P : ℕ}
    (hP : 2 ≤ P) (hmin : ∀ p ∈ Pr, P ≤ p) {rest : ℕ → Prop} [DecidablePred rest]
    (hrest : ∀ p ∈ Pr, ∀ m, rest (p * m) ↔ rest m) {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 2 ≤ H)
    {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (coefA f) (roughSet rest Pr X) w - pairPoly f Pr rest X H w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((8 * X : ℕ) : ℝ))
          * (4 / (X : ℝ) ^ 2 * (10 * X / H + 16 * X / P)) := by
  classical
  simp_rw [rough_sub_pairPoly_eq f hPr rest X hH]
  have hbase := integral_normSq_sum_unitLogPhase_le (Icc 1 (8 * X)) id
    (errCoef f Pr rest X H) (fun i hi => (mem_Icc.mp hi).1) (fun i hi => (mem_Icc.mp hi).2) hW
  have hfib : ∑ n ∈ (Icc 1 (8 * X)).image id,
        ‖∑ i ∈ Icc 1 (8 * X) with id i = n, errCoef f Pr rest X H i‖ ^ (2 : ℕ)
      = ∑ n ∈ Icc 1 (8 * X), ‖errCoef f Pr rest X H n‖ ^ 2 := by
    rw [image_id]
    refine sum_congr rfl fun n hn => ?_
    have : (Icc 1 (8 * X)).filter (fun i => id i = n) = {n} := by
      ext i
      simp only [mem_filter, mem_singleton, id]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨hn, rfl⟩
    rw [this, sum_singleton]
  rw [hfib] at hbase
  have hcoef : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((8 * X : ℕ) : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le
    have : (0 : ℝ) ≤ W := by linarith
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (sum_normSq_errCoef_le hf hmul hPr hP hmin hrest hX hH) hcoef)

end

end GaloisForLFunctions.MatomakiRadziwill
