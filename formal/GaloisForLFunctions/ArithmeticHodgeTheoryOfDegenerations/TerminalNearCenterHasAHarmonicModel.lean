import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWeightsPreserveHarmonicGapRows

/-!
# A harmonic model for the terminal near center

The exact logarithmic cutoff is a linear inequality in each integer gap.
Periodic averaging retains the harmonic Ramanujan charge. Moving a terminal
weight between endpoints and removing the top boundary cost only the gap.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence

private theorem nearDifferencePair_eq_linear_gaps {t : ℝ} (ht : 0 < t)
    {N : ℕ} (hdN : ⌊(Real.exp t - 1) * N⌋₊ ≤ N) (u v : ℕ → ℝ) :
    nearDifferencePair t N u v =
      ∑ h ∈ Icc 1 ⌊(Real.exp t - 1) * N⌋₊, (1 / (h : ℝ)) *
        ∑ n ∈ Icc ⌈(h : ℝ) / (Real.exp t - 1)⌉₊ (N - h),
          (u n * v (n + h) + u (n + h) * v n) := by
  let d : ℝ := Real.exp t - 1
  have hd : 0 < d := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  let A : ℕ → ℕ → ℝ := fun n j =>
    if |Real.log j - Real.log n| ≤ t then u n * v j / ((j : ℝ) - n) else 0
  let B : ℕ → ℕ → ℝ := fun n j =>
    if |Real.log j - Real.log n| ≤ t then u j * v n / ((j : ℝ) - n) else 0
  have hpt : ∀ n j : ℕ,
      (if n ≠ j ∧ |Real.log j - Real.log n| ≤ t then
        u n * v j / |(n : ℝ) - j| else 0) =
      (if n < j then A n j else 0) + (if j < n then B j n else 0) := by
    intro n j
    dsimp only [A, B]
    rcases lt_trichotomy n j with h | h | h
    · have hR : (n : ℝ) < j := by exact_mod_cast h
      simp only [ne_eq, h.ne, not_false_eq_true, true_and, if_pos h,
        if_neg (by omega : ¬j < n), add_zero, abs_of_neg (sub_neg.mpr hR), neg_sub]
    · subst j
      simp
    · have hR : (j : ℝ) < n := by exact_mod_cast h
      simp only [ne_eq, h.ne', not_false_eq_true, true_and,
        if_neg (by omega : ¬n < j), if_pos h, zero_add,
        abs_of_pos (sub_pos.mpr hR), abs_sub_comm (Real.log n)]
  have hgap {n h : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) :
      (|Real.log ((n + h : ℕ) : ℝ) - Real.log n| ≤ t) ↔ ⌈(h : ℝ) / d⌉₊ ≤ n := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [log_add_sub_log hn,
      abs_of_nonneg (Real.log_nonneg (le_add_of_nonneg_right (by positivity))),
      Real.log_le_iff_le_exp (by positivity), Nat.ceil_le, div_le_iff₀ hd]
    constructor
    · intro hlog
      have hb : (h : ℝ) / n ≤ d := by dsimp only [d]; linarith only [hlog]
      exact (div_le_iff₀ hn0).mp hb |>.trans_eq (mul_comm _ _)
    · intro hlin
      have hb : (h : ℝ) / n ≤ d :=
        (div_le_iff₀ hn0).mpr (hlin.trans_eq (mul_comm _ _))
      dsimp only [d] at hb
      linarith only [hb]
  have hrow (h : ℕ) (hh : 1 ≤ h) :
      (∑ n ∈ Icc 1 (N - h),
        if |Real.log ((n + h : ℕ) : ℝ) - Real.log n| ≤ t then
          u n * v (n + h) + u (n + h) * v n else 0) =
      ∑ n ∈ Icc ⌈(h : ℝ) / d⌉₊ (N - h),
        (u n * v (n + h) + u (n + h) * v n) := by
    have ha : 1 ≤ ⌈(h : ℝ) / d⌉₊ := Nat.one_le_ceil_iff.mpr
      (div_pos (by exact_mod_cast hh) hd)
    have he : (Icc 1 (N - h)).filter (fun n => ⌈(h : ℝ) / d⌉₊ ≤ n) =
        Icc ⌈(h : ℝ) / d⌉₊ (N - h) := by
      ext n
      simp only [mem_filter, mem_Icc]
      omega
    rw [← he, sum_filter]
    exact sum_congr rfl fun n hn => by simp only [hgap (mem_Icc.mp hn).1 hh]
  have hall : nearDifferencePair t N u v =
      ∑ h ∈ Icc 1 N, (1 / (h : ℝ)) *
        ∑ n ∈ Icc ⌈(h : ℝ) / d⌉₊ (N - h),
          (u n * v (n + h) + u (n + h) * v n) := by
    unfold nearDifferencePair
    simp_rw [hpt]
    simp only [sum_add_distrib]
    rw [sum_comm (f := fun n j => if j < n then B j n else 0),
      sum_sum_ite_lt A N, sum_sum_ite_lt B N, ← sum_add_distrib]
    apply sum_congr rfl
    intro h hh
    rw [← sum_add_distrib, ← sum_add_distrib, ← hrow h (mem_Icc.mp hh).1, mul_sum]
    apply sum_congr rfl
    intro n hn
    dsimp only [A, B]
    simp only [Nat.cast_add, add_sub_cancel_left]
    split_ifs <;> ring
  rw [hall]
  symm
  apply sum_subset
  · intro h hh
    exact mem_Icc.mpr ⟨(mem_Icc.mp hh).1, (mem_Icc.mp hh).2.trans hdN⟩
  · intro h hh hnQ
    have hQh : ⌊d * N⌋₊ < h := by
      simp only [mem_Icc, not_and] at hnQ
      exact Nat.lt_of_not_ge (hnQ (mem_Icc.mp hh).1)
    have hdNh : d * N < h := (Nat.lt_floor_add_one (d * N)).trans_le
      (by exact_mod_cast hQh)
    have haN : N < ⌈(h : ℝ) / d⌉₊ := by
      apply Nat.lt_of_not_ge
      intro hle
      have hdiv : (h : ℝ) / d ≤ (N : ℝ) :=
        (Nat.le_ceil ((h : ℝ) / d)).trans (by exact_mod_cast hle)
      have hb := (div_le_iff₀ hd).mp hdiv
      nlinarith only [hdNh, hb]
    rw [Icc_eq_empty_of_lt (lt_of_le_of_lt (Nat.sub_le N h) haN), sum_empty, mul_zero]

private theorem abs_terminal_interval_top_sub_le
    {F : ℝ → ℝ} {BF : ℝ} (hF : ∀ x, |F x| ≤ BF)
    {a N h : ℕ} (hhN : h ≤ N) :
    |(∑ n ∈ Icc a (N - h), F ((n : ℝ) / N)) -
      ∑ n ∈ Icc a N, F ((n : ℝ) / N)| ≤ BF * h := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  let s := Icc a (N - h)
  let t := Icc a N
  have hst : s ⊆ t := fun n hn => mem_Icc.mpr
    ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans (Nat.sub_le N h)⟩
  have hsub : t \ s ⊆ Icc (N - h + 1) N := by
    intro n hn
    have hn' := mem_sdiff.mp hn
    simp only [s, t, mem_Icc] at hn'
    exact mem_Icc.mpr ⟨by omega, hn'.1.2⟩
  have hcard : (t \ s).card ≤ h := by
    have he : (Icc (N - h + 1) N).card = h := by rw [Nat.card_Icc]; omega
    exact (card_le_card hsub).trans_eq he
  have he : (∑ n ∈ t, F ((n : ℝ) / N)) =
      (∑ n ∈ s, F ((n : ℝ) / N)) + ∑ n ∈ t \ s, F ((n : ℝ) / N) := by
    have hdisj : Disjoint s (t \ s) := disjoint_left.mpr
      (fun n hn hn' => (mem_sdiff.mp hn').2 hn)
    have hunion : s ∪ (t \ s) = t := by
      ext n
      constructor
      · intro hn
        rcases mem_union.mp hn with hn | hn
        · exact hst hn
        · exact (mem_sdiff.mp hn).1
      · intro hn
        by_cases hs : n ∈ s
        · exact mem_union.mpr (Or.inl hs)
        · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hn, hs⟩))
    rw [← sum_union hdisj, hunion]
  change |(∑ n ∈ s, F ((n : ℝ) / N)) - ∑ n ∈ t, F ((n : ℝ) / N)| ≤ _
  rw [he, show ∀ a b : ℝ, a - (a + b) = -b from fun a b => by ring, abs_neg]
  calc
    _ ≤ ∑ _n ∈ t \ s, BF :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => hF _)
    _ = BF * (t \ s).card := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ BF * h := mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hBF

private theorem abs_terminal_oriented_gapRow_sub_le
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {m l a h N : ℕ} (hm : 0 < m) (hl : 0 < l)
    (hN : 1 ≤ N) (ha : 1 ≤ a) (hhN : h ≤ N) :
    |(∑ n ∈ Icc a (N - h),
        (F ((n : ℝ) / N) * ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
          F (((n + h : ℕ) : ℝ) / N) * ramanujanLagCoefficient l (n + h) *
            ramanujanLagCoefficient m n)) -
      (2 * (if m = l then ramanujanLagCoefficient m h else 0)) *
        ∑ n ∈ Icc a N, F ((n : ℝ) / N)| ≤
      2 * (l * m : ℕ) *
        (2 * (∑ d ∈ l.divisors, (d : ℝ)) * ∑ d ∈ m.divisors, (d : ℝ)) * (BF + LF) +
      (LF * (∑ d ∈ l.divisors, (d : ℝ)) * (∑ d ∈ m.divisors, (d : ℝ)) +
        2 * BF * ∑ d ∈ m.divisors, (d : ℝ)) * h := by
  let Bl : ℝ := ∑ d ∈ l.divisors, (d : ℝ)
  let Bm : ℝ := ∑ d ∈ m.divisors, (d : ℝ)
  let K : ℝ := 2 * (l * m : ℕ) * (2 * Bl * Bm) * (BF + LF)
  let C : ℝ := LF * Bl * Bm + 2 * BF * Bm
  let s := Icc a (N - h)
  let A : ℝ := 2 * (if m = l then ramanujanLagCoefficient m h else 0)
  let W : ℝ := ∑ n ∈ s, F ((n : ℝ) / N) *
    (ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
      ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n)
  let E : ℝ := ∑ n ∈ s,
    (F ((n : ℝ) / N) * ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
      F (((n + h : ℕ) : ℝ) / N) * ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hBl : 0 ≤ Bl := by dsimp only [Bl]; positivity
  have hBm : 0 ≤ Bm := by dsimp only [Bm]; positivity
  have hcard : s.card ≤ N := by dsimp only [s]; rw [Nat.card_Icc]; omega
  have hstep : ∀ n ∈ s,
      |(F (((n + h : ℕ) : ℝ) / N) - F ((n : ℝ) / N)) *
        ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n| ≤
          (LF * (h : ℝ) / N) * Bl * Bm := by
    intro n hn
    have hnN : n ≤ N := (mem_Icc.mp hn).2.trans (Nat.sub_le N h)
    have hnhN : n + h ≤ N := by have hb := (mem_Icc.mp hn).2; omega
    have hx (k : ℕ) (hk : k ≤ N) : (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hN0).mpr (by exact_mod_cast hk)⟩
    have hf := hFL _ (hx (n + h) hnhN) _ (hx n hnN)
    have he : (((n + h : ℕ) : ℝ) / N) - (n : ℝ) / N = (h : ℝ) / N := by
      push_cast
      ring
    rw [he, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h / N)] at hf
    have hf' : |F (((n + h : ℕ) : ℝ) / N) - F ((n : ℝ) / N)| ≤ LF * h / N :=
      hf.trans_eq (by ring)
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul hf' (abs_ramanujanLagCoefficient_le l (n + h)) (abs_nonneg _) (by positivity))
      (abs_ramanujanLagCoefficient_le m n) (abs_nonneg _) (by positivity)
  have hEW : |E - W| ≤ LF * Bl * Bm * h := by
    have he : E - W = ∑ n ∈ s,
        (F (((n + h : ℕ) : ℝ) / N) - F ((n : ℝ) / N)) *
          ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n := by
      dsimp only [E, W]
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun n _ => by ring
    rw [he]
    calc
      _ ≤ ∑ _n ∈ s, (LF * (h : ℝ) / N) * Bl * Bm :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hstep)
      _ = (s.card : ℝ) * ((LF * h / N) * Bl * Bm) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((LF * h / N) * Bl * Bm) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = LF * Bl * Bm * h := by field_simp
  have hW : |W - A * ∑ n ∈ s, F ((n : ℝ) / N)| ≤ K :=
    abs_sum_Icc_terminal_ramanujan_gapRow_sub_le hF hLF hFL hm hl hN (Nat.sub_le N h) h
  have hA : |A| ≤ 2 * Bm := by
    dsimp only [A]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply mul_le_mul_of_nonneg_left _ zero_le_two
    split_ifs
    · exact abs_ramanujanLagCoefficient_le m h
    · simp only [abs_zero]; exact hBm
  have htop : |A * ∑ n ∈ s, F ((n : ℝ) / N) -
      A * ∑ n ∈ Icc a N, F ((n : ℝ) / N)| ≤ 2 * BF * Bm * h := by
    rw [← mul_sub, abs_mul]
    exact (mul_le_mul hA (abs_terminal_interval_top_sub_le hF hhN)
      (abs_nonneg _) (by positivity)).trans_eq (by ring)
  change |E - A * ∑ n ∈ Icc a N, F ((n : ℝ) / N)| ≤ K + C * h
  have htri := (abs_sub_le E W (A * ∑ n ∈ Icc a N, F ((n : ℝ) / N))).trans
    (add_le_add hEW ((abs_sub_le W (A * ∑ n ∈ s, F ((n : ℝ) / N))
      (A * ∑ n ∈ Icc a N, F ((n : ℝ) / N))).trans (add_le_add hW htop)))
  exact htri.trans_eq (by dsimp only [C]; ring)

private theorem sum_terminal_harmonic_model {d : ℝ} (hd : 0 < d)
    (N m : ℕ) (F : ℝ → ℝ) :
    (∑ h ∈ Icc 1 ⌊d * N⌋₊, (1 / (h : ℝ)) * ramanujanLagCoefficient m h *
      ∑ n ∈ Icc ⌈(h : ℝ) / d⌉₊ N, F ((n : ℝ) / N)) =
      ∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * lagHarmonic m ⌊d * n⌋₊ := by
  let Q : ℕ := ⌊d * N⌋₊
  have hrow (h : ℕ) (hh : h ∈ Icc 1 Q) :
      (∑ n ∈ Icc ⌈(h : ℝ) / d⌉₊ N, F ((n : ℝ) / N)) =
        ∑ n ∈ Icc 1 N, if h ≤ ⌊d * n⌋₊ then F ((n : ℝ) / N) else 0 := by
    have ha : 1 ≤ ⌈(h : ℝ) / d⌉₊ := Nat.one_le_ceil_iff.mpr
      (div_pos (by exact_mod_cast (mem_Icc.mp hh).1) hd)
    have hiff (n : ℕ) : h ≤ ⌊d * n⌋₊ ↔ ⌈(h : ℝ) / d⌉₊ ≤ n := by
      rw [Nat.le_floor_iff (by positivity : 0 ≤ d * n), Nat.ceil_le, div_le_iff₀ hd]
      rw [mul_comm d]
    have hset : (Icc 1 N).filter (fun n : ℕ => h ≤ ⌊d * (n : ℝ)⌋₊) =
        Icc ⌈(h : ℝ) / d⌉₊ N := by
      ext n
      simp only [mem_filter, mem_Icc, hiff]
      omega
    rw [← hset, sum_filter]
  change (∑ h ∈ Icc 1 Q, _) = _
  calc
    _ = ∑ h ∈ Icc 1 Q, ∑ n ∈ Icc 1 N,
        if h ≤ ⌊d * n⌋₊ then F ((n : ℝ) / N) *
          (ramanujanLagCoefficient m h / h) else 0 := by
      apply sum_congr rfl
      intro h hh
      rw [hrow h hh, mul_sum]
      apply sum_congr rfl
      intro n hn
      split_ifs <;> ring
    _ = ∑ n ∈ Icc 1 N, ∑ h ∈ Icc 1 Q,
        if h ≤ ⌊d * n⌋₊ then F ((n : ℝ) / N) *
          (ramanujanLagCoefficient m h / h) else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      have hnQ : ⌊d * n⌋₊ ≤ Q := by
        apply (Nat.le_floor_iff (by positivity : 0 ≤ d * N)).mpr
        exact (Nat.floor_le (by positivity : 0 ≤ d * n)).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Icc.mp hn).2) hd.le)
      have hset : (Icc 1 Q).filter (fun h => h ≤ ⌊d * n⌋₊) = Icc 1 ⌊d * n⌋₊ := by
        ext h
        simp only [mem_filter, mem_Icc]
        omega
      rw [← sum_filter, hset, lagHarmonic, mul_sum]

/-- The terminal near difference kernel retains the local harmonic sum, with a harmonic
averaging error and a boundary error proportional to the logarithmic width. -/
theorem abs_terminal_nearDifferencePair_sub_harmonic_le
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {m l N : ℕ} (hm : 0 < m) (hl : 0 < l) (hN : 1 ≤ N)
    {t : ℝ} (ht : 0 < t) (hd1 : Real.exp t - 1 ≤ 1) :
    |nearDifferencePair t N (fun n => F ((n : ℝ) / N) * ramanujanLagCoefficient l n)
        (ramanujanLagCoefficient m) / (2 * N) -
      (if m = l then (∑ n ∈ Icc 1 N,
        F ((n : ℝ) / N) * lagHarmonic m ⌊(Real.exp t - 1) * n⌋₊) / N else 0)| ≤
      (2 * (l * m : ℕ) *
        (2 * (∑ d ∈ l.divisors, (d : ℝ)) * ∑ d ∈ m.divisors, (d : ℝ)) * (BF + LF)) *
          harmonic N / (2 * N) +
      (LF * (∑ d ∈ l.divisors, (d : ℝ)) * (∑ d ∈ m.divisors, (d : ℝ)) +
        2 * BF * ∑ d ∈ m.divisors, (d : ℝ)) * (Real.exp t - 1) / 2 := by
  let d : ℝ := Real.exp t - 1
  let Q : ℕ := ⌊d * N⌋₊
  let Bl : ℝ := ∑ j ∈ l.divisors, (j : ℝ)
  let Bm : ℝ := ∑ j ∈ m.divisors, (j : ℝ)
  let K : ℝ := 2 * (l * m : ℕ) * (2 * Bl * Bm) * (BF + LF)
  let C : ℝ := LF * Bl * Bm + 2 * BF * Bm
  let A : ℕ → ℝ := fun h => 2 * (if m = l then ramanujanLagCoefficient m h else 0)
  let E : ℕ → ℝ := fun h => ∑ n ∈ Icc ⌈(h : ℝ) / d⌉₊ (N - h),
    (F ((n : ℝ) / N) * ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
      F (((n + h : ℕ) : ℝ) / N) * ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n)
  let S : ℕ → ℝ := fun h => ∑ n ∈ Icc ⌈(h : ℝ) / d⌉₊ N, F ((n : ℝ) / N)
  have hd : 0 < d := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hK : 0 ≤ K := by dsimp only [K, Bl, Bm]; positivity
  have hC : 0 ≤ C := by dsimp only [C, Bl, Bm]; positivity
  have hQN : Q ≤ N := by
    have hq : (Q : ℝ) ≤ d * N := Nat.floor_le (by positivity)
    have hb : d * N ≤ (N : ℝ) := by nlinarith only [hd1, hN0]
    exact_mod_cast hq.trans hb
  have hr : ∀ h ∈ Icc 1 Q, |E h - A h * S h| ≤ K + C * h := by
    intro h hh
    have ha : 1 ≤ ⌈(h : ℝ) / d⌉₊ := Nat.one_le_ceil_iff.mpr
      (div_pos (by exact_mod_cast (mem_Icc.mp hh).1) hd)
    exact abs_terminal_oriented_gapRow_sub_le hF hLF hFL hm hl hN ha
      ((mem_Icc.mp hh).2.trans hQN)
  have hmain : (∑ h ∈ Icc 1 Q, (1 / (h : ℝ)) * (A h * S h)) / (2 * N) =
      (if m = l then (∑ n ∈ Icc 1 N,
        F ((n : ℝ) / N) * lagHarmonic m ⌊d * n⌋₊) / N else 0) := by
    by_cases hml : m = l
    · simp only [A, if_pos hml]
      have he : (∑ h ∈ Icc 1 Q, (1 / (h : ℝ)) * (2 * ramanujanLagCoefficient m h * S h)) =
          2 * ∑ h ∈ Icc 1 Q, (1 / (h : ℝ)) * ramanujanLagCoefficient m h * S h := by
        rw [mul_sum]
        exact sum_congr rfl fun h _ => by ring
      rw [he, show (∑ h ∈ Icc 1 Q, (1 / (h : ℝ)) * ramanujanLagCoefficient m h * S h) =
          ∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * lagHarmonic m ⌊d * n⌋₊ from
        sum_terminal_harmonic_model hd N m F]
      field_simp
      simp only [mul_comm d]
    · simp only [A, if_neg hml, mul_zero, zero_mul, sum_const_zero, zero_div]
  rw [nearDifferencePair_eq_linear_gaps ht hQN]
  change |(∑ h ∈ Icc 1 Q, (1 / (h : ℝ)) * E h) / (2 * N) - _| ≤
    K * harmonic N / (2 * N) + C * d / 2
  rw [← hmain, ← sub_div, ← sum_sub_distrib, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
  have hsum : |∑ h ∈ Icc 1 Q, ((1 / (h : ℝ)) * E h - (1 / (h : ℝ)) * (A h * S h))| ≤
      K * harmonic N + C * Q := by
    calc
      _ ≤ ∑ h ∈ Icc 1 Q, ((1 / (h : ℝ)) * K + C) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun h hh => ?_)
        rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h)]
        have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (mem_Icc.mp hh).1)
        exact (mul_le_mul_of_nonneg_left (hr h hh) (by positivity)).trans_eq (by field_simp)
      _ = (∑ h ∈ Icc 1 Q, 1 / (h : ℝ)) * K + C * Q := by
        rw [sum_add_distrib, ← sum_mul, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
          nsmul_eq_mul, mul_comm (Q : ℝ)]
      _ ≤ K * harmonic N + C * Q := by
        refine add_le_add ?_ (le_refl _)
        rw [mul_comm K, harmonic_eq_sum_Icc_real]
        apply mul_le_mul_of_nonneg_right _ hK
        simpa only [one_div] using sum_le_sum_of_subset_of_nonneg (f := fun h : ℕ => 1 / (h : ℝ))
          (show Icc 1 Q ⊆ Icc 1 N from fun h hh =>
            mem_Icc.mpr ⟨(mem_Icc.mp hh).1, (mem_Icc.mp hh).2.trans hQN⟩)
          (by intros; positivity)
  calc
    _ ≤ (K * harmonic N + C * Q) / (2 * N) :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ ≤ (K * harmonic N + C * (d * N)) / (2 * N) :=
      div_le_div_of_nonneg_right
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
          (Nat.floor_le (show 0 ≤ d * (N : ℝ) by positivity)) hC))
        (by positivity)
    _ = K * harmonic N / (2 * N) + C * d / 2 := by field_simp

/-- At vanishing logarithmic width, a terminally weighted near center has the local harmonic
model. No growth assumption on the overlap is needed for this approximation. -/
theorem tendsto_terminal_nearCenterPair_sub_harmonic
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      nearCenterPair (c N) N (fun n => F ((n : ℝ) / N) * ramanujanLagCoefficient l n)
        (ramanujanLagCoefficient m) / N -
      (if m = l then (∑ n ∈ Icc 1 N,
        F ((n : ℝ) / N) * lagHarmonic m ⌊(Real.exp (2 * c N / N) - 1) * n⌋₊) / N else 0))
      atTop (𝓝 0) := by
  let Bl : ℝ := ∑ j ∈ l.divisors, (j : ℝ)
  let Bm : ℝ := ∑ j ∈ m.divisors, (j : ℝ)
  let K : ℝ := 2 * (l * m : ℕ) * (2 * Bl * Bm) * (BF + LF)
  let C : ℝ := LF * Bl * Bm + 2 * BF * Bm
  let B : ℝ := BF * Bl + Bm
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have htlim : Tendsto (fun N : ℕ => 2 * c N / N) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hcN.const_mul 2
  have hdlim : Tendsto (fun N : ℕ => Real.exp (2 * c N / N) - 1) atTop (𝓝 0) := by
    simpa only [Real.exp_zero, sub_self, Function.comp_def] using
      ((Real.continuous_exp.tendsto 0).comp htlim).sub_const 1
  have hdiff : Tendsto (fun N : ℕ =>
      nearDifferencePair (2 * c N / N) N
        (fun n => F ((n : ℝ) / N) * ramanujanLagCoefficient l n) (ramanujanLagCoefficient m) /
          (2 * N) -
      (if m = l then (∑ n ∈ Icc 1 N,
        F ((n : ℝ) / N) * lagHarmonic m ⌊(Real.exp (2 * c N / N) - 1) * n⌋₊) / N else 0))
      atTop (𝓝 0) := by
    have hlim := (tendsto_harmonic_div_self.const_mul (K / 2)).add
      (hdlim.const_mul (C / 2))
    simp only [mul_zero, add_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1,
      hdlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hdN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs]
    exact (abs_terminal_nearDifferencePair_sub_harmonic_le hF hLF hFL hm hl hN
      (div_pos (mul_pos zero_lt_two (hc N)) hN0) hdN.le).trans_eq
        (by dsimp only [K, C, Bl, Bm]; ring)
  have hu (N n : ℕ) : |F ((n : ℝ) / N) * ramanujanLagCoefficient l n| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (hF _) (abs_ramanujanLagCoefficient_le l n) (abs_nonneg _) hBF).trans
      (le_add_of_nonneg_right (by dsimp only [Bm]; positivity))
  have hv (n : ℕ) : |ramanujanLagCoefficient m n| ≤ B :=
    (abs_ramanujanLagCoefficient_le m n).trans
      (le_add_of_nonneg_left (by dsimp only [Bl]; positivity))
  have hsum : Tendsto (fun N : ℕ => nearSumPair (c N) N
      (fun n => F ((n : ℝ) / N) * ramanujanLagCoefficient l n) (ramanujanLagCoefficient m) /
        (2 * N)) atTop (𝓝 0) := by
    have hlim := hcN.const_mul (2 * Real.exp 2 * B ^ 2)
    simp only [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1,
      hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hw
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
    exact (div_le_div_of_nonneg_right (abs_nearSumPair_le (hc N) hN hw.le (hu N) hv)
      (by positivity)).trans_eq (by ring)
  have hz := hdiff.add hsum
  simp only [add_zero] at hz
  exact hz.congr fun N => by rw [nearCenterPair_eq]; ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_nearDifferencePair_sub_harmonic_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_nearCenterPair_sub_harmonic
