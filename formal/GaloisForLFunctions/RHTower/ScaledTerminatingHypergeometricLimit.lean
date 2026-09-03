import Mathlib

/-!
# Scaled limit of terminating hypergeometric sums (the Mehler–Heine mechanism)

For the terminating hypergeometric sum

`hypSum n d c σ = Σ_{l ≤ n} (−1)^l n^{(l)} (n + d)_l / ((c)_l l!) σ^{2l}`   (`n^{(l)}` falling, `(·)_l` rising)

along sequences `n_j → ∞`, `σ_j ≥ 0` with `n_j σ_j → w`, Tannery's theorem gives

`hypSum n_j d c σ_j → Σ_l (−1)^l w^{2l} / ((c)_l l!)`,

which is `cos(2w)` for `c = 1/2` and `sin(2w)/(2w)` for `c = 3/2`.  This is the Mehler–Heine limit
of the Jacobi polynomials `P_n^{(c−1, d−c)}(1 − 2σ²)` up to their leading constants.
-/

open Filter Finset
open scoped Topology BigOperators

namespace RHTower

namespace ScaledHypergeometric

/-- The falling factorial `n(n−1)⋯(n−l+1)` as a real number. -/
noncomputable def fallingNat (n l : ℕ) : ℝ := ∏ i ∈ range l, ((n : ℝ) - i)

/-- The rising factorial `a(a+1)⋯(a+l−1)`. -/
noncomputable def rising (a : ℝ) (l : ℕ) : ℝ := ∏ i ∈ range l, (a + i)

/-- The `l`-th term of the terminating `₂F₁(−n, n+d; c; σ²)`. -/
noncomputable def hypTerm (n : ℕ) (d c σ : ℝ) (l : ℕ) : ℝ :=
  (-1) ^ l * fallingNat n l * rising ((n : ℝ) + d) l / (rising c l * l.factorial) * σ ^ (2 * l)

/-- The terminating `₂F₁(−n, n+d; c; σ²)`. -/
noncomputable def hypSum (n : ℕ) (d c σ : ℝ) : ℝ := ∑ l ∈ range (n + 1), hypTerm n d c σ l

/-- The limit series `Σ_l (−1)^l w^{2l} / ((c)_l l!)`. -/
noncomputable def limitTerm (c w : ℝ) (l : ℕ) : ℝ :=
  (-1) ^ l * w ^ (2 * l) / (rising c l * l.factorial)

/-! ## Elementary facts about the factorials -/

@[simp] theorem rising_zero (a : ℝ) : rising a 0 = 1 := by simp [rising]

theorem rising_succ (a : ℝ) (l : ℕ) : rising a (l + 1) = rising a l * (a + l) := by
  simp [rising, prod_range_succ]

theorem rising_succ' (a : ℝ) (l : ℕ) : rising a (l + 1) = a * rising (a + 1) l := by
  unfold rising
  rw [prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro i _
  ring

theorem rising_pos {a : ℝ} (ha : 0 < a) (l : ℕ) : 0 < rising a l := by
  unfold rising
  exact prod_pos fun i _ => by positivity

theorem rising_nonneg {a : ℝ} (ha : 0 ≤ a) (l : ℕ) : 0 ≤ rising a l := by
  unfold rising
  exact prod_nonneg fun i _ => by positivity

theorem fallingNat_eq_zero_of_lt {n l : ℕ} (h : n < l) : fallingNat n l = 0 := by
  unfold fallingNat
  exact prod_eq_zero (mem_range.mpr h) (by simp)

theorem fallingNat_nonneg {n l : ℕ} (h : l ≤ n) : 0 ≤ fallingNat n l := by
  unfold fallingNat
  apply prod_nonneg
  intro i hi
  rw [mem_range] at hi
  have : (i : ℝ) ≤ n := by exact_mod_cast (by omega : i ≤ n)
  linarith

theorem fallingNat_le_pow {n l : ℕ} (h : l ≤ n) : fallingNat n l ≤ (n : ℝ) ^ l := by
  unfold fallingNat
  rw [show (n : ℝ) ^ l = ∏ _i ∈ range l, (n : ℝ) by simp]
  apply Finset.prod_le_prod
  · intro i hi
    rw [mem_range] at hi
    have : (i : ℝ) ≤ n := by exact_mod_cast (by omega : i ≤ n)
    linarith
  · intro i _
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]

theorem rising_le_pow {a : ℝ} (ha : 0 ≤ a) (l : ℕ) : rising a l ≤ (a + l) ^ l := by
  unfold rising
  rw [show (a + l) ^ l = ∏ _i ∈ range l, (a + l) by simp]
  apply Finset.prod_le_prod
  · intro i _; positivity
  · intro i hi
    rw [mem_range] at hi
    have : (i : ℝ) ≤ l := by exact_mod_cast hi.le
    linarith

theorem min_pow_le_rising {c : ℝ} (hc : 0 < c) (l : ℕ) : (min c 1) ^ l ≤ rising c l := by
  unfold rising
  rw [show (min c 1) ^ l = ∏ _i ∈ range l, min c 1 by simp]
  apply Finset.prod_le_prod
  · intro i _; positivity
  · intro i _
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    rcases le_or_gt c 1 with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h.le]; linarith

theorem hypTerm_eq_zero_of_lt {n l : ℕ} (h : n < l) (d c σ : ℝ) : hypTerm n d c σ l = 0 := by
  unfold hypTerm
  rw [fallingNat_eq_zero_of_lt h]
  ring

theorem hypSum_eq_tsum (n : ℕ) (d c σ : ℝ) : hypSum n d c σ = ∑' l, hypTerm n d c σ l := by
  unfold hypSum
  symm
  apply tsum_eq_sum
  intro l hl
  rw [mem_range] at hl
  exact hypTerm_eq_zero_of_lt (by omega) d c σ

/-! ## The domination bound -/

theorem abs_hypTerm_le {n : ℕ} {d c σ B : ℝ} (hd : 0 ≤ d) (hc : 0 < c) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hB : (n : ℝ) * σ ≤ B) (hB0 : 0 ≤ B) (l : ℕ) :
    |hypTerm n d c σ l| ≤ (B * (2 * B + d) / min c 1) ^ l / l.factorial := by
  rcases lt_or_ge n l with h | h
  · rw [hypTerm_eq_zero_of_lt h, abs_zero]; positivity
  unfold hypTerm
  have hfall := fallingNat_nonneg h
  have hrise := rising_nonneg (by positivity : (0 : ℝ) ≤ n + d) l
  have hrc := rising_pos hc l
  have hm : 0 < min c 1 := lt_min hc one_pos
  rw [abs_mul, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hfall, abs_of_nonneg hrise,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ rising c l * l.factorial),
    abs_pow, abs_of_nonneg hσ0]
  -- fallingNat n l * rising (n+d) l * σ^(2l) ≤ (B (2B + d))^l
  have hnum : fallingNat n l * rising ((n : ℝ) + d) l * σ ^ (2 * l) ≤ (B * (2 * B + d)) ^ l := by
    have h1 : fallingNat n l ≤ (n : ℝ) ^ l := fallingNat_le_pow h
    have h2 : rising ((n : ℝ) + d) l ≤ ((n : ℝ) + d + l) ^ l := rising_le_pow (by positivity) l
    have hl : (l : ℝ) ≤ n := by exact_mod_cast h
    calc fallingNat n l * rising ((n : ℝ) + d) l * σ ^ (2 * l)
        ≤ (n : ℝ) ^ l * ((n : ℝ) + d + l) ^ l * σ ^ (2 * l) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 hrise (by positivity)) (by positivity)
      _ = ((n : ℝ) * σ) ^ l * (((n : ℝ) + d + l) * σ) ^ l := by
          rw [mul_pow, mul_pow, pow_mul, show σ ^ 2 = σ * σ by ring, mul_pow]; ring
      _ ≤ B ^ l * (2 * B + d) ^ l := by
          have h3 : ((n : ℝ) + d + l) * σ ≤ 2 * B + d := by
            calc ((n : ℝ) + d + l) * σ = (n : ℝ) * σ + d * σ + (l : ℝ) * σ := by ring
              _ ≤ B + d * 1 + B := by
                  have hlσ : (l : ℝ) * σ ≤ B :=
                    (mul_le_mul_of_nonneg_right hl hσ0).trans hB
                  exact add_le_add (add_le_add hB (mul_le_mul_of_nonneg_left hσ1 hd)) hlσ
              _ = 2 * B + d := by ring
          exact mul_le_mul (pow_le_pow_left₀ (by positivity) hB l)
            (pow_le_pow_left₀ (by positivity) h3 l) (by positivity) (by positivity)
      _ = (B * (2 * B + d)) ^ l := by rw [mul_pow]
  have hden : (min c 1) ^ l * l.factorial ≤ rising c l * l.factorial :=
    mul_le_mul_of_nonneg_right (min_pow_le_rising hc l) (by positivity)
  calc fallingNat n l * rising ((n : ℝ) + d) l / (rising c l * l.factorial) * σ ^ (2 * l)
      = (fallingNat n l * rising ((n : ℝ) + d) l * σ ^ (2 * l)) / (rising c l * l.factorial) := by
        ring
    _ ≤ (B * (2 * B + d)) ^ l / ((min c 1) ^ l * l.factorial) := by
        apply div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (B * (2 * B + d) / min c 1) ^ l / l.factorial := by
        rw [div_pow, div_div]

/-! ## The termwise limit -/

theorem tendsto_hypTerm {d c : ℝ} {n : ℕ → ℕ} {σ : ℕ → ℝ} {w : ℝ}
    (hn : Tendsto n atTop atTop)
    (hnσ : Tendsto (fun j => (n j : ℝ) * σ j) atTop (𝓝 w)) (l : ℕ) :
    Tendsto (fun j => hypTerm (n j) d c (σ j) l) atTop (𝓝 (limitTerm c w l)) := by
  have hnR : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hσ : Tendsto σ atTop (𝓝 0) := by
    have h := hnσ.div_atTop hnR
    refine h.congr' ?_
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hj
    have : (n j : ℝ) ≠ 0 := by exact_mod_cast (by omega : n j ≠ 0)
    field_simp
  have hfact : ∀ i : ℕ, Tendsto (fun j => ((n j : ℝ) - i) * σ j) atTop (𝓝 w) := by
    intro i
    have h := hnσ.sub (hσ.const_mul (i : ℝ))
    rw [mul_zero, sub_zero] at h
    refine h.congr' (Eventually.of_forall fun j => ?_)
    ring
  have hfact' : ∀ i : ℕ, Tendsto (fun j => ((n j : ℝ) + d + i) * σ j) atTop (𝓝 w) := by
    intro i
    have h := hnσ.add (hσ.const_mul (d + i))
    rw [mul_zero, add_zero] at h
    refine h.congr' (Eventually.of_forall fun j => ?_)
    ring
  have hprod1 : Tendsto (fun j => ∏ i ∈ range l, (((n j : ℝ) - i) * σ j)) atTop (𝓝 (w ^ l)) := by
    have := tendsto_finsetProd (range l) (fun i _ => hfact i)
    simpa [prod_const] using this
  have hprod2 : Tendsto (fun j => ∏ i ∈ range l, (((n j : ℝ) + d + i) * σ j)) atTop (𝓝 (w ^ l)) := by
    have := tendsto_finsetProd (range l) (fun i _ => hfact' i)
    simpa [prod_const] using this
  have hcomb := ((hprod1.mul hprod2).const_mul ((-1) ^ l)).div_const (rising c l * l.factorial)
  have hlim : limitTerm c w l = (-1) ^ l * (w ^ l * w ^ l) / (rising c l * l.factorial) := by
    unfold limitTerm
    rw [← pow_add, two_mul]
  rw [hlim]
  refine hcomb.congr' ?_
  filter_upwards with j
  unfold hypTerm fallingNat
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_range]
  unfold rising
  rw [show σ j ^ (2 * l) = σ j ^ l * σ j ^ l by rw [two_mul, pow_add]]
  ring

/-! ## The scaled limit -/

theorem summable_bound (c K : ℝ) :
    Summable fun l : ℕ => (K / min c 1) ^ l / l.factorial :=
  Real.summable_pow_div_factorial _

/-- **Mehler–Heine mechanism for terminating hypergeometric sums.**  If `n_j → ∞`, `σ_j ≥ 0` and
`n_j σ_j → w`, then `₂F₁(−n_j, n_j + d; c; σ_j²) → Σ_l (−1)^l w^{2l} / ((c)_l l!)`. -/
theorem tendsto_hypSum {d c : ℝ} (hd : 0 ≤ d) (hc : 0 < c) {n : ℕ → ℕ} {σ : ℕ → ℝ} {w : ℝ}
    (hn : Tendsto n atTop atTop) (hσ0 : ∀ j, 0 ≤ σ j)
    (hnσ : Tendsto (fun j => (n j : ℝ) * σ j) atTop (𝓝 w)) :
    Tendsto (fun j => hypSum (n j) d c (σ j)) atTop (𝓝 (∑' l, limitTerm c w l)) := by
  simp only [hypSum_eq_tsum]
  set B : ℝ := |w| + 1 with hB
  have hB0 : 0 ≤ B := by positivity
  have hnR : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hσ : Tendsto σ atTop (𝓝 0) := by
    have h := hnσ.div_atTop hnR
    refine h.congr' ?_
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hj
    have : (n j : ℝ) ≠ 0 := by exact_mod_cast (by omega : n j ≠ 0)
    field_simp
  have hev1 : ∀ᶠ j in atTop, (n j : ℝ) * σ j ≤ B := by
    have := hnσ.eventually (eventually_le_nhds (by linarith [le_abs_self w] : w < |w| + 1))
    exact this
  have hev2 : ∀ᶠ j in atTop, σ j ≤ 1 := hσ.eventually (eventually_le_nhds one_pos)
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun l => (B * (2 * B + d) / min c 1) ^ l / l.factorial)
    (summable_bound c _) (fun l => tendsto_hypTerm hn hnσ l) ?_
  filter_upwards [hev1, hev2] with j hj1 hj2
  intro l
  rw [Real.norm_eq_abs]
  exact abs_hypTerm_le hd hc (hσ0 j) hj2 hj1 hB0 l

/-! ## The two limit series -/

theorem rising_half_mul_factorial (l : ℕ) :
    rising (1 / 2) l * l.factorial = ((2 * l).factorial : ℝ) / 4 ^ l := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [rising_succ, Nat.factorial_succ, show 2 * (l + 1) = 2 * l + 1 + 1 by ring,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      have h4 : (4 : ℝ) ^ l ≠ 0 := by positivity
      have : rising (1 / 2) l * (1 / 2 + l) * ((l + 1) * l.factorial) =
          (rising (1 / 2) l * l.factorial) * ((1 / 2 + l) * (l + 1)) := by ring
      rw [this, ih]
      field_simp
      ring

theorem rising_three_half_mul_factorial (l : ℕ) :
    rising (3 / 2) l * l.factorial = ((2 * l + 1).factorial : ℝ) / 4 ^ l := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [rising_succ, Nat.factorial_succ, show 2 * (l + 1) + 1 = 2 * l + 1 + 1 + 1 by ring,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      have h4 : (4 : ℝ) ^ l ≠ 0 := by positivity
      have : rising (3 / 2) l * (3 / 2 + l) * ((l + 1) * l.factorial) =
          (rising (3 / 2) l * l.factorial) * ((3 / 2 + l) * (l + 1)) := by ring
      rw [this, ih]
      field_simp
      ring

/-- `c = 1/2`: the limit series is `cos(2w)`. -/
theorem tsum_limitTerm_half (w : ℝ) : ∑' l, limitTerm (1 / 2) w l = Real.cos (2 * w) := by
  have h := Real.hasSum_cos (2 * w)
  rw [← h.tsum_eq]
  congr 1
  funext l
  unfold limitTerm
  rw [rising_half_mul_factorial, mul_pow, pow_mul, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
  have h4 : (4 : ℝ) ^ l ≠ 0 := by positivity
  have hf : ((2 * l).factorial : ℝ) ≠ 0 := by exact_mod_cast (2 * l).factorial_ne_zero
  field_simp

/-- `c = 3/2`: the limit series is `sin(2w)/(2w)` for `w ≠ 0`. -/
theorem tsum_limitTerm_three_half {w : ℝ} (hw : w ≠ 0) :
    ∑' l, limitTerm (3 / 2) w l = Real.sin (2 * w) / (2 * w) := by
  have h := Real.hasSum_sin (2 * w)
  have h2w : (2 * w) ≠ 0 := by positivity
  have h' := h.div_const (2 * w)
  rw [← h'.tsum_eq]
  congr 1
  funext l
  unfold limitTerm
  rw [rising_three_half_mul_factorial, pow_succ, mul_pow, pow_mul, pow_mul,
    show (2 : ℝ) ^ 2 = 4 by norm_num]
  have h4 : (4 : ℝ) ^ l ≠ 0 := by positivity
  have hf : ((2 * l + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (2 * l + 1).factorial_ne_zero
  field_simp

/-! ## The square-variable form and the Ring.choose bridge -/

/-- The terminating `₂F₁(−n, n+d; c; x)` in the variable `x` (so `hypSum n d c σ = hypSumSq n d c (σ²)`). -/
noncomputable def hypSumSq (n : ℕ) (d c x : ℝ) : ℝ :=
  ∑ l ∈ range (n + 1),
    (-1) ^ l * fallingNat n l * rising ((n : ℝ) + d) l / (rising c l * l.factorial) * x ^ l

theorem hypSum_eq_hypSumSq (n : ℕ) (d c σ : ℝ) : hypSum n d c σ = hypSumSq n d c (σ ^ 2) := by
  unfold hypSum hypSumSq hypTerm
  apply sum_congr rfl
  intro l _
  rw [← pow_mul, mul_comm 2 l]

theorem rising_add (a : ℝ) (m k : ℕ) : rising a (m + k) = rising a m * rising (a + m) k := by
  unfold rising
  rw [prod_range_add]
  congr 1
  apply prod_congr rfl
  intro i _
  push_cast
  ring

theorem fallingNat_eq_factorial_mul_choose (n l : ℕ) :
    fallingNat n l = (l.factorial : ℝ) * (n.choose l : ℝ) := by
  unfold fallingNat
  have h := descPochhammer_eval_eq_prod_range (R := ℝ) l (n : ℝ)
  rw [← h, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

theorem descPochhammer_int_smeval_real (a : ℝ) (n : ℕ) :
    (descPochhammer ℤ n).smeval a = ∏ i ∈ range n, (a - i) := by
  induction n with
  | zero => simp [descPochhammer_zero, Polynomial.smeval_one]
  | succ n ih =>
      rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, prod_range_succ,
        Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
      simp

theorem ringChoose_eq_prod_div_factorial (a : ℝ) (n : ℕ) :
    Ring.choose a n = (∏ i ∈ range n, (a - i)) / n.factorial := by
  rw [Ring.choose_eq_smul, descPochhammer_int_smeval_real, smul_eq_mul, div_eq_inv_mul]

theorem ringChoose_neg_eq_rising (a : ℝ) (n : ℕ) :
    Ring.choose (-a) n = (-1) ^ n * rising a n / n.factorial := by
  rw [ringChoose_eq_prod_div_factorial]
  congr 1
  unfold rising
  rw [show (∏ i ∈ range n, (-a - (i : ℝ))) = ∏ i ∈ range n, ((-1) * (a + i)) by
    apply prod_congr rfl; intro i _; ring]
  rw [prod_mul_distrib, prod_const, card_range]

theorem normalizedCentralBinom_eq_rising_half_div (n : ℕ) :
    (Nat.centralBinom n : ℝ) / 4 ^ n = rising (1 / 2) n / n.factorial := by
  have h := rising_half_mul_factorial n
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hcb := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [← Nat.centralBinom_eq_two_mul_choose, show 2 * n - n = n by omega] at hcb
  have hcb' : ((2 * n).factorial : ℝ) = Nat.centralBinom n * n.factorial * n.factorial := by
    exact_mod_cast hcb.symm
  rw [div_eq_div_iff h4 hf]
  have h2 : rising (1 / 2) n * 4 ^ n * n.factorial =
      (Nat.centralBinom n : ℝ) * n.factorial * n.factorial := by
    have h' := h
    field_simp at h'
    rw [hcb'] at h'
    linear_combination h'
  exact (mul_right_cancel₀ hf h2).symm

end ScaledHypergeometric

end RHTower
