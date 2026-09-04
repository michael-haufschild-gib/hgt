import GaloisForLFunctions.RHTower.Sieve.MRFibreReduction
import GaloisForLFunctions.RHTower.Sieve.PairFibreMeanSquare
import GaloisForLFunctions.RHTower.Sieve.PairFibreTrivial

/-!
# Route E: a short-interval rate is not a strict-half-power bound

Route E's harmonic front asks for Menon's short-interval mean square

    (1/X) ∫_X^{2X} |(1/h) ∑_{x ≤ n ≤ x+h} μ(n)|² dx ≪ (log log h)²/(log h)² + (log log X)⁴/(log X)²

(S. Menon, arXiv:2607.15574, Theorem 1.1), and the marker cards consume it only through the
corpus's MR-reduced hypothesis `AveragedShortInterval`: the average over the dyadic block of fibre
starts of the absolute fibre sum is `o(h√x)`.  The route's RH step is the all-strict-half-power
bound on the Möbius partial sums, which is RH itself
(`mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis`,
`routeEParityColumnDefectAllStrictHalfPowerBound_implies_riemannHypothesis`).

This file records the separation between the two as a theorem, so that the harmonic front cannot
be mistaken for progress on the RH step.  The witness `logThinnedSign` is `(-1)^n` with, on the
dyadic block `2^j ≤ n < 2^(j+1)`, one sign in every `2(j+1)` flipped to `+1`.  It is `±1`-valued
and satisfies, at **every** start `a ≥ 1` and every length `h ≤ a` (not merely almost all starts),

    |∑_{a ≤ n < a+h} f(n)| ≤ 5 + 2h/(⌊log₂ a⌋ + 1),

so its Menon-type mean square is `O(1/h² + 1/(log X)²)`, better than Menon's rate
(`meanSquare_logThinnedSign_le`); it satisfies `AveragedShortInterval f hh` for every window law
`hh → ∞` with `hh + 2 ≤ √x/2` (`averagedShortInterval_logThinnedSign`); and its partial sums at
`N = 2^m` are at least `2^(m-1)/m - 3m`, so no bound `|∑_{n<N} f(n)| ≤ C (N+1)^(1/2+δ)` with
`0 < δ < 1/2` holds (`logThinnedSign_not_strictHalfPowerBound`).

Consequently no argument that uses of `μ` only `|μ| ≤ 1`, a short-interval bound of Menon's shape
at any rate `φ` with `N·φ(N) ≫ N^(1/2+δ)`, and the corpus's averaged fibre hypothesis can reach the
strict-half-power bound.  The general schedule `blockThinnedSign K` records the trade-off for an
arbitrary thinning `K`: interval sums are `O(1 + h/K)` and partial sums are `≳ ∑_j 2^j/K_j`.
-/

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-- The block-thinned alternating sign with schedule `K`: `(-1)^n`, except that on the dyadic
block `2^j ≤ n < 2^(j+1)` the sign at every `n ≡ -1 (mod 2 K j)` is flipped to `+1`. -/
def blockThinnedSign (K : ℕ → ℕ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n + 2 * (if 2 * K (Nat.log 2 n) ∣ n + 1 then 1 else 0)

/-- The logarithmic schedule `K j = j + 1`: one flipped sign in every `2(⌊log₂ n⌋ + 1)`. -/
def logThinnedSign : ℕ → ℝ := blockThinnedSign (fun j => j + 1)

/-- The thinned sign takes only the values `±1`. -/
theorem blockThinnedSign_eq_one_or_neg_one (K : ℕ → ℕ) (n : ℕ) :
    blockThinnedSign K n = 1 ∨ blockThinnedSign K n = -1 := by
  unfold blockThinnedSign
  by_cases hd : 2 * K (Nat.log 2 n) ∣ n + 1
  · left
    have h2 : 2 ∣ n + 1 := (dvd_mul_right 2 _).trans hd
    have hne : ¬ Even n := Nat.even_add_one.mp (even_iff_two_dvd.mpr h2)
    have hodd : Odd n := Nat.not_even_iff_odd.mp hne
    rw [if_pos hd, hodd.neg_one_pow]
    norm_num
  · rw [if_neg hd, mul_zero, add_zero]
    exact neg_one_pow_eq_or ℝ n

theorem abs_blockThinnedSign_le_one (K : ℕ → ℕ) (n : ℕ) :
    |blockThinnedSign K n| ≤ 1 := by
  rcases blockThinnedSign_eq_one_or_neg_one K n with h | h <;> rw [h] <;> norm_num

/-- An interval sum of the thinned sign is the alternating sum plus twice the number of flips. -/
theorem sum_Ico_blockThinnedSign (K : ℕ → ℕ) (a b : ℕ) :
    ∑ n ∈ Ico a b, blockThinnedSign K n =
      (∑ n ∈ Ico a b, (-1 : ℝ) ^ n) +
        2 * ((((Ico a b).filter (fun n => 2 * K (Nat.log 2 n) ∣ n + 1)).card : ℕ) : ℝ) := by
  unfold blockThinnedSign
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]

theorem sum_range_neg_one_pow_eq_zero_or_one (N : ℕ) :
    (∑ n ∈ range N, (-1 : ℝ) ^ n) = 0 ∨ (∑ n ∈ range N, (-1 : ℝ) ^ n) = 1 := by
  rw [neg_one_geom_sum]
  split_ifs <;> simp

theorem abs_sum_Ico_neg_one_pow_le {a b : ℕ} (hab : a ≤ b) :
    |∑ n ∈ Ico a b, (-1 : ℝ) ^ n| ≤ 1 := by
  rw [Finset.sum_Ico_eq_sub _ hab]
  rcases sum_range_neg_one_pow_eq_zero_or_one b with hb | hb <;>
    rcases sum_range_neg_one_pow_eq_zero_or_one a with ha | ha <;>
    rw [hb, ha] <;> norm_num

/-- Integers `n ∈ [a, b)` with `m ∣ n + 1`. -/
theorem card_filter_dvd_succ_Ico {a b : ℕ} (m : ℕ) (hab : a ≤ b) :
    ((Ico a b).filter (fun n => m ∣ n + 1)).card = b / m - a / m := by
  classical
  rw [← card_filter_dvd_Ioc m a b hab, Finset.card_filter, Finset.card_filter]
  have h := Finset.sum_Ico_add' (fun x => if m ∣ x then 1 else 0) a b 1
  rw [h, Finset.Ico_add_one_add_one_eq_Ioc]

theorem cast_div_sub_div_le {a b m : ℕ} (hab : a ≤ b) (hm : 0 < m) :
    ((b / m - a / m : ℕ) : ℝ) ≤ ((b : ℝ) - a) / m + 1 := by
  rw [Nat.cast_sub (Nat.div_le_div_right hab), sub_div]
  obtain ⟨hb1, -⟩ := cast_div_bounds (d := m) (n := b) hm
  obtain ⟨-, ha2⟩ := cast_div_bounds (d := m) (n := a) hm
  linarith

theorem le_cast_div_sub_div {a b m : ℕ} (hab : a ≤ b) (hm : 0 < m) :
    ((b : ℝ) - a) / m - 1 ≤ ((b / m - a / m : ℕ) : ℝ) := by
  rw [Nat.cast_sub (Nat.div_le_div_right hab), sub_div]
  obtain ⟨-, hb2⟩ := cast_div_bounds (d := m) (n := b) hm
  obtain ⟨ha1, -⟩ := cast_div_bounds (d := m) (n := a) hm
  linarith

theorem log_two_eq_of_mem_Ico_pow {j n : ℕ} (hn : n ∈ Ico (2 ^ j) (2 ^ (j + 1))) :
    Nat.log 2 n = j := by
  rw [Finset.mem_Ico] at hn
  exact Nat.log_eq_of_pow_le_of_lt_pow hn.1 hn.2

/-- The number of flips on the dyadic block `[2^j, 2^(j+1))`. -/
theorem card_filter_block (K : ℕ → ℕ) (j : ℕ) :
    ((Ico (2 ^ j) (2 ^ (j + 1))).filter (fun n => 2 * K (Nat.log 2 n) ∣ n + 1)).card
      = 2 ^ (j + 1) / (2 * K j) - 2 ^ j / (2 * K j) := by
  classical
  rw [← card_filter_dvd_succ_Ico (2 * K j) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j))]
  congr 1
  apply Finset.filter_congr
  intro n hn
  rw [log_two_eq_of_mem_Ico_pow hn]

/-- The block sum of the thinned sign is at least `2^j/K_j - 3`. -/
theorem sum_block_blockThinnedSign_ge (K : ℕ → ℕ) (hK : ∀ j, 1 ≤ K j) (j : ℕ) :
    (2 : ℝ) ^ j / K j - 3 ≤ ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), blockThinnedSign K n := by
  rw [sum_Ico_blockThinnedSign, card_filter_block]
  have hpow : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)
  have hm : 0 < 2 * K j := by have := hK j; omega
  have hcount := le_cast_div_sub_div hpow hm
  have halt := abs_le.mp (abs_sum_Ico_neg_one_pow_le hpow)
  have hKR : (0 : ℝ) < (K j : ℝ) := by exact_mod_cast hK j
  have hcast : (((2 ^ (j + 1) : ℕ) : ℝ) - ((2 ^ j : ℕ) : ℝ)) / ((2 * K j : ℕ) : ℝ)
      = (2 : ℝ) ^ j / K j / 2 := by
    push_cast
    field_simp
    ring
  rw [hcast] at hcount
  linarith [halt.1]

/-- Partial sums at powers of two: at least `∑_{j<m} (2^j/K_j - 3)`. -/
theorem sum_range_pow_blockThinnedSign_ge (K : ℕ → ℕ) (hK : ∀ j, 1 ≤ K j) (m : ℕ) :
    ∑ j ∈ range m, ((2 : ℝ) ^ j / K j - 3) ≤ ∑ n ∈ range (2 ^ m), blockThinnedSign K n := by
  induction m with
  | zero =>
    simp only [Finset.sum_range_zero, pow_zero, Finset.sum_range_one]
    unfold blockThinnedSign
    have hnd : ¬ (2 * K (Nat.log 2 0) ∣ 0 + 1) := by
      intro h
      have h1 := Nat.le_of_dvd Nat.one_pos h
      have h2 := hK (Nat.log 2 0)
      omega
    rw [if_neg hnd]
    norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ,
      ← Finset.sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m))]
    exact add_le_add ih (sum_block_blockThinnedSign_ge K hK m)

/-- Partial sums at an arbitrary `N ≥ 1`. -/
theorem sum_range_blockThinnedSign_ge (K : ℕ → ℕ) (hK : ∀ j, 1 ≤ K j) {N : ℕ} (hN : 1 ≤ N) :
    (∑ j ∈ range (Nat.log 2 N), ((2 : ℝ) ^ j / K j - 3)) - 1
      ≤ ∑ n ∈ range N, blockThinnedSign K n := by
  have hle : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  rw [← Finset.sum_range_add_sum_Ico _ hle, sum_Ico_blockThinnedSign]
  have h1 := sum_range_pow_blockThinnedSign_ge K hK (Nat.log 2 N)
  have h2 := abs_le.mp (abs_sum_Ico_neg_one_pow_le hle)
  have h3 : (0 : ℝ) ≤ ((((Ico (2 ^ Nat.log 2 N) N).filter
      (fun n => 2 * K (Nat.log 2 n) ∣ n + 1)).card : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith [h2.1]

/-- The number of flips in `[a, a+h)`, `h ≤ a`, is at most `h/K_J + 2` with `J = ⌊log₂ a⌋`. -/
theorem card_filter_Ico_le (K : ℕ → ℕ) (hK : ∀ j, 1 ≤ K j) (hmono : Monotone K)
    {a h : ℕ} (hha : h ≤ a) :
    ((((Ico a (a + h)).filter (fun n => 2 * K (Nat.log 2 n) ∣ n + 1)).card : ℕ) : ℝ)
      ≤ (h : ℝ) / K (Nat.log 2 a) + 2 := by
  classical
  set J := Nat.log 2 a with hJ
  have hlog : ∀ n ∈ Ico a (a + h), Nat.log 2 n = J ∨ Nat.log 2 n = J + 1 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hlo : J ≤ Nat.log 2 n := Nat.log_mono_right hn.1
    have ha2 : a < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
    have hn2 : n < 2 ^ (J + 2) := by
      calc n < a + h := hn.2
        _ ≤ 2 * a := by omega
        _ < 2 ^ (J + 2) := by rw [pow_succ]; omega
    have hhi : Nat.log 2 n < J + 2 := Nat.log_lt_of_lt_pow (by omega) hn2
    omega
  have hsub : (Ico a (a + h)).filter (fun n => 2 * K (Nat.log 2 n) ∣ n + 1)
      ⊆ (Ico a (a + h)).filter (fun n => 2 * K J ∣ n + 1)
        ∪ (Ico a (a + h)).filter (fun n => 2 * K (J + 1) ∣ n + 1) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hlog n hn.1 with hl | hl
    · left
      refine ⟨hn.1, ?_⟩
      rw [hl] at hn
      exact hn.2
    · right
      refine ⟨hn.1, ?_⟩
      rw [hl] at hn
      exact hn.2
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hab : a ≤ a + h := Nat.le_add_right a h
  have hmJ : 0 < 2 * K J := by have := hK J; omega
  have hmJ1 : 0 < 2 * K (J + 1) := by have := hK (J + 1); omega
  have hKJ : (0 : ℝ) < K J := by exact_mod_cast hK J
  have hKmono : (2 * K J : ℝ) ≤ 2 * K (J + 1) := by
    have := hmono (Nat.le_succ J)
    exact_mod_cast Nat.mul_le_mul_left 2 this
  have hc1 : ((((Ico a (a + h)).filter (fun n => 2 * K J ∣ n + 1)).card : ℕ) : ℝ)
      ≤ (h : ℝ) / (2 * K J) + 1 := by
    rw [card_filter_dvd_succ_Ico _ hab]
    have h1 := cast_div_sub_div_le hab hmJ
    have h2 : (((a + h : ℕ) : ℝ) - a) / ((2 * K J : ℕ) : ℝ) = (h : ℝ) / (2 * K J) := by
      push_cast
      ring
    rw [h2] at h1
    exact h1
  have hc2 : ((((Ico a (a + h)).filter (fun n => 2 * K (J + 1) ∣ n + 1)).card : ℕ) : ℝ)
      ≤ (h : ℝ) / (2 * K J) + 1 := by
    rw [card_filter_dvd_succ_Ico _ hab]
    have h1 := cast_div_sub_div_le hab hmJ1
    have h2 : (((a + h : ℕ) : ℝ) - a) / ((2 * K (J + 1) : ℕ) : ℝ) = (h : ℝ) / (2 * K (J + 1)) := by
      push_cast
      ring
    rw [h2] at h1
    have h3 : (h : ℝ) / (2 * K (J + 1)) ≤ (h : ℝ) / (2 * K J) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg h) (by positivity) hKmono
    linarith
  have hcardR : ((((Ico a (a + h)).filter (fun n => 2 * K (Nat.log 2 n) ∣ n + 1)).card : ℕ) : ℝ)
      ≤ ((((Ico a (a + h)).filter (fun n => 2 * K J ∣ n + 1)).card : ℕ) : ℝ)
        + ((((Ico a (a + h)).filter (fun n => 2 * K (J + 1) ∣ n + 1)).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hsum : (h : ℝ) / (2 * K J) + (h : ℝ) / (2 * K J) = (h : ℝ) / K J := by
    field_simp
    ring
  rw [hJ] at hsum
  linarith

/-- **Interval sums of the thinned sign.**  At every start `a ≥ 1` and length `h ≤ a`,
`|∑_{a ≤ n < a+h} f(n)| ≤ 5 + 2h/K_J`, `J = ⌊log₂ a⌋`. -/
theorem abs_sum_Ico_blockThinnedSign_le (K : ℕ → ℕ) (hK : ∀ j, 1 ≤ K j) (hmono : Monotone K)
    {a h : ℕ} (hha : h ≤ a) :
    |∑ n ∈ Ico a (a + h), blockThinnedSign K n| ≤ 5 + 2 * ((h : ℝ) / K (Nat.log 2 a)) := by
  rw [sum_Ico_blockThinnedSign]
  have h1 := abs_le.mp (abs_sum_Ico_neg_one_pow_le (Nat.le_add_right a h))
  have h2 := card_filter_Ico_le K hK hmono hha
  have h3 : (0 : ℝ) ≤ ((((Ico a (a + h)).filter
      (fun n => 2 * K (Nat.log 2 n) ∣ n + 1)).card : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ (h : ℝ) / K (Nat.log 2 a) := by positivity
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-! ### The logarithmic schedule -/

theorem one_le_logSchedule (j : ℕ) : 1 ≤ (fun j : ℕ => j + 1) j := Nat.le_add_left 1 j

theorem monotone_logSchedule : Monotone (fun j : ℕ => j + 1) :=
  fun _ _ hij => Nat.succ_le_succ hij

theorem logThinnedSign_eq_one_or_neg_one (n : ℕ) :
    logThinnedSign n = 1 ∨ logThinnedSign n = -1 :=
  blockThinnedSign_eq_one_or_neg_one _ n

theorem abs_logThinnedSign_le_one (n : ℕ) : |logThinnedSign n| ≤ 1 :=
  abs_blockThinnedSign_le_one _ n

/-- **Every** short-interval sum of the witness is `≤ 5 + 2h/(⌊log₂ a⌋ + 1)`. -/
theorem abs_sum_Ico_logThinnedSign_le {a h : ℕ} (hha : h ≤ a) :
    |∑ n ∈ Ico a (a + h), logThinnedSign n|
      ≤ 5 + 2 * ((h : ℝ) / ((Nat.log 2 a : ℝ) + 1)) := by
  have := abs_sum_Ico_blockThinnedSign_le (fun j => j + 1) one_le_logSchedule
    monotone_logSchedule hha
  unfold logThinnedSign
  simp only [Nat.cast_add, Nat.cast_one] at this
  exact this

/-- **Menon's shape, at a better rate.**  The discrete mean square of the normalised
short-interval sums over `X ≤ x < 2X` is at most `(5/h + 2/(⌊log₂ X⌋ + 1))²`. -/
theorem meanSquare_logThinnedSign_le {X h : ℕ} (hX : 1 ≤ X) (hh : 1 ≤ h) (hhX : h ≤ X) :
    (∑ x ∈ Ico X (2 * X), ((∑ n ∈ Ico x (x + h), logThinnedSign n) / h) ^ 2) / X
      ≤ (5 / (h : ℝ) + 2 / ((Nat.log 2 X : ℝ) + 1)) ^ 2 := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  set B : ℝ := 5 / (h : ℝ) + 2 / ((Nat.log 2 X : ℝ) + 1) with hB
  have hterm : ∀ x ∈ Ico X (2 * X),
      ((∑ n ∈ Ico x (x + h), logThinnedSign n) / h) ^ 2 ≤ B ^ 2 := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    have hhx : h ≤ x := le_trans hhX hx.1
    have hbound := abs_sum_Ico_logThinnedSign_le hhx
    have hlogle : (Nat.log 2 X : ℝ) + 1 ≤ (Nat.log 2 x : ℝ) + 1 := by
      have := Nat.log_mono_right (b := 2) hx.1
      have h' : Nat.log 2 X + 1 ≤ Nat.log 2 x + 1 := Nat.succ_le_succ this
      exact_mod_cast h'
    have hlog0 : (0 : ℝ) < (Nat.log 2 X : ℝ) + 1 := by positivity
    have hrat : (h : ℝ) / ((Nat.log 2 x : ℝ) + 1) ≤ (h : ℝ) / ((Nat.log 2 X : ℝ) + 1) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg h) hlog0 hlogle
    have habs : |(∑ n ∈ Ico x (x + h), logThinnedSign n) / h| ≤ B := by
      rw [abs_div, abs_of_pos hhR, div_le_iff₀ hhR, hB]
      have : (5 / (h : ℝ) + 2 / ((Nat.log 2 X : ℝ) + 1)) * h
          = 5 + 2 * ((h : ℝ) / ((Nat.log 2 X : ℝ) + 1)) := by
        field_simp
        try ring
      rw [this]
      linarith
    calc ((∑ n ∈ Ico x (x + h), logThinnedSign n) / h) ^ 2
        = |(∑ n ∈ Ico x (x + h), logThinnedSign n) / h| ^ 2 := (sq_abs _).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcard : ((2 * X - X : ℕ) : ℝ) = X := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcard] at hsum
  rw [div_le_iff₀ hXR]
  linarith

/-- Partial sums of the witness at `N = 2^m` are at least `2^(m-1)/m - 3m`. -/
theorem sum_range_pow_logThinnedSign_ge {m : ℕ} (hm : 1 ≤ m) :
    (2 : ℝ) ^ (m - 1) / m - 3 * m ≤ ∑ n ∈ range (2 ^ m), logThinnedSign n := by
  have h := sum_range_pow_blockThinnedSign_ge (fun j => j + 1) one_le_logSchedule m
  refine le_trans ?_ h
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have hpart : ∀ j ∈ range k,
      (-3 : ℝ) ≤ (2 : ℝ) ^ j / (((fun j : ℕ => j + 1) j : ℕ) : ℝ) - 3 := by
    intro j _
    have : (0 : ℝ) ≤ (2 : ℝ) ^ j / (((fun j : ℕ => j + 1) j : ℕ) : ℝ) := by positivity
    linarith
  have hsum := Finset.sum_le_sum hpart
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  simp only [Nat.add_sub_cancel]
  push_cast at hsum ⊢
  linarith

/-- **The witness violates every strict-half-power bound.**  For `0 < δ < 1/2` and every `C`,
`|∑_{n<N} f(n)| ≤ C (N+1)^(1/2+δ)` fails at some `N = 2^m`. -/
theorem logThinnedSign_not_strictHalfPowerBound {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (C : ℝ) :
    ¬ ∀ N : ℕ, |∑ n ∈ range N, logThinnedSign n| ≤ C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
  intro hbound
  set θ : ℝ := 1 / 2 - δ with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  set s : ℝ := (2 : ℝ) ^ (θ / 3) with hs
  have hs1 : 1 < s := Real.one_lt_rpow (by norm_num) (by positivity)
  set c : ℝ := s - 1 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc3 : 0 < c ^ 3 := by positivity
  obtain ⟨m, hm1, hmc⟩ : ∃ m : ℕ, 1 ≤ m ∧ (4 * |C| + 8) / c ^ 3 ≤ (m : ℝ) := by
    refine ⟨⌈(4 * |C| + 8) / c ^ 3⌉₊ + 1, by omega, ?_⟩
    have := Nat.le_ceil ((4 * |C| + 8) / c ^ 3)
    push_cast
    linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmc' : 4 * |C| + 8 ≤ (m : ℝ) * c ^ 3 := by
    rwa [div_le_iff₀ hc3] at hmc
  set P : ℝ := ((2 : ℝ) ^ m) ^ (1 - θ) with hP
  have h2m0 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h2m1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hP1 : 1 ≤ P := Real.one_le_rpow h2m1 (by linarith)
  have hQ : ((2 : ℝ) ^ m) ^ θ = s ^ (3 * m) := by
    have e1 : ((2 : ℝ) ^ m) ^ θ = (2 : ℝ) ^ ((m : ℝ) * θ) := by
      rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have e2 : s ^ (3 * m) = (2 : ℝ) ^ (θ / 3 * ((3 * m : ℕ) : ℝ)) := by
      rw [hs, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    rw [e1, e2]
    congr 1
    push_cast
    ring
  have h1c : 1 + c = s := by rw [hc]; ring
  have hbern : (m : ℝ) * c ≤ s ^ m := by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ c) m
    rw [h1c] at this
    linarith
  have hmc0 : 0 ≤ (m : ℝ) * c := by positivity
  have hcube : ((m : ℝ) * c) ^ 3 ≤ s ^ (3 * m) := by
    rw [mul_comm 3 m, pow_mul]
    exact pow_le_pow_left₀ hmc0 hbern 3
  have hlow := sum_range_pow_logThinnedSign_ge hm1
  have hsplit : (2 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ θ * P := by
    rw [hP, ← Real.rpow_add h2m0]
    simp
  have hhalf : (2 : ℝ) ^ (m - 1) = (2 : ℝ) ^ m / 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  have hup := hbound (2 ^ m)
  have hcastpow : (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m := by push_cast; ring
  rw [hcastpow] at hup
  have hexp : (1 / 2 : ℝ) + δ = 1 - θ := by rw [hθ]; ring
  rw [hexp] at hup
  have hN1 : ((2 : ℝ) ^ m + 1) ^ (1 - θ) ≤ 2 * P := by
    calc ((2 : ℝ) ^ m + 1) ^ (1 - θ) ≤ (2 * (2 : ℝ) ^ m) ^ (1 - θ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (2 : ℝ) ^ (1 - θ) * P := by rw [Real.mul_rpow (by norm_num) h2m0.le]
      _ ≤ 2 * P := by
          have : (2 : ℝ) ^ (1 - θ) ≤ 2 := by
            calc (2 : ℝ) ^ (1 - θ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
          exact mul_le_mul_of_nonneg_right this (by linarith)
  have hM : ∑ n ∈ range (2 ^ m), logThinnedSign n ≤ 2 * |C| * P := by
    have h1 := (abs_le.mp hup).2
    have h2 : C * ((2 : ℝ) ^ m + 1) ^ (1 - θ) ≤ |C| * (2 * P) := by
      calc C * ((2 : ℝ) ^ m + 1) ^ (1 - θ) ≤ |C| * ((2 : ℝ) ^ m + 1) ^ (1 - θ) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * (2 * P) := mul_le_mul_of_nonneg_left hN1 (abs_nonneg C)
    linarith
  have hQge : (m : ℝ) ^ 3 * c ^ 3 ≤ ((2 : ℝ) ^ m) ^ θ := by
    rw [hQ]
    calc (m : ℝ) ^ 3 * c ^ 3 = ((m : ℝ) * c) ^ 3 := by ring
      _ ≤ s ^ (3 * m) := hcube
  have hmpos : (0 : ℝ) < m := by linarith
  have hlow' : P * ((m : ℝ) ^ 2 * c ^ 3 / 2) - 3 * m
      ≤ ∑ n ∈ range (2 ^ m), logThinnedSign n := by
    refine le_trans ?_ hlow
    rw [hhalf]
    have : P * ((m : ℝ) ^ 2 * c ^ 3 / 2) ≤ (2 : ℝ) ^ m / 2 / m := by
      rw [hsplit, div_div, le_div_iff₀ (by positivity)]
      calc P * ((m : ℝ) ^ 2 * c ^ 3 / 2) * (2 * m) = P * ((m : ℝ) ^ 3 * c ^ 3) := by ring
        _ ≤ P * ((2 : ℝ) ^ m) ^ θ := mul_le_mul_of_nonneg_left hQge (by linarith)
        _ = ((2 : ℝ) ^ m) ^ θ * P := by ring
    linarith
  have hbr : 4 * (m : ℝ) ≤ (m : ℝ) ^ 2 * c ^ 3 / 2 - 2 * |C| := by
    have h1 : (m : ℝ) * (4 * |C| + 8) ≤ (m : ℝ) * ((m : ℝ) * c ^ 3) :=
      mul_le_mul_of_nonneg_left hmc' (by linarith)
    have h2 : |C| ≤ (m : ℝ) * |C| := by
      have := mul_le_mul_of_nonneg_right hmR (abs_nonneg C)
      linarith
    nlinarith [h1, h2]
  have hfinal : P * (4 * (m : ℝ)) ≤ 3 * m := by
    have h0 := le_trans hlow' hM
    have h1 : P * (4 * (m : ℝ)) ≤ P * ((m : ℝ) ^ 2 * c ^ 3 / 2 - 2 * |C|) :=
      mul_le_mul_of_nonneg_left hbr (by linarith)
    nlinarith [h0, h1]
  have h4m : 4 * (m : ℝ) ≤ P * (4 * m) := by
    have := mul_le_mul_of_nonneg_right hP1 (by positivity : (0 : ℝ) ≤ 4 * m)
    linarith
  linarith

/-! ### The corpus's averaged fibre hypothesis holds for the witness -/

/-- The fibre sums of the witness are `O(1 + h·log 2/log(√x/2))`, uniformly over the block. -/
theorem abs_sum_innerFibre_logThinnedSign_le {x h : ℝ} (hx : 16 ≤ x) (hh : 1 ≤ h)
    (hsmall : h + 2 ≤ Real.sqrt x / 2) {a : ℕ} (ha : a ∈ outerBlock x h) :
    |∑ b ∈ innerFibre x h a, logThinnedSign b|
      ≤ 5 + 2 * ((h + 2) * (Real.log 2 / Real.log (Real.sqrt x / 2))) := by
  have hx4 : 4 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hr4 : 4 ≤ Real.sqrt x := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have := Real.sqrt_le_sqrt hx
    rwa [h16] at this
  have hr0 : 0 < Real.sqrt x := by linarith
  have hL : 0 < Real.log (Real.sqrt x / 2) := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu0 : 0 < Real.log 2 / Real.log (Real.sqrt x / 2) := div_pos hl2 hL
  have ha' := mem_outerBlock.mp ha
  obtain ⟨⟨ha1, -⟩, halo, hahi⟩ := ha'
  have haR : (0 : ℝ) < a := by exact_mod_cast ha1
  have hxa : Real.sqrt x / 2 ≤ x / a := by
    have h1 : x / (2 * Real.sqrt x) ≤ x / a :=
      div_le_div_of_nonneg_left hx0.le haR hahi
    have h2 : x / (2 * Real.sqrt x) = Real.sqrt x / 2 := by
      rw [show x / (2 * Real.sqrt x) = (x / Real.sqrt x) / 2 by ring, Real.div_sqrt]
    linarith
  set lo : ℕ := ⌈x / (a : ℝ)⌉₊ with hlo
  set hi : ℕ := ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ with hhi
  have hfib : innerFibre x h a = Finset.Ico lo (hi + 1) := by
    rw [innerFibre_eq hx4 (by linarith) ha, Finset.Ico_add_one_right_eq_Icc]
  have hlo1 : 1 ≤ lo := Nat.one_le_ceil_iff.mpr (div_pos hx0 haR)
  have hloR : x / a ≤ (lo : ℝ) := Nat.le_ceil _
  have hhiR : (hi : ℝ) ≤ (x + h * Real.sqrt x) / a := Nat.floor_le (by positivity)
  have hlen : (x + h * Real.sqrt x) / a - x / a ≤ h := by
    rw [← sub_div, add_sub_cancel_left, div_le_iff₀ haR]
    exact mul_le_mul_of_nonneg_left halo (by linarith)
  rw [hfib]
  by_cases hcase : hi + 1 ≤ lo
  · rw [Finset.Ico_eq_empty_of_le hcase, Finset.sum_empty, abs_zero]
    positivity
  · rw [not_le] at hcase
    have hLdef : hi + 1 = lo + (hi + 1 - lo) := by omega
    rw [hLdef]
    have hLR : ((hi + 1 - lo : ℕ) : ℝ) ≤ h + 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    have hLle : hi + 1 - lo ≤ lo := by
      have : ((hi + 1 - lo : ℕ) : ℝ) ≤ (lo : ℝ) := by linarith
      exact_mod_cast this
    have hbound := abs_sum_Ico_logThinnedSign_le hLle
    refine le_trans hbound ?_
    set J := Nat.log 2 lo with hJ
    have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
    have hlo2 : (lo : ℝ) < (2 : ℝ) ^ (J + 1) := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) lo
      exact_mod_cast this
    have hlogJ : Real.log (Real.sqrt x / 2) ≤ ((J : ℝ) + 1) * Real.log 2 := by
      calc Real.log (Real.sqrt x / 2) ≤ Real.log (lo : ℝ) :=
            Real.log_le_log (by linarith) (le_trans hxa hloR)
        _ ≤ Real.log ((2 : ℝ) ^ (J + 1)) :=
            Real.log_le_log (by exact_mod_cast hlo1) hlo2.le
        _ = ((J : ℝ) + 1) * Real.log 2 := by
            rw [Real.log_pow]
            push_cast
            ring
    have hinv : 1 / ((J : ℝ) + 1) ≤ Real.log 2 / Real.log (Real.sqrt x / 2) := by
      rw [div_le_div_iff₀ hJ1 hL]
      linarith
    have hL0 : (0 : ℝ) ≤ ((hi + 1 - lo : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep : ((hi + 1 - lo : ℕ) : ℝ) / ((J : ℝ) + 1)
        ≤ (h + 2) * (Real.log 2 / Real.log (Real.sqrt x / 2)) := by
      calc ((hi + 1 - lo : ℕ) : ℝ) / ((J : ℝ) + 1)
          = ((hi + 1 - lo : ℕ) : ℝ) * (1 / ((J : ℝ) + 1)) := by ring
        _ ≤ (h + 2) * (Real.log 2 / Real.log (Real.sqrt x / 2)) := by
            apply mul_le_mul (by linarith) hinv (by positivity) (by linarith)
    linarith

/-- **The corpus's MR-reduced hypothesis holds for the witness**, for every window law that grows
and stays below `√x/2 - 2`. -/
theorem averagedShortInterval_logThinnedSign {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hsmall : ∀ᶠ x in atTop, hh x + 2 ≤ Real.sqrt x / 2) :
    AveragedShortInterval logThinnedSign hh := by
  unfold AveragedShortInterval
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogtop : Tendsto (fun x : ℝ => Real.log (Real.sqrt x / 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_sqrt_atTop.atTop_div_const (by norm_num))
  have hg : Tendsto (fun x : ℝ => 10 / (hh x * Real.log 2) + 12 / Real.log (Real.sqrt x / 2))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 10 / (hh x * Real.log 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hgrow.atTop_mul_const hl2)
    have h2 : Tendsto (fun x : ℝ => 12 / Real.log (Real.sqrt x / 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlogtop
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [hgrow.eventually_ge_atTop 1, eventually_ge_atTop (16 : ℝ)] with x hhx hx
    have hr0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have hnum : 0 ≤ ∑ a ∈ outerBlock x (hh x), |∑ b ∈ innerFibre x (hh x) a, logThinnedSign b| :=
      Finset.sum_nonneg (fun a _ => abs_nonneg _)
    positivity
  · filter_upwards [hgrow.eventually_ge_atTop 1, eventually_ge_atTop (16 : ℝ), hsmall]
      with x hhx hx hsm
    have hx4 : 4 ≤ x := by linarith
    have hr4 : 4 ≤ Real.sqrt x := by
      have h16 : Real.sqrt 16 = 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have := Real.sqrt_le_sqrt hx
      rwa [h16] at this
    have hr0 : 0 < Real.sqrt x := by linarith
    have hL : 0 < Real.log (Real.sqrt x / 2) := Real.log_pos (by linarith)
    set u : ℝ := Real.log 2 / Real.log (Real.sqrt x / 2) with hu
    have hu0 : 0 < u := div_pos hl2 hL
    set B : ℝ := 5 + 2 * ((hh x + 2) * u) with hB
    have hB0 : 0 ≤ B := by positivity
    have hterm : ∀ a ∈ outerBlock x (hh x),
        |∑ b ∈ innerFibre x (hh x) a, logThinnedSign b| ≤ B :=
      fun a ha => abs_sum_innerFibre_logThinnedSign_le hx hhx hsm ha
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hcard := card_outerBlock_le hx4 (by linarith : (0 : ℝ) ≤ hh x)
    have hS : ∑ a ∈ outerBlock x (hh x), |∑ b ∈ innerFibre x (hh x) a, logThinnedSign b|
        ≤ (Real.sqrt x + 1) * B :=
      le_trans hsum (mul_le_mul_of_nonneg_right hcard hB0)
    have hden : 0 < hh x * Real.sqrt x * Real.log 2 := by positivity
    rw [div_le_iff₀ hden]
    have hgoal : (Real.sqrt x + 1) * B
        ≤ (10 / (hh x * Real.log 2) + 12 / Real.log (Real.sqrt x / 2))
          * (hh x * Real.sqrt x * Real.log 2) := by
      have hrhs : (10 / (hh x * Real.log 2) + 12 / Real.log (Real.sqrt x / 2))
          * (hh x * Real.sqrt x * Real.log 2)
            = 10 * Real.sqrt x + 12 * (hh x * Real.sqrt x * u) := by
        rw [hu]
        field_simp
        try ring
      rw [hrhs, hB]
      have hur : 4 * u ≤ Real.sqrt x * u := by nlinarith
      have hhu : 0 ≤ hh x * u := by positivity
      have hhur : 0 ≤ hh x * (Real.sqrt x * u) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hur (by linarith : (0 : ℝ) ≤ hh x)]
    exact le_trans hS hgoal

/-- **Route E rate no-go.**  There is a `±1`-valued sequence whose short-interval sums are
`≤ 5 + 2h/(⌊log₂ a⌋ + 1)` at every start `a ≥ 1` and every length `h ≤ a`, which satisfies the
corpus's MR-reduced averaged-fibre hypothesis for every admissible window law, and whose partial
sums violate every strict-half-power bound.  A short-interval rate of Menon's shape — at any rate
`φ` with `N·φ(N) ≫ N^(1/2+δ)`, even pointwise in the start — is therefore not an input from which
the Möbius strict-half-power bound (equivalently RH) can be derived using only `|μ| ≤ 1`. -/
theorem routeE_shortIntervalRate_not_strictHalfPower :
    ∃ f : ℕ → ℝ, (∀ n, f n = 1 ∨ f n = -1) ∧
      (∀ a h : ℕ, h ≤ a →
        |∑ n ∈ Ico a (a + h), f n| ≤ 5 + 2 * ((h : ℝ) / ((Nat.log 2 a : ℝ) + 1))) ∧
      (∀ hh : ℝ → ℝ, Tendsto hh atTop atTop →
        (∀ᶠ x in atTop, hh x + 2 ≤ Real.sqrt x / 2) → AveragedShortInterval f hh) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ C : ℝ,
        ¬ ∀ N : ℕ, |∑ n ∈ range N, f n| ≤ C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)) :=
  ⟨logThinnedSign, logThinnedSign_eq_one_or_neg_one,
    fun _ _ hha => abs_sum_Ico_logThinnedSign_le hha,
    fun _ hgrow hsmall => averagedShortInterval_logThinnedSign hgrow hsmall,
    fun _ hδ0 hδ1 C => logThinnedSign_not_strictHalfPowerBound hδ0 hδ1 C⟩

end

end RHTower.Sieve
