import GaloisForLFunctions.RHTower.ZetaLittlewoodDeficit
import GaloisForLFunctions.RHTower.Sieve.GhsPerronDamped

/-!
# Twisting a multiplicative function shifts its character frequency

Multiplying a sequence by the archimedean character of frequency `-τ` translates every multiplicative
distance to a character:

```text
D(f·n^{-iτ}, n^{iv}; P)² = D(f, n^{i(τ+v)}; P)².
```

Consequently the real-twist gap transfers cellwise: on a cell whose effective frequency `τ + v` is at
least `1/2` in modulus and stays inside the polynomial horizon, the twisted function is at squared
distance at least a quarter of the Littlewood deficit from `n^{iv}`.  When the twist itself lies beyond
the whole frequency range of the Perron step, every cell is ordinary, so the corpus's damped Euler bound
applies uniformly and the twisted Dirichlet series obeys

```text
‖L(f·n^{-iτ}, σ+iv)‖ ≤ (1 + 1/(σ−1))·exp(7/2 + 2(σ−1)(log z + log 4) − Δ/4) + tail.
```
-/

open Filter Topology Set

namespace RHTower

noncomputable section

open RHTower.Sieve

/-- The archimedean character is additive in its frequency. -/
theorem charFn_mul_charFn (a b : ℝ) (n : ℕ) :
    charFn a n * charFn b n = charFn (a + b) n := by
  rw [charFn, charFn, charFn, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Conjugation reverses the frequency of the archimedean character. -/
theorem conj_charFn_eq (t : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (charFn t n) = charFn (-t) n := by
  rw [conj_charFn, charFn]
  congr 1
  push_cast
  ring

@[simp] theorem charFn_one (t : ℝ) : charFn t 1 = 1 := by
  rw [charFn]
  norm_num

/-- The character splits over a product of positive integers. -/
theorem charFn_mul_pos (t : ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    charFn t (m * n) = charFn t m * charFn t n := by
  have hlog : Real.log ((m * n : ℕ) : ℝ) = Real.log (m : ℝ) + Real.log (n : ℝ) := by
    push_cast
    exact Real.log_mul (by positivity) (by positivity)
  rw [charFn, charFn, charFn, hlog, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The twist of a sequence by the archimedean character of frequency `-τ`. -/
def twistSeq (f : ℕ → ℂ) (τ : ℝ) : ℕ → ℂ := fun n => f n * charFn (-τ) n

@[simp] theorem twistSeq_apply (f : ℕ → ℂ) (τ : ℝ) (n : ℕ) :
    twistSeq f τ n = f n * charFn (-τ) n := rfl

theorem norm_twistSeq (f : ℕ → ℂ) (τ : ℝ) (n : ℕ) : ‖twistSeq f τ n‖ = ‖f n‖ := by
  rw [twistSeq_apply, norm_mul, norm_charFn, mul_one]

theorem norm_twistSeq_le_one {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (τ : ℝ) (n : ℕ) :
    ‖twistSeq f τ n‖ ≤ 1 := by
  rw [norm_twistSeq]; exact hf n

theorem twistSeq_one {f : ℕ → ℂ} (hf1 : f 1 = 1) (τ : ℝ) : twistSeq f τ 1 = 1 := by
  rw [twistSeq_apply, hf1, charFn_one, mul_one]

/-- The twist inherits multiplicativity on coprime arguments. -/
theorem twistSeq_coprime_mul {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hf : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (τ : ℝ) {m n : ℕ}
    (hmn : Nat.Coprime m n) : twistSeq f τ (m * n) = twistSeq f τ m * twistSeq f τ n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hn1 : n = 1 := Nat.coprime_zero_left n |>.1 hmn
    rw [hn1, mul_one, twistSeq_one hf1, mul_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm1 : m = 1 := Nat.coprime_zero_right m |>.1 hmn
    rw [hm1, one_mul, twistSeq_one hf1, one_mul]
  rw [twistSeq_apply, twistSeq_apply, twistSeq_apply, hf hmn, charFn_mul_pos (-τ) hm hn]
  ring

/-- The pointwise form of the frequency shift. -/
theorem twistSeq_mul_conj_charFn (f : ℕ → ℂ) (τ v : ℝ) (n : ℕ) :
    twistSeq f τ n * (starRingEnd ℂ) (charFn v n)
      = f n * (starRingEnd ℂ) (charFn (τ + v) n) := by
  rw [twistSeq_apply, conj_charFn_eq, conj_charFn_eq, mul_assoc, charFn_mul_charFn,
    show -τ + -v = -(τ + v) by ring]

/-- **(Z11) The frequency shift.**  Twisting a sequence by `n^{-iτ}` translates every character
distance by `τ`. -/
theorem mulDistSqPair_twistSeq (f : ℕ → ℂ) (τ v : ℝ) (P : Finset ℕ) :
    mulDistSqPair (twistSeq f τ) (charFn v) P = mulDistSqPair f (charFn (τ + v)) P := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [twistSeq_mul_conj_charFn]

/-- The twisted pretentious distance in the notation of the deficit transfer. -/
theorem pretentiousDistSq_twistSeq (f : ℕ → ℂ) (τ v x : ℝ) :
    pretentiousDistSq (twistSeq f τ) (primeChar v) x
      = pretentiousDistSq f (primeChar (τ + v)) x :=
  mulDistSqPair_twistSeq f τ v _

/-- The Littlewood deficit share carried by every ordinary cell. -/
def littlewoodCellGap (B x : ℝ) : ℝ :=
  (Real.log (Real.log (Real.log x))
      - Real.log (37 + littlewoodFreqThreshold + 24 * B * Real.log 2)
      - zetaDeficitConst) / 4

/-- The horizon threshold forces the scale past `e⁴`. -/
theorem four_le_log_of_horizon {x : ℝ} (hx : zetaHorizonLogThreshold ≤ Real.log x) :
    4 ≤ Real.log x := by
  have hmax4 : (4 : ℝ) ≤ max 4 (4 * Real.log 69122 + 16 * Real.log 2) := le_max_left _ _
  have hexpmono := Real.exp_le_exp.mpr hmax4
  have hexp4 : (4 : ℝ) < Real.exp 4 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    linarith
  rw [zetaHorizonLogThreshold] at hx
  linarith

theorem one_le_floor_of_horizon {x : ℝ} (hx : zetaHorizonLogThreshold ≤ Real.log x)
    (hx0 : 0 < x) : 1 ≤ ⌊x⌋₊ := by
  have h4 := four_le_log_of_horizon hx
  have hx1 : (1 : ℝ) ≤ x := by
    by_contra hcon
    rcases lt_or_ge x 1 with hlt | hge
    · have := Real.log_neg hx0 hlt
      linarith
    · exact hcon hge
  exact Nat.le_floor (by exact_mod_cast hx1)

/-- **(Z12) The ordinary-cell gap.**  A real prime sequence twisted by `n^{-iτ}` stays at squared
distance at least the Littlewood cell gap from `n^{iv}`, for every cell frequency `v` whose effective
frequency `τ + v` is at least `1/2` in modulus and inside the polynomial horizon. -/
theorem littlewoodCellGap_le_mulDistSqPair_twistSeq {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1)
    {B x τ v : ℝ} (hB : 0 < B) (hx : zetaHorizonLogThreshold ≤ Real.log x) (hx0 : 0 < x)
    (hlow : 1 ≤ 2 * |τ + v|) (hhigh : 2 * |τ + v| ≤ x ^ B) :
    littlewoodCellGap B x
      ≤ mulDistSqPair (twistSeq (fun n => (r n : ℂ)) τ) (charFn v) (Nat.primesLE ⌊x⌋₊) := by
  have habs : |2 * (τ + v)| = 2 * |τ + v| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h := quarter_littlewoodDeficit_le_pretentiousDistSq (r := r) hr (B := B) (x := x)
    (α := τ + v) hB hx hx0 (by rw [habs]; exact hlow) (by rw [habs]; exact hhigh)
  rw [mulDistSqPair_twistSeq]
  exact h

/-- Away from the antitwist every frequency of the range is ordinary. -/
theorem abs_shift_ge_of_far {T τ v : ℝ} (hT : T + 1 ≤ |τ|) (hv : |v| ≤ T) : 1 ≤ |τ + v| := by
  have h1 : |τ| - |v| ≤ |τ + v| := by
    have h := abs_sub_abs_le_abs_sub τ (-v)
    rw [sub_neg_eq_add, abs_neg] at h
    linarith
  linarith

theorem abs_shift_le_of_far {T τ v : ℝ} (hv : |v| ≤ T) : |τ + v| ≤ |τ| + T :=
  le_trans (abs_add_le τ v) (by linarith)

/-- **The far-twist uniform gap.**  If the twist frequency lies beyond the whole Perron range and the
range stays inside the polynomial horizon, then every frequency of the range is an ordinary cell, so the
uniform distance hypothesis of the sharp Halász architecture holds with the Littlewood cell gap. -/
theorem sqrt_littlewoodCellGap_le_sqrt_mulDistSqPair_twistSeq {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1)
    {B x τ T : ℝ} (hB : 0 < B) (hx : zetaHorizonLogThreshold ≤ Real.log x) (hx0 : 0 < x)
    (hfar : T + 1 ≤ |τ|) (hhorizon : 2 * (|τ| + T) ≤ x ^ B) :
    ∀ v : ℝ, |v| ≤ T →
      Real.sqrt (littlewoodCellGap B x)
        ≤ Real.sqrt (mulDistSqPair (twistSeq (fun n => (r n : ℂ)) τ) (charFn v)
            (Nat.primesLE ⌊x⌋₊)) := by
  intro v hv
  refine Real.sqrt_le_sqrt ?_
  refine littlewoodCellGap_le_mulDistSqPair_twistSeq hr hB hx hx0 ?_ ?_
  · have := abs_shift_ge_of_far hfar hv
    linarith
  · have h1 : |τ + v| ≤ |τ| + T := abs_shift_le_of_far hv
    linarith

/-- **(Z12) The damped size of the twisted Dirichlet series.**  Beyond the antitwist the twisted series
is bounded on the whole Perron range by the damped Euler size at the Littlewood cell gap. -/
theorem norm_LSeries_truncSeq_twistSeq_le_damped {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1) (hr1 : r 1 = 1)
    (hrmul : ∀ {m n : ℕ}, Nat.Coprime m n → r (m * n) = r m * r n)
    {B x τ T σ : ℝ} (hB : 0 < B) (hx : zetaHorizonLogThreshold ≤ Real.log x) (hx0 : 0 < x)
    (hfar : T + 1 ≤ |τ|) (hhorizon : 2 * (|τ| + T) ≤ x ^ B) (hσ : 1 < σ)
    {L : ℕ} (hL : 1 ≤ L) {v : ℝ} (hv : |v| ≤ T) :
    ‖LSeries (truncSeq (twistSeq (fun n => (r n : ℂ)) τ) L) ((σ : ℂ) + (v : ℝ) * Complex.I)‖
      ≤ dampedSize σ (Real.sqrt (littlewoodCellGap B x)) ⌊x⌋₊ L := by
  have hf1 : ((r 1 : ℂ)) = 1 := by rw [hr1]; norm_num
  have hfmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      ((r (m * n) : ℂ)) = (r m : ℂ) * (r n : ℂ) := by
    intro m n hmn
    rw [hrmul hmn]
    push_cast
    ring
  have hbdd : ∀ n : ℕ, ‖((r n : ℂ))‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hr n
  exact norm_LSeries_truncSeq_line_le_damped (f := twistSeq (fun n => (r n : ℂ)) τ)
    (twistSeq_one hf1 τ) (fun {m n} h => twistSeq_coprime_mul hf1 (fun {a b} hab => hfmul hab) τ h)
    (norm_twistSeq_le_one hbdd τ) hσ (one_le_floor_of_horizon hx hx0) (Real.sqrt_nonneg _)
    (sqrt_littlewoodCellGap_le_sqrt_mulDistSqPair_twistSeq hr hB hx hx0 hfar hhorizon) hL hv

end

end RHTower
