import Mathlib

/-!
# Exact laws of the binary parity drift

For a real number `x` let `b_n(x) = ⌊2ⁿ x⌋ mod 2`; for `π = 11.b₁b₂…` these are the binary digits
after the point.  The parity drift of the Parity-Drift Hypothesis is
`D_x(N) = Σ_{n<N} (b_{2n+1}(x) − b_{2n+2}(x))`.

* `quatDigit_succ` : the base-4 digit `⌊4ⁿ⁺¹x⌋ mod 4` equals `2 b_{2n+1} + b_{2n+2}`.
* `drift_eq_card_sub_card` : `D_x(N)` is the number of base-4 digits `2` minus the number of
  base-4 digits `1` among the first `N` base-4 digits after the point.
* `drift_eq_alternating_sum` : `D_x(N) = Σ_{m<2N} (−1)ᵐ b_{m+1}(x)`.
* `drift_add_drift_two_mul` : `D_x(N) + D_{2x}(N) = b₁(x) − b_{2N+1}(x)` for every real `x`.
* `drift_neg` : `D_{−x} = −D_x` when no `2ⁿx` is an integer, in particular for `x = π`.
* `not_simplyNormalBaseFour_of_parityDriftHypothesis` : the hypothesis forces failure of simple
  normality in base 4.
* `exists_tendsto_drift` : every `θ ∈ [−1, 1]` is the limit of `D_x(N)/N` for some real `x`.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.BinaryParityDrift

/-- The `n`-th binary digit `⌊2ⁿ x⌋ mod 2`. -/
noncomputable def binDigit (x : ℝ) (n : ℕ) : ℤ := ⌊(2 : ℝ) ^ n * x⌋ % 2

/-- The `n`-th base-4 digit `⌊4ⁿ x⌋ mod 4`. -/
noncomputable def quatDigit (x : ℝ) (n : ℕ) : ℤ := ⌊(4 : ℝ) ^ n * x⌋ % 4

/-- The parity drift `D_x(N) = Σ_{n<N} (b_{2n+1} − b_{2n+2})`. -/
noncomputable def drift (x : ℝ) (N : ℕ) : ℤ :=
  ∑ n ∈ range N, (binDigit x (2 * n + 1) - binDigit x (2 * n + 2))

theorem binDigit_nonneg (x : ℝ) (n : ℕ) : 0 ≤ binDigit x n :=
  Int.emod_nonneg _ (by norm_num)

theorem binDigit_le_one (x : ℝ) (n : ℕ) : binDigit x n ≤ 1 := by
  have := Int.emod_lt_of_pos ⌊(2 : ℝ) ^ n * x⌋ (by norm_num : (0 : ℤ) < 2)
  unfold binDigit
  omega

/-- `⌊2y⌋` is `2⌊y⌋` or `2⌊y⌋ + 1`. -/
theorem floor_two_mul_bounds (y : ℝ) : 2 * ⌊y⌋ ≤ ⌊2 * y⌋ ∧ ⌊2 * y⌋ ≤ 2 * ⌊y⌋ + 1 := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  refine ⟨Int.le_floor.mpr (by push_cast; linarith), ?_⟩
  have h3 := Int.floor_le (2 * y)
  have h4 : (⌊2 * y⌋ : ℝ) < 2 * ⌊y⌋ + 2 := by linarith
  have h5 : ⌊2 * y⌋ < 2 * ⌊y⌋ + 2 := by exact_mod_cast h4
  omega

/-- The binary digit recursion `⌊2ⁿ⁺¹x⌋ = 2⌊2ⁿx⌋ + b_{n+1}(x)`. -/
theorem floor_two_pow_succ (x : ℝ) (n : ℕ) :
    ⌊(2 : ℝ) ^ (n + 1) * x⌋ = 2 * ⌊(2 : ℝ) ^ n * x⌋ + binDigit x (n + 1) := by
  have h := floor_two_mul_bounds ((2 : ℝ) ^ n * x)
  have he : (2 : ℝ) ^ (n + 1) * x = 2 * ((2 : ℝ) ^ n * x) := by ring
  unfold binDigit
  rw [he]
  omega

/-- The base-4 recursion `⌊4ⁿ⁺¹x⌋ = 4⌊4ⁿx⌋ + 2b_{2n+1} + b_{2n+2}`. -/
theorem floor_four_pow_succ (x : ℝ) (n : ℕ) :
    ⌊(4 : ℝ) ^ (n + 1) * x⌋ =
      4 * ⌊(4 : ℝ) ^ n * x⌋ + (2 * binDigit x (2 * n + 1) + binDigit x (2 * n + 2)) := by
  have h4 : ∀ m : ℕ, (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * m) := fun m => by
    rw [pow_mul]; norm_num
  have e1 := floor_two_pow_succ x (2 * n + 1)
  have e0 := floor_two_pow_succ x (2 * n)
  rw [h4, h4, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, e1, e0]
  ring

/-- **Base-4 law.** The `(n+1)`-th base-4 digit is `2 b_{2n+1} + b_{2n+2}`. -/
theorem quatDigit_succ (x : ℝ) (n : ℕ) :
    quatDigit x (n + 1) = 2 * binDigit x (2 * n + 1) + binDigit x (2 * n + 2) := by
  have := binDigit_nonneg x (2 * n + 1)
  have := binDigit_le_one x (2 * n + 1)
  have := binDigit_nonneg x (2 * n + 2)
  have := binDigit_le_one x (2 * n + 2)
  unfold quatDigit
  rw [floor_four_pow_succ]
  omega

theorem binDigit_sub_binDigit_eq (x : ℝ) (n : ℕ) :
    binDigit x (2 * n + 1) - binDigit x (2 * n + 2) =
      (if quatDigit x (n + 1) = 2 then 1 else 0) - (if quatDigit x (n + 1) = 1 then 1 else 0) := by
  rw [quatDigit_succ]
  have := binDigit_nonneg x (2 * n + 1)
  have := binDigit_le_one x (2 * n + 1)
  have := binDigit_nonneg x (2 * n + 2)
  have := binDigit_le_one x (2 * n + 2)
  split_ifs <;> omega

/-- **Counting law.** The parity drift counts base-4 digits `2` minus base-4 digits `1`. -/
theorem drift_eq_card_sub_card (x : ℝ) (N : ℕ) :
    drift x N = (#{n ∈ range N | quatDigit x (n + 1) = 2} : ℤ) -
      #{n ∈ range N | quatDigit x (n + 1) = 1} := by
  unfold drift
  simp_rw [binDigit_sub_binDigit_eq, sum_sub_distrib, sum_boole]

/-- **Alternating-sum law.** `D_x(N) = Σ_{m<2N} (−1)ᵐ b_{m+1}(x)`. -/
theorem drift_eq_alternating_sum (x : ℝ) (N : ℕ) :
    drift x N = ∑ m ∈ range (2 * N), (-1) ^ m * binDigit x (m + 1) := by
  induction N with
  | zero => simp [drift]
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ← ih, drift,
      sum_range_succ, ← drift]
    rw [pow_succ, pow_mul]
    norm_num
    ring

theorem binDigit_two_mul (x : ℝ) (n : ℕ) : binDigit (2 * x) n = binDigit x (n + 1) := by
  unfold binDigit
  congr 2
  ring

/-- **Doubling law.** `D_x(N) + D_{2x}(N) = b₁(x) − b_{2N+1}(x)`. -/
theorem drift_add_drift_two_mul (x : ℝ) (N : ℕ) :
    drift x N + drift (2 * x) N = binDigit x 1 - binDigit x (2 * N + 1) := by
  unfold drift
  rw [← sum_add_distrib]
  have h := sum_range_sub' (fun n => binDigit x (2 * n + 1)) N
  simp only [mul_zero, zero_add] at h
  rw [← h]
  refine sum_congr rfl fun n _ => ?_
  rw [binDigit_two_mul, binDigit_two_mul, show 2 * n + 1 + 1 = 2 * n + 2 by ring,
    show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring]
  ring

theorem abs_binDigit_sub_le (x : ℝ) (m n : ℕ) : |((binDigit x m - binDigit x n : ℤ) : ℝ)| ≤ 1 := by
  have := binDigit_nonneg x m
  have := binDigit_le_one x m
  have := binDigit_nonneg x n
  have := binDigit_le_one x n
  have h : |binDigit x m - binDigit x n| ≤ 1 := abs_le.mpr ⟨by omega, by omega⟩
  exact_mod_cast h

/-- A bounded integer sequence divided by `N` tends to zero. -/
theorem tendsto_bounded_div {e : ℕ → ℤ} (he : ∀ N, |(e N : ℝ)| ≤ 1) :
    Tendsto (fun N : ℕ => (e N : ℝ) / N) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) tendsto_one_div_atTop_nhds_zero_nat
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (he N) (Nat.cast_nonneg N)

/-- If `u N + v N` stays in `[−1, 1]` and `u N / N → θ`, then `v N / N → −θ`. -/
theorem tendsto_neg_of_add_bounded {u v : ℕ → ℤ} {θ : ℝ}
    (huv : ∀ N, |((u N + v N : ℤ) : ℝ)| ≤ 1)
    (hu : Tendsto (fun N : ℕ => (u N : ℝ) / N) atTop (𝓝 θ)) :
    Tendsto (fun N : ℕ => (v N : ℝ) / N) atTop (𝓝 (-θ)) := by
  have h := hu.neg.add (tendsto_bounded_div huv)
  rw [add_zero] at h
  refine h.congr fun N => ?_
  push_cast
  ring

/-- Doubling reverses the asymptotic drift. -/
theorem tendsto_drift_two_mul {x θ : ℝ}
    (h : Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 θ)) :
    Tendsto (fun N : ℕ => (drift (2 * x) N : ℝ) / N) atTop (𝓝 (-θ)) :=
  tendsto_neg_of_add_bounded
    (fun N => by rw [drift_add_drift_two_mul]; exact abs_binDigit_sub_le ..) h

theorem tendsto_drift_of_two_mul {x θ : ℝ}
    (h : Tendsto (fun N : ℕ => (drift (2 * x) N : ℝ) / N) atTop (𝓝 θ)) :
    Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 (-θ)) :=
  tendsto_neg_of_add_bounded
    (fun N => by rw [add_comm, drift_add_drift_two_mul]; exact abs_binDigit_sub_le ..) h

/-- `⌊−y⌋ = −⌊y⌋ − 1` off the integers. -/
theorem floor_neg_of_ne_int {y : ℝ} (hy : ∀ m : ℤ, y ≠ m) : ⌊-y⌋ = -⌊y⌋ - 1 := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  have h3 : (⌊y⌋ : ℝ) < y := lt_of_le_of_ne h1 fun h => hy _ h.symm
  rw [Int.floor_eq_iff]
  push_cast
  constructor <;> linarith

theorem binDigit_neg {x : ℝ} {n : ℕ} (hx : ∀ m : ℤ, (2 : ℝ) ^ n * x ≠ m) :
    binDigit (-x) n = 1 - binDigit x n := by
  unfold binDigit
  rw [mul_neg, floor_neg_of_ne_int hx]
  omega

/-- **Reflection law.** Off the dyadic rationals, `D_{−x} = −D_x`. -/
theorem drift_neg {x : ℝ} (hx : ∀ (n : ℕ) (m : ℤ), (2 : ℝ) ^ n * x ≠ m) (N : ℕ) :
    drift (-x) N = -drift x N := by
  unfold drift
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [binDigit_neg (hx _), binDigit_neg (hx _)]
  ring

theorem two_pow_mul_pi_ne_int (n : ℕ) (m : ℤ) : (2 : ℝ) ^ n * Real.pi ≠ m := by
  have h : Irrational (((2 : ℚ) ^ n : ℚ) * Real.pi) :=
    irrational_pi.ratCast_mul (by positivity)
  push_cast at h
  exact h.ne_int m

/-- The parity drift of `−π` is the negative of that of `π`. -/
theorem drift_neg_pi (N : ℕ) : drift (-Real.pi) N = -drift Real.pi N :=
  drift_neg two_pow_mul_pi_ne_int N

/-- The Parity-Drift Hypothesis for `x`: `D_x(N)/N` does not tend to `0`. -/
def ParityDriftHypothesis (x : ℝ) : Prop :=
  ¬ Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 0)

/-- The hypothesis is the statement `limsup |D_x(N)|/N > 0`. -/
theorem parityDriftHypothesis_iff (x : ℝ) :
    ParityDriftHypothesis x ↔ ∃ ε > 0, ∃ᶠ N in atTop, ε ≤ |(drift x N : ℝ)| / N := by
  unfold ParityDriftHypothesis
  rw [Metric.tendsto_nhds]
  simp only [not_forall, not_eventually, not_lt, exists_prop]
  refine exists_congr fun ε => and_congr_right fun _ => ?_
  refine frequently_congr (Eventually.of_forall fun N => ?_)
  rw [Real.dist_eq, sub_zero, abs_div, Nat.abs_cast]

/-- The strong form: `p_odd(N) → 1/2 + δ` and `p_even(N) → 1/2 − δ` with `δ ≠ 0`. -/
def StrongParityDriftHypothesis (x : ℝ) : Prop :=
  ∃ δ : ℝ, δ ≠ 0 ∧
    Tendsto (fun N : ℕ => (∑ n ∈ range N, binDigit x (2 * n + 1) : ℝ) / N) atTop
        (𝓝 (1 / 2 + δ)) ∧
    Tendsto (fun N : ℕ => (∑ n ∈ range N, binDigit x (2 * n + 2) : ℝ) / N) atTop
        (𝓝 (1 / 2 - δ))

theorem parityDriftHypothesis_of_strong {x : ℝ} (h : StrongParityDriftHypothesis x) :
    ParityDriftHypothesis x := by
  obtain ⟨δ, hδ, ho, he⟩ := h
  have hd : Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 (2 * δ)) := by
    have := ho.sub he
    rw [show 1 / 2 + δ - (1 / 2 - δ) = 2 * δ by ring] at this
    refine this.congr fun N => ?_
    simp only [drift, sum_sub_distrib]
    push_cast
    ring
  intro h0
  exact hδ (by linarith [tendsto_nhds_unique hd h0])

/-- Simple normality in base 4, read from the base-4 digits after the point. -/
def SimplyNormalBaseFour (x : ℝ) : Prop :=
  ∀ d : ℤ, 0 ≤ d → d < 4 →
    Tendsto (fun N : ℕ => (#{n ∈ range N | quatDigit x (n + 1) = d} : ℝ) / N) atTop (𝓝 (1 / 4))

theorem tendsto_drift_of_simplyNormalBaseFour {x : ℝ} (hx : SimplyNormalBaseFour x) :
    Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 0) := by
  have h := (hx 2 (by norm_num) (by norm_num)).sub (hx 1 (by norm_num) (by norm_num))
  rw [sub_self] at h
  refine h.congr fun N => ?_
  rw [drift_eq_card_sub_card]
  push_cast
  ring

/-- **The hypothesis refutes simple normality in base 4.** -/
theorem not_simplyNormalBaseFour_of_parityDriftHypothesis {x : ℝ}
    (h : ParityDriftHypothesis x) : ¬ SimplyNormalBaseFour x :=
  fun hn => h (tendsto_drift_of_simplyNormalBaseFour hn)

/-- The hypothesis is invariant under doubling. -/
theorem parityDriftHypothesis_two_mul_iff (x : ℝ) :
    ParityDriftHypothesis (2 * x) ↔ ParityDriftHypothesis x := by
  unfold ParityDriftHypothesis
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · simpa using tendsto_drift_of_two_mul h
  · simpa using tendsto_drift_two_mul h

/-! ### Realisation of every drift value -/

/-- The integer formed by the first `n` base-4 digits of a digit sequence. -/
def digitPrefix (d : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => 4 * digitPrefix d n + d n

/-- The real number `Σ dₙ 4^{−(n+1)}`. -/
noncomputable def ofQuatDigits (d : ℕ → ℤ) : ℝ := ∑' n, (d n : ℝ) / 4 ^ (n + 1)

theorem floor_four_pow_mul_ofQuatDigits {d : ℕ → ℤ} (h0 : ∀ n, 0 ≤ d n) (h2 : ∀ n, d n ≤ 2)
    (n : ℕ) : ⌊(4 : ℝ) ^ n * ofQuatDigits d⌋ = digitPrefix d n := by
  set f : ℕ → ℝ := fun k => (d k : ℝ) / 4 ^ (k + 1) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => div_nonneg (by exact_mod_cast h0 k) (by positivity)
  have hfle : ∀ k, f k ≤ 1 / 2 * (1 / 4 : ℝ) ^ k := fun k => by
    have hk : (d k : ℝ) ≤ 2 := by exact_mod_cast h2 k
    simp only [hf, one_div, inv_pow]
    rw [div_le_iff₀ (by positivity), pow_succ]
    field_simp
    linarith
  have hg : Summable fun k : ℕ => 1 / 2 * (1 / 4 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hfle hg
  have hpre : ∀ m, ∑ k ∈ range m, f k = (digitPrefix d m : ℝ) / 4 ^ m := by
    intro m
    induction m with
    | zero => simp [digitPrefix]
    | succ m ih =>
      rw [sum_range_succ, ih]
      simp only [hf, digitPrefix]
      push_cast
      field_simp
      ring
  have htail0 : 0 ≤ ∑' k, f (k + n) := tsum_nonneg fun k => hf0 _
  have htail1 : ∑' k, f (k + n) ≤ 2 / 3 / 4 ^ n := by
    have hle : ∑' k, f (k + n) ≤ ∑' k : ℕ, (1 / 2 * (1 / 4 : ℝ) ^ n) * (1 / 4 : ℝ) ^ k := by
      refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff n).mpr hs)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
      have := hfle (k + n)
      rw [pow_add] at this
      linarith
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hle
    refine hle.trans (le_of_eq ?_)
    rw [one_div_pow]
    field_simp
    norm_num
  have hsplit := hs.sum_add_tsum_nat_add n
  have hx : ofQuatDigits d = (digitPrefix d n : ℝ) / 4 ^ n + ∑' k, f (k + n) := by
    rw [← hpre, hsplit]
    rfl
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  rw [Int.floor_eq_iff, hx, mul_add, mul_div_cancel₀ _ h4.ne']
  have hb : (4 : ℝ) ^ n * ∑' k, f (k + n) ≤ 2 / 3 := by
    calc (4 : ℝ) ^ n * ∑' k, f (k + n) ≤ 4 ^ n * (2 / 3 / 4 ^ n) :=
          mul_le_mul_of_nonneg_left htail1 h4.le
      _ = 2 / 3 := by field_simp
  constructor <;> nlinarith [mul_nonneg h4.le htail0]

theorem quatDigit_ofQuatDigits {d : ℕ → ℤ} (h0 : ∀ n, 0 ≤ d n) (h2 : ∀ n, d n ≤ 2) (n : ℕ) :
    quatDigit (ofQuatDigits d) (n + 1) = d n := by
  unfold quatDigit
  rw [floor_four_pow_mul_ofQuatDigits h0 h2, digitPrefix]
  have := h0 n
  have := h2 n
  omega

/-- Base-4 digits `2·(⌊(n+1)θ⌋ − ⌊nθ⌋) ∈ {0, 2}`, a Sturmian placement of digits `2`. -/
noncomputable def sturmDigit (θ : ℝ) (n : ℕ) : ℤ := 2 * (⌊((n : ℝ) + 1) * θ⌋ - ⌊(n : ℝ) * θ⌋)

theorem floor_step_bounds {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (n : ℕ) :
    0 ≤ ⌊((n : ℝ) + 1) * θ⌋ - ⌊(n : ℝ) * θ⌋ ∧ ⌊((n : ℝ) + 1) * θ⌋ - ⌊(n : ℝ) * θ⌋ ≤ 1 := by
  have hmono : ⌊(n : ℝ) * θ⌋ ≤ ⌊((n : ℝ) + 1) * θ⌋ := Int.floor_mono (by nlinarith)
  have ha := Int.floor_le (((n : ℝ) + 1) * θ)
  have hb := Int.lt_floor_add_one ((n : ℝ) * θ)
  have hc : (⌊((n : ℝ) + 1) * θ⌋ : ℝ) < ⌊(n : ℝ) * θ⌋ + 2 := by nlinarith
  have hd : ⌊((n : ℝ) + 1) * θ⌋ < ⌊(n : ℝ) * θ⌋ + 2 := by exact_mod_cast hc
  constructor <;> omega

theorem drift_ofQuatDigits_sturmDigit {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (N : ℕ) :
    drift (ofQuatDigits (sturmDigit θ)) N = ⌊(N : ℝ) * θ⌋ := by
  have hd0 : ∀ n, 0 ≤ sturmDigit θ n := fun n => by
    have := floor_step_bounds h0 h1 n; unfold sturmDigit; omega
  have hd2 : ∀ n, sturmDigit θ n ≤ 2 := fun n => by
    have := floor_step_bounds h0 h1 n; unfold sturmDigit; omega
  unfold drift
  have h := sum_range_sub (fun n : ℕ => ⌊(n : ℝ) * θ⌋) N
  simp only [Nat.cast_zero, zero_mul, Int.floor_zero, sub_zero, Nat.cast_succ] at h
  rw [← h]
  refine sum_congr rfl fun n _ => ?_
  rw [binDigit_sub_binDigit_eq, quatDigit_ofQuatDigits hd0 hd2]
  have := floor_step_bounds h0 h1 n
  unfold sturmDigit
  split_ifs <;> omega

theorem tendsto_floor_mul_div {θ : ℝ} :
    Tendsto (fun N : ℕ => (⌊(N : ℝ) * θ⌋ : ℝ) / N) atTop (𝓝 θ) := by
  have hlow : Tendsto (fun N : ℕ => θ - 1 / (N : ℝ)) atTop (𝓝 θ) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [le_div_iff₀ hN', sub_mul, one_div, inv_mul_cancel₀ hN'.ne']
    linarith [Int.lt_floor_add_one ((N : ℝ) * θ)]
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hN']
    linarith [Int.floor_le ((N : ℝ) * θ)]

/-- **Realisation.** Every `θ ∈ [−1, 1]` is the asymptotic parity drift of some real number. -/
theorem exists_tendsto_drift {θ : ℝ} (hθ : θ ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ x : ℝ, Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 θ) := by
  rcases le_total 0 θ with h | h
  · refine ⟨ofQuatDigits (sturmDigit θ), ?_⟩
    simp_rw [drift_ofQuatDigits_sturmDigit h hθ.2]
    exact tendsto_floor_mul_div
  · refine ⟨2 * ofQuatDigits (sturmDigit (-θ)), ?_⟩
    have hm : Tendsto (fun N : ℕ => (drift (ofQuatDigits (sturmDigit (-θ))) N : ℝ) / N) atTop
        (𝓝 (-θ)) := by
      simp_rw [drift_ofQuatDigits_sturmDigit (neg_nonneg.mpr h) (by linarith [hθ.1])]
      exact tendsto_floor_mul_div
    simpa using tendsto_drift_two_mul hm

end GaloisForLFunctions.HTGeometry.BinaryParityDrift
