import GaloisForLFunctions.TransHorizonIncidenceMechanics.HorizonLawOfPositiveRows
import GaloisForLFunctions.TransHorizonIncidenceMechanics.HalfDampingIsTheExactThresholdOfTheParityPair

/-!
# The horizon limit commutes with the receiver exactly from half damping on

For a weight `c` let `c_J = c · 1_{d ≤ 2^J}` be its dyadic rows, each centred at its own finite mean.
For nonnegative weights the rows have uniformly bounded receivers iff the weight is paid
(`rows_uniformly_bounded_iff`). For signed weights of the damped class `𝒞(K, ε)`:

* **Bounded rows always pay the limit.** At a fixed cutoff the receiver energy is a finite
  expression, continuous in the weight and the mean.
* **From half damping on the converse holds.** Below the horizon `N` a row is the weight plus the
  drift `τ_N n`, `τ_N = Σ_{d>N} c(d)/d`, and `N τ_N² ≤ 4K²`; beyond it the row is the sawtooth sum
  `−Σ_{d≤N} c(d){n/d}`, bounded by `Σ_{d≤N}|c(d)| ≤ 3K√N`, whose pronic tail is `≤ 9K²`. So the rows
  are uniformly paid exactly when the weight is (`rows_bounded_iff_receiverBounded_of_half_le`).
* **Below half damping the converse fails inside the class.** For every `0 ≤ ε < 1/2` an explicit
  weight `c ∈ 𝒞(1, ε)` with `Σ c(d)/d = 0` is paid while its dyadic rows have unbounded receivers
  (`exists_paid_weight_with_unbounded_rows`).

Hence commutation on `𝒞(1, ε)` holds iff `ε ≥ 1/2` (`horizonLimit_commutes_with_receiver_iff`): the
threshold of the parity barrier is also the threshold at which finite horizons faithfully report the
receiver.

The witness is a lacunary superposition of *windowed dipoles*
`b(d) = α d` on `(N, N+w]`, `b(d) = −α d` on `(N−w, N]`. A dipole has harmonic mass zero, so beyond its
support its prefix is a bounded sawtooth sum; and by the hyperbola swap
`Σ_d b(d)⌊n/d⌋ = Σ_k S(⌊n/k⌋)` (`S` the plain partial sums of `b`) its prefix below the cut `X` is at
most `P⌊n/(N+w)⌋ + sup|S|·D(n)`, where `P = αw²` and `D(n) ≤ 1` counts the `k` with `⌊n/k⌋` inside
the window. The row whose horizon `N` splits the dipole keeps only the negative half: its mean is
`−αw`, so its prefix carries the drift `αw·n` on all of `[1, N]` and its energy is at least
`α²w²N/4` minus the paid energy of the weight. With `N = 2^{Lt}`, `w = 2^{Mt}`, `X = 2^{Qt}` the drift
energy grows like `2^{(2M − (1+2ε)L)t}` while the dipoles' own energies are summable; the exponents
exist exactly when `ε < 1/2`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Bounded rows pay the limit -/

/-- The finite mean of the dyadic row of horizon `2^J`. -/
def dyadicRowMean (c : ℕ → ℝ) (J : ℕ) : ℝ := ∑ d ∈ Icc 1 (2 ^ J), dyadicRow c J d / d

theorem dyadicRowMean_eq (c : ℕ → ℝ) (J : ℕ) :
    dyadicRowMean c J = ∑ d ∈ Icc 1 (2 ^ J), c d / d :=
  sum_congr rfl fun d hd => by simp [dyadicRow, (mem_Icc.mp hd).2]

theorem sum_range_succ_eq_sum_Icc_one {f : ℕ → ℝ} (h0 : f 0 = 0) (n : ℕ) :
    ∑ d ∈ range (n + 1), f d = ∑ d ∈ Icc 1 n, f d := by
  symm
  refine sum_subset (fun d hd => ?_) fun d hd hd' => ?_
  · simp only [mem_Icc, mem_range] at hd ⊢; omega
  · simp only [mem_Icc, mem_range, not_and, not_le] at hd hd'
    obtain rfl : d = 0 := by by_contra h; exact absurd (hd' (by omega)) (by omega)
    exact h0

theorem tendsto_dyadicRowMean {c : ℕ → ℝ} {m : ℝ} (hm : HasSum (fun d : ℕ => c d / d) m) :
    Tendsto (dyadicRowMean c) atTop (𝓝 m) := by
  have hJ : Tendsto (fun J : ℕ => 2 ^ J + 1) atTop atTop :=
    tendsto_atTop_mono (fun J => (Nat.lt_two_pow_self (n := J)).le.trans (Nat.le_succ _)) tendsto_id
  refine (hm.tendsto_sum_nat.comp hJ).congr fun J => ?_
  simp only [Function.comp_apply, dyadicRowMean_eq]
  exact sum_range_succ_eq_sum_Icc_one (by simp) _

/-- The receiver energy at a fixed cutoff is continuous in the weight and the mean. -/
theorem tendsto_weightPronicEnergy_of_tendsto {c : ℕ → ℕ → ℝ} {c₀ : ℕ → ℝ} {m : ℕ → ℝ} {m₀ : ℝ}
    (hc : ∀ d, Tendsto (fun J => c J d) atTop (𝓝 (c₀ d))) (hm : Tendsto m atTop (𝓝 m₀))
    (T : ℕ) :
    Tendsto (fun J => weightPronicEnergy (c J) (m J) T) atTop
      (𝓝 (weightPronicEnergy c₀ m₀ T)) := by
  unfold weightPronicEnergy weightCenteredPrefix
  refine tendsto_finsetSum _ fun n _ => ?_
  refine Tendsto.div_const (Tendsto.pow (Tendsto.sub ?_ (hm.mul_const _)) 2) _
  exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun d _ => hc d

theorem tendsto_dyadicRow (c : ℕ → ℝ) (d : ℕ) :
    Tendsto (fun J => dyadicRow c J d) atTop (𝓝 (c d)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop d] with J hJ
  have : d ≤ 2 ^ J := hJ.trans (Nat.lt_two_pow_self).le
  simp [dyadicRow, this]

/-- **Uniformly bounded rows pay the limit**, for every signed weight with a mean. -/
theorem weightPronicEnergy_le_of_rows_le {c : ℕ → ℝ} {m : ℝ}
    (hm : HasSum (fun d : ℕ => c d / d) m) {E : ℝ}
    (hE : ∀ J T : ℕ, weightPronicEnergy (dyadicRow c J) (dyadicRowMean c J) T ≤ E) (T : ℕ) :
    weightPronicEnergy c m T ≤ E :=
  le_of_tendsto' (tendsto_weightPronicEnergy_of_tendsto (tendsto_dyadicRow c)
    (tendsto_dyadicRowMean hm) T) fun J => hE J T

/-! ### Above half damping the rows are paid uniformly -/

theorem dampedClass_dyadicRow {K ε : ℝ} {c : ℕ → ℝ} (hc : DampedClass K ε c) (J : ℕ) :
    DampedClass K ε (dyadicRow c J) := fun d => by
  unfold dyadicRow
  split_ifs
  · exact hc d
  · simpa using (abs_nonneg _).trans (hc d)

theorem tsum_dyadicRow_div (c : ℕ → ℝ) (J : ℕ) :
    ∑' d : ℕ, dyadicRow c J d / d = dyadicRowMean c J :=
  (hasSum_dyadicRow_div c J).tsum_eq

/-- **Above half damping** every weight of `𝒞(K, ε)` and all of its rows are paid by one
constant: the horizon limit commutes with the receiver on the whole class. -/
theorem exists_uniform_rowEnergy_bound {K ε : ℝ} (hε : 1 / 2 < ε) :
    ∃ E : ℝ, ∀ c : ℕ → ℝ, DampedClass K ε c →
      (∀ T : ℕ, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) ∧
      ∀ J T : ℕ, weightPronicEnergy (dyadicRow c J) (dyadicRowMean c J) T ≤ E := by
  obtain ⟨E, hE⟩ := exists_uniform_weightPronicEnergy_bound (K := K) hε
  refine ⟨E, fun c hc => ⟨hE c hc, fun J T => ?_⟩⟩
  have h := hE _ (dampedClass_dyadicRow hc J) T
  rwa [tsum_dyadicRow_div] at h

/-! ### At half damping the rows are paid exactly when the weight is -/

/-- The pronic tail mass `Σ_{X ≤ n ≤ T} 1/(n(n+1)) = 1/X − 1/(T+1)`. -/
theorem sum_Icc_pronic_tail_eq {X : ℕ} (hX : 1 ≤ X) {T : ℕ} (hT : X ≤ T + 1) :
    ∑ n ∈ Icc X T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) = 1 / (X : ℝ) - 1 / ((T : ℝ) + 1) := by
  induction T with
  | zero =>
    obtain rfl : X = 1 := by omega
    simp
  | succ T ih =>
    rcases Nat.eq_or_lt_of_le hT with h | h
    · rw [Icc_eq_empty (by omega), sum_empty, h]
      push_cast
      ring
    · rw [sum_Icc_succ_top (by omega), ih (by omega)]
      have h1 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
      push_cast
      field_simp
      ring

theorem sum_Icc_pronic_tail_le {X : ℕ} (hX : 1 ≤ X) (T : ℕ) :
    ∑ n ∈ Icc X T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ 1 / (X : ℝ) := by
  rcases le_or_gt X (T + 1) with hT | hT
  · rw [sum_Icc_pronic_tail_eq hX hT]
    have : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
    linarith
  · rw [Icc_eq_empty (by omega), sum_empty]
    positivity

/-- The harmonic tail of a half-damped weight: `|Σ_{d>N} c(d)/d| ≤ 2K N^{-1/2}`. -/
theorem abs_tail_le_of_half {K : ℝ} {c : ℕ → ℝ} (hc : DampedClass K (1 / 2) c) {N : ℕ}
    (hN : 1 ≤ N) :
    |∑' k : ℕ, c (k + (N + 1)) / ((k + (N + 1) : ℕ) : ℝ)| ≤ K * ((N : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2)) := by
  have hK := nonneg_of_dampedClass hc
  have hbound : ∀ k : ℕ, ‖c (k + (N + 1)) / ((k + (N + 1) : ℕ) : ℝ)‖ ≤
      K * ((N : ℝ) + 1 + k) ^ (-(1 / 2 : ℝ) - 1) := by
    intro k
    have hcast : ((k + (N + 1) : ℕ) : ℝ) = (N : ℝ) + 1 + k := by push_cast; ring
    have hpos : (0 : ℝ) < (N : ℝ) + 1 + k := by positivity
    rw [Real.norm_eq_abs, abs_div, hcast, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |c (k + (N + 1))| ≤ K * (((k + (N + 1) : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) := hc _
      _ = K * ((N : ℝ) + 1 + k) ^ (-(1 / 2 : ℝ) - 1) * ((N : ℝ) + 1 + k) := by
        rw [hcast, mul_assoc, ← Real.rpow_add_one hpos.ne',
          show -(1 / 2 : ℝ) - 1 + 1 = -(1 / 2) by ring]
  have hsum := (HTGeometry.summable_shift_rpow (q := -(1 / 2 : ℝ)) (by norm_num) N).mul_left K
  calc _ ≤ ∑' k : ℕ, K * ((N : ℝ) + 1 + k) ^ (-(1 / 2 : ℝ) - 1) :=
        tsum_of_norm_bounded hsum.hasSum hbound
    _ = K * ∑' k : ℕ, ((N : ℝ) + 1 + k) ^ (-(1 / 2 : ℝ) - 1) := tsum_mul_left
    _ ≤ K * ((N : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        have h := HTGeometry.tsum_shift_rpow_le (q := -(1 / 2 : ℝ)) (by norm_num) hN
        rwa [neg_neg] at h

/-- **At half damping a paid weight has uniformly paid rows.** Below the horizon `N` the row is the
weight plus the drift `τ_N n` with `N τ_N² ≤ 4K²`; beyond it the row is a sawtooth sum bounded by
`Σ_{d ≤ N} |c(d)| ≤ 3K√N`, whose pronic tail is at most `9K²`. -/
theorem rowEnergy_le_of_half {K : ℝ} {c : ℕ → ℝ} (hc : DampedClass K (1 / 2) c) {E : ℝ}
    (hE : ∀ T : ℕ, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) (J T : ℕ) :
    weightPronicEnergy (dyadicRow c J) (dyadicRowMean c J) T ≤ 2 * E + 17 * K ^ 2 := by
  have hK := nonneg_of_dampedClass hc
  have hs : Summable (fun d : ℕ => c d / d) := summable_div_of_dampedClass (by norm_num) hc
  set N := 2 ^ J with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set m := ∑' d : ℕ, c d / d with hmdef
  set τ := m - dyadicRowMean c J with hτdef
  -- the drift of the row
  have hτeq : τ = ∑' k : ℕ, c (k + (N + 1)) / ((k + (N + 1) : ℕ) : ℝ) := by
    rw [hτdef, hmdef, ← hs.sum_add_tsum_nat_add (N + 1),
      sum_range_succ_eq_sum_Icc_one (f := fun d => c d / d) (by simp), dyadicRowMean_eq]
    ring
  have hτ2 : τ ^ 2 * N ≤ 4 * K ^ 2 := by
    have h := abs_tail_le_of_half hc hN1
    rw [← hτeq] at h
    have hsq : τ ^ 2 ≤ (K * ((N : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hpow : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * N = 1 := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hN0.le]
      norm_num
      rw [Real.rpow_neg_one, inv_mul_cancel₀ hN0.ne']
    calc τ ^ 2 * N ≤ (K * ((N : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2))) ^ 2 * N := by gcongr
      _ = 4 * K ^ 2 * (((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * N) := by ring
      _ = 4 * K ^ 2 := by rw [hpow, mul_one]
  -- the sawtooth bound beyond the horizon
  have hhead : (∑ d ∈ Icc 1 N, |c d|) ^ 2 ≤ 9 * K ^ 2 * N := by
    have h1 : ∑ d ∈ Icc 1 N, |c d| ≤ K * (1 + (N : ℝ) ^ (1 - 1 / 2 : ℝ) / (1 - 1 / 2)) :=
      (sum_le_sum fun d _ => hc d).trans (by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (RHTower.sum_rpow_neg_head_le (by norm_num) (by norm_num) N) hK)
    have hsqrt : ((N : ℝ) ^ (1 - 1 / 2 : ℝ)) ^ 2 = N := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (1 - 1 / 2 : ℝ)) 2, ← Real.rpow_mul hN0.le]
      norm_num
    have hge : (1 : ℝ) ≤ (N : ℝ) ^ (1 - 1 / 2 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    have h0 : 0 ≤ ∑ d ∈ Icc 1 N, |c d| := sum_nonneg fun _ _ => abs_nonneg _
    calc (∑ d ∈ Icc 1 N, |c d|) ^ 2 ≤ (K * (1 + (N : ℝ) ^ (1 - 1 / 2 : ℝ) / (1 - 1 / 2))) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ ≤ (K * (3 * (N : ℝ) ^ (1 - 1 / 2 : ℝ))) ^ 2 := by
          gcongr
          norm_num
          linarith
      _ = 9 * K ^ 2 * N := by rw [mul_pow, mul_pow, hsqrt]; ring
  have hrow : ∀ n : ℕ, weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n =
      ∑ d ∈ Icc 1 n, dyadicRow c J d * ((n / d : ℕ) : ℝ) - dyadicRowMean c J * n := by
    intro n; rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
  have hlow : ∀ n ∈ (Icc 1 T).filter (· ≤ N),
      weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        2 * (weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) + 2 * τ ^ 2 := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
    have hp : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    have heq : weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n =
        weightCenteredPrefix c m n + τ * n := by
      rw [hrow, weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hτdef]
      have : ∑ d ∈ Icc 1 n, dyadicRow c J d * ((n / d : ℕ) : ℝ) =
          ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) := sum_congr rfl fun d hd => by
        have : d ≤ 2 ^ J := (mem_Icc.mp hd).2.trans hn.2
        simp [dyadicRow, this]
      rw [this]; ring
    rw [heq, div_le_iff₀ hp]
    have hfrac : 2 * (weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) *
        ((n : ℝ) * ((n : ℝ) + 1)) = 2 * weightCenteredPrefix c m n ^ 2 := by
      field_simp
    nlinarith [sq_nonneg (weightCenteredPrefix c m n - τ * n), sq_nonneg τ]
  have hhigh : ∀ n ∈ (Icc 1 T).filter (fun n => ¬ n ≤ N),
      weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        9 * K ^ 2 * N * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    intro n hn
    simp only [mem_filter, mem_Icc, not_le] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
    have heq : weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n =
        ∑ d ∈ Icc 1 N, c d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d) := by
      rw [hrow, dyadicRowMean_eq]
      have hsplit : Icc 1 n = Icc 1 N ∪ Ioc N n := by
        ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
      have hdisj : Disjoint (Icc 1 N) (Ioc N n) := by
        rw [disjoint_left]; intro d h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
      rw [hsplit, sum_union hdisj]
      have hz : ∑ d ∈ Ioc N n, dyadicRow c J d * ((n / d : ℕ) : ℝ) = 0 :=
        sum_eq_zero fun d hd => by
          have : ¬ d ≤ 2 ^ J := by simp only [mem_Ioc] at hd; omega
          simp [dyadicRow, this]
      have hc' : ∑ d ∈ Icc 1 N, dyadicRow c J d * ((n / d : ℕ) : ℝ) =
          ∑ d ∈ Icc 1 N, c d * ((n / d : ℕ) : ℝ) := sum_congr rfl fun d hd => by
        have : d ≤ 2 ^ J := (mem_Icc.mp hd).2
        simp [dyadicRow, this]
      rw [hz, add_zero, hc', sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun d _ => ?_
      ring
    have habs : |weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n| ≤ ∑ d ∈ Icc 1 N, |c d| := by
      rw [heq]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
      rw [abs_mul]
      calc |c d| * |((n / d : ℕ) : ℝ) - (n : ℝ) / d| ≤ |c d| * 1 :=
            mul_le_mul_of_nonneg_left (abs_natDiv_sub_div_le n d (mem_Icc.mp hd).1) (abs_nonneg _)
        _ = |c d| := mul_one _
    have hsq : weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n ^ 2 ≤ 9 * K ^ 2 * N := by
      refine le_trans ?_ hhead
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [mul_one_div]
    gcongr
  rw [weightPronicEnergy, ← sum_filter_add_sum_filter_not (Icc 1 T) (· ≤ N)]
  have hA : ∑ n ∈ (Icc 1 T).filter (· ≤ N), (weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
      ≤ E := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n hn _ => ?_) (hE T)
    have : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    positivity
  have hcard : (((Icc 1 T).filter (· ≤ N)).card : ℝ) ≤ N := by
    have : (Icc 1 T).filter (· ≤ N) ⊆ Icc 1 N := fun n hn => by
      simp only [mem_filter, mem_Icc] at hn ⊢; exact ⟨hn.1.1, hn.2⟩
    have h := card_le_card this
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact_mod_cast h
  have htail : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n ≤ N), 1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      1 / ((N : ℝ) + 1) := by
    have hfil : (Icc 1 T).filter (fun n => ¬ n ≤ N) = Icc (N + 1) T := by
      ext n; simp only [mem_filter, mem_Icc, not_le]; omega
    rw [hfil]
    have := sum_Icc_pronic_tail_le (X := N + 1) (by omega) T
    simpa using this
  calc ∑ n ∈ (Icc 1 T).filter (· ≤ N),
        weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) +
      ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n ≤ N),
        weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
      ≤ (2 * E + 2 * τ ^ 2 * N) + 9 * K ^ 2 * N * (1 / ((N : ℝ) + 1)) := by
        gcongr
        · refine (sum_le_sum hlow).trans ?_
          rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
          have hτ0 : 0 ≤ 2 * τ ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hcard hτ0]
        · refine (sum_le_sum hhigh).trans ?_
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ 2 * E + 17 * K ^ 2 := by
        have h1 : 9 * K ^ 2 * N * (1 / ((N : ℝ) + 1)) ≤ 9 * K ^ 2 := by
          rw [mul_one_div, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg K]
        nlinarith [hτ2]

/-- **From half damping on, the horizon limit commutes with the receiver**: on `𝒞(K, ε)`,
`ε ≥ 1/2`, the dyadic rows are uniformly paid exactly when the weight is paid. -/
theorem rows_bounded_iff_receiverBounded_of_half_le {K ε : ℝ} (hε : 1 / 2 ≤ ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) :
    (∃ E : ℝ, ∀ J T : ℕ, weightPronicEnergy (dyadicRow c J) (dyadicRowMean c J) T ≤ E) ↔
      ReceiverBounded c := by
  have hc' : DampedClass K (1 / 2) c := dampedClass_mono (by norm_num) hε hc
  have hs : Summable (fun d : ℕ => c d / d) := summable_div_of_dampedClass (by norm_num) hc'
  constructor
  · rintro ⟨E, hE⟩
    exact ⟨E, weightPronicEnergy_le_of_rows_le hs.hasSum hE⟩
  · rintro ⟨E, hE⟩
    exact ⟨2 * E + 17 * K ^ 2, rowEnergy_le_of_half hc' hE⟩

/-! ### Counting tools -/

/-- The hyperbola swap `Σ_{d≤n} c(d)⌊n/d⌋ = Σ_{k≤n} Σ_{d≤⌊n/k⌋} c(d)`. -/
theorem sum_mul_div_eq_sum_partial (c : ℕ → ℝ) (n : ℕ) :
    ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) = ∑ k ∈ Icc 1 n, ∑ d ∈ Icc 1 (n / k), c d := by
  have h1 : ∀ k ∈ Icc 1 n, ∑ d ∈ Icc 1 (n / k), c d =
      ∑ d ∈ Icc 1 n, if d * k ≤ n then c d else 0 := by
    intro k hk
    have hk0 : 0 < k := (mem_Icc.mp hk).1
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [mem_Icc, mem_filter, Nat.le_div_iff_mul_le hk0]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, (Nat.le_mul_of_pos_right d hk0).trans h2⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hfil : (Icc 1 n).filter (fun k => d * k ≤ n) = Icc 1 (n / d) := by
    ext k
    simp only [mem_Icc, mem_filter, Nat.le_div_iff_mul_le hd0, mul_comm d k]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, (Nat.le_mul_of_pos_right k hd0).trans h2⟩, h2⟩
  rw [← sum_filter, sum_const, nsmul_eq_mul, hfil, Nat.card_Icc, Nat.add_sub_cancel, mul_comm]

/-! ### The windowed dipole -/

/-- The windowed dipole: `αd` on `(N, N+w]`, `−αd` on `(N−w, N]`, zero elsewhere. -/
def windowDipole (N w : ℕ) (α : ℝ) (d : ℕ) : ℝ :=
  if N < d ∧ d ≤ N + w then α * d else if N - w < d ∧ d ≤ N then -(α * d) else 0

theorem windowDipole_eq_zero_of_not_mem {N w : ℕ} {α : ℝ} {d : ℕ}
    (hd : d ∉ Ioc (N - w) (N + w)) : windowDipole N w α d = 0 := by
  simp only [mem_Ioc, not_and, not_le] at hd
  unfold windowDipole
  split_ifs with h1 h2
  · exact absurd (hd (by omega)) (by omega)
  · exact absurd (hd h2.1) (by omega)
  · rfl

theorem abs_windowDipole_le {N w : ℕ} {α : ℝ} (hα : 0 ≤ α) (d : ℕ) :
    |windowDipole N w α d| ≤ α * ((N : ℝ) + w) := by
  unfold windowDipole
  split_ifs with h1 h2
  · rw [abs_of_nonneg (by positivity)]
    gcongr
    exact_mod_cast h1.2
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    gcongr
    exact_mod_cast h2.2.trans (Nat.le_add_right N w)
  · rw [abs_zero]
    positivity

theorem windowDipole_div (N w : ℕ) (α : ℝ) {d : ℕ} (hd : 0 < d) :
    windowDipole N w α d / d =
      (if N < d ∧ d ≤ N + w then α else 0) - (if N - w < d ∧ d ≤ N then α else 0) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold windowDipole
  split_ifs <;> first
    | (exfalso; omega)
    | (rw [mul_div_assoc, div_self hd0]; ring)
    | (rw [neg_div, mul_div_assoc, div_self hd0]; ring)
    | simp

/-- Harmonic partial masses of the dipole are counts. -/
theorem sum_windowDipole_div (N w : ℕ) (α : ℝ) (x : ℕ) :
    ∑ d ∈ Icc 1 x, windowDipole N w α d / d =
      α * ((Icc 1 x).filter (fun d => N < d ∧ d ≤ N + w)).card -
        α * ((Icc 1 x).filter (fun d => N - w < d ∧ d ≤ N)).card := by
  rw [sum_congr rfl fun d hd => windowDipole_div N w α (mem_Icc.mp hd).1, sum_sub_distrib,
    ← sum_filter, ← sum_filter, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_comm,
    mul_comm (((Icc 1 x).filter (fun d => N - w < d ∧ d ≤ N)).card : ℝ)]

theorem card_filter_right_of_le {N w x : ℕ} (hx : N + w ≤ x) :
    ((Icc 1 x).filter (fun d => N < d ∧ d ≤ N + w)).card = w := by
  have : (Icc 1 x).filter (fun d => N < d ∧ d ≤ N + w) = Ioc N (N + w) := by
    ext d; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  rw [this, Nat.card_Ioc]; omega

theorem card_filter_left_of_le {N w x : ℕ} (hw : w ≤ N) (hx : N ≤ x) :
    ((Icc 1 x).filter (fun d => N - w < d ∧ d ≤ N)).card = w := by
  have : (Icc 1 x).filter (fun d => N - w < d ∧ d ≤ N) = Ioc (N - w) N := by
    ext d; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  rw [this, Nat.card_Ioc]; omega

theorem card_filter_right_le (N w x : ℕ) :
    ((Icc 1 x).filter (fun d => N < d ∧ d ≤ N + w)).card ≤ w := by
  calc _ ≤ (Ioc N (N + w)).card := card_le_card fun d hd => by
        simp only [mem_filter, mem_Icc, mem_Ioc] at hd ⊢; omega
    _ = w := by rw [Nat.card_Ioc]; omega

theorem card_filter_left_le (N w x : ℕ) :
    ((Icc 1 x).filter (fun d => N - w < d ∧ d ≤ N)).card ≤ w := by
  calc _ ≤ (Ioc (N - w) N).card := card_le_card fun d hd => by
        simp only [mem_filter, mem_Icc, mem_Ioc] at hd ⊢; omega
    _ ≤ w := by rw [Nat.card_Ioc]; omega

/-- The dipole has harmonic mass zero. -/
theorem sum_windowDipole_div_of_le {N w : ℕ} (α : ℝ) (hw : w ≤ N) {x : ℕ} (hx : N + w ≤ x) :
    ∑ d ∈ Icc 1 x, windowDipole N w α d / d = 0 := by
  rw [sum_windowDipole_div, card_filter_right_of_le hx, card_filter_left_of_le hw (by omega),
    sub_self]

/-- The negative half carries harmonic mass `−αw`. -/
theorem sum_windowDipole_div_center {N w : ℕ} (α : ℝ) (hw : w ≤ N) :
    ∑ d ∈ Icc 1 N, windowDipole N w α d / d = -(α * w) := by
  have h0 : (Icc 1 N).filter (fun d => N < d ∧ d ≤ N + w) = ∅ := by
    ext d; simp only [mem_filter, mem_Icc, Finset.notMem_empty, iff_false]; omega
  rw [sum_windowDipole_div, h0, card_filter_left_of_le hw le_rfl, card_empty]
  push_cast
  ring

theorem abs_sum_windowDipole_div_le {N w : ℕ} {α : ℝ} (hα : 0 ≤ α) (x : ℕ) :
    |∑ d ∈ Icc 1 x, windowDipole N w α d / d| ≤ α * w := by
  rw [sum_windowDipole_div, ← mul_sub, abs_mul, abs_of_nonneg hα]
  refine mul_le_mul_of_nonneg_left ?_ hα
  have h1 : (((Icc 1 x).filter (fun d => N < d ∧ d ≤ N + w)).card : ℝ) ≤ w := by
    exact_mod_cast card_filter_right_le N w x
  have h2 : (((Icc 1 x).filter (fun d => N - w < d ∧ d ≤ N)).card : ℝ) ≤ w := by
    exact_mod_cast card_filter_left_le N w x
  rw [abs_le]
  constructor <;> linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤
    ((Icc 1 x).filter (fun d => N < d ∧ d ≤ N + w)).card), (Nat.cast_nonneg _ : (0 : ℝ) ≤
    ((Icc 1 x).filter (fun d => N - w < d ∧ d ≤ N)).card)]

/-- The total variation of the dipole: `Σ |b| ≤ 2w · α(N+w)`. -/
theorem sum_abs_windowDipole_le {N w : ℕ} {α : ℝ} (hα : 0 ≤ α) (hw : w ≤ N) (x : ℕ) :
    ∑ d ∈ Icc 1 x, |windowDipole N w α d| ≤ 2 * w * (α * ((N : ℝ) + w)) := by
  calc ∑ d ∈ Icc 1 x, |windowDipole N w α d|
      ≤ ∑ d ∈ Ioc (N - w) (N + w), |windowDipole N w α d| := by
        rw [← sum_filter_add_sum_filter_not (Icc 1 x) (· ∈ Ioc (N - w) (N + w))]
        have h0 : ∑ d ∈ (Icc 1 x).filter (· ∉ Ioc (N - w) (N + w)), |windowDipole N w α d| = 0 :=
          sum_eq_zero fun d hd => by
            rw [windowDipole_eq_zero_of_not_mem (mem_filter.mp hd).2, abs_zero]
        rw [h0, add_zero]
        exact sum_le_sum_of_subset_of_nonneg (fun d hd => (mem_filter.mp hd).2)
          fun _ _ _ => abs_nonneg _
    _ ≤ ∑ d ∈ Ioc (N - w) (N + w), α * ((N : ℝ) + w) :=
        sum_le_sum fun d _ => abs_windowDipole_le hα d
    _ = 2 * w * (α * ((N : ℝ) + w)) := by
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show N + w - (N - w) = 2 * w by omega]
        push_cast
        ring

/-- Below the window the plain partial sums vanish. -/
theorem sum_windowDipole_of_le {N w : ℕ} (α : ℝ) {x : ℕ} (hx : x ≤ N - w) :
    ∑ d ∈ Icc 1 x, windowDipole N w α d = 0 :=
  sum_eq_zero fun d hd => windowDipole_eq_zero_of_not_mem (by
    simp only [mem_Icc, mem_Ioc, not_and, not_le] at hd ⊢; omega)

/-- Beyond the window the plain mass is `P = αw²`. -/
theorem sum_windowDipole_of_ge {N w : ℕ} (α : ℝ) (hw : w ≤ N) {x : ℕ} (hx : N + w ≤ x) :
    ∑ d ∈ Icc 1 x, windowDipole N w α d = α * (w : ℝ) ^ 2 := by
  have hsplit : ∀ d ∈ Icc 1 x, windowDipole N w α d =
      (if d ∈ Ioc N (N + w) then α * d else 0) - (if d ∈ Ioc (N - w) N then α * d else 0) := by
    intro d _
    simp only [mem_Ioc]
    unfold windowDipole
    split_ifs <;> first | (exfalso; omega) | ring
  rw [sum_congr rfl hsplit, sum_sub_distrib, sum_ite_mem, sum_ite_mem,
    show Icc 1 x ∩ Ioc N (N + w) = Ioc N (N + w) by
      ext d; simp only [mem_inter, mem_Icc, mem_Ioc]; omega,
    show Icc 1 x ∩ Ioc (N - w) N = Ioc (N - w) N by
      ext d; simp only [mem_inter, mem_Icc, mem_Ioc]; omega]
  have hshift : ∑ d ∈ Ioc N (N + w), α * (d : ℝ) = ∑ d ∈ Ioc (N - w) N, α * ((d : ℝ) + w) := by
    have hmap : (Ioc (N - w) N).map (addRightEmbedding w) = Ioc N (N + w) := by
      rw [map_add_right_Ioc, Nat.sub_add_cancel hw]
    rw [← hmap, sum_map]
    refine sum_congr rfl fun d _ => ?_
    simp only [addRightEmbedding_apply]
    push_cast
    ring
  rw [hshift, ← sum_sub_distrib]
  simp only [mul_add, add_sub_cancel_left]
  rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show N - (N - w) = w by omega]
  ring

/-- Every plain partial sum is bounded by the total variation. -/
theorem abs_sum_windowDipole_le {N w : ℕ} {α : ℝ} (hα : 0 ≤ α) (hw : w ≤ N) (x : ℕ) :
    |∑ d ∈ Icc 1 x, windowDipole N w α d| ≤ 2 * w * (α * ((N : ℝ) + w)) :=
  (abs_sum_le_sum_abs _ _).trans (sum_abs_windowDipole_le hα hw x)

/-! ### The prefix of a dipole -/

/-- The prefix of the dipole is a sum of plain partial sums: `A(n) = Σ_{k≤n} S(⌊n/k⌋)`. -/
theorem weightCenteredPrefix_windowDipole (N w : ℕ) (α : ℝ) (n : ℕ) :
    weightCenteredPrefix (windowDipole N w α) 0 n =
      ∑ k ∈ Icc 1 n, ∑ d ∈ Icc 1 (n / k), windowDipole N w α d := by
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, sum_mul_div_eq_sum_partial, zero_mul,
    sub_zero]

/-- Beyond the window the prefix is a bounded sawtooth sum. -/
theorem abs_weightCenteredPrefix_windowDipole_le_of_ge {N w : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hw : w ≤ N) {n : ℕ} (hn : N + w ≤ n) :
    |weightCenteredPrefix (windowDipole N w α) 0 n| ≤ 2 * w * (α * ((N : ℝ) + w)) := by
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, zero_mul, sub_zero]
  have hsplit : ∑ d ∈ Icc 1 n, windowDipole N w α d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 n, windowDipole N w α d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d) +
        n * ∑ d ∈ Icc 1 n, windowDipole N w α d / d := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    ring
  rw [hsplit, sum_windowDipole_div_of_le α hw hn, mul_zero, add_zero]
  refine (abs_sum_le_sum_abs _ _).trans
    ((sum_le_sum fun d hd => ?_).trans (sum_abs_windowDipole_le hα hw n))
  rw [abs_mul]
  calc |windowDipole N w α d| * |((n / d : ℕ) : ℝ) - (n : ℝ) / d|
      ≤ |windowDipole N w α d| * 1 :=
        mul_le_mul_of_nonneg_left (abs_natDiv_sub_div_le n d (mem_Icc.mp hd).1) (abs_nonneg _)
    _ = |windowDipole N w α d| := mul_one _

/-- The number of `k ≤ n` with `⌊n/k⌋` strictly inside the window. -/
def windowMiddleCount (N w n : ℕ) : ℕ :=
  ((Icc 1 n).filter (fun k => N - w < n / k ∧ n / k < N + w)).card

/-- **The hyperbola bound.** `|A(n)| ≤ P ⌊n/(N+w)⌋ + (Σ|b|) D(n)`. -/
theorem abs_weightCenteredPrefix_windowDipole_le {N w : ℕ} {α : ℝ} (hα : 0 ≤ α) (hN : 1 ≤ N)
    (hw : w ≤ N) (n : ℕ) :
    |weightCenteredPrefix (windowDipole N w α) 0 n| ≤
      α * (w : ℝ) ^ 2 * ((n / (N + w) : ℕ) : ℝ) +
        2 * w * (α * ((N : ℝ) + w)) * windowMiddleCount N w n := by
  rw [weightCenteredPrefix_windowDipole]
  set P := α * (w : ℝ) ^ 2 with hPdef
  set B := 2 * w * (α * ((N : ℝ) + w)) with hBdef
  have hP : 0 ≤ P := by positivity
  have hpt : ∀ k ∈ Icc 1 n, |∑ d ∈ Icc 1 (n / k), windowDipole N w α d| ≤
      (if N + w ≤ n / k then P else 0) + (if N - w < n / k ∧ n / k < N + w then B else 0) := by
    intro k _
    by_cases h1 : N + w ≤ n / k
    · rw [if_pos h1, if_neg (by omega), add_zero, sum_windowDipole_of_ge α hw h1,
        abs_of_nonneg hP]
    · by_cases h2 : N - w < n / k
      · rw [if_neg h1, if_pos ⟨h2, by omega⟩, zero_add]
        exact abs_sum_windowDipole_le hα hw _
      · rw [if_neg h1, if_neg (by omega), add_zero, sum_windowDipole_of_le α (by omega),
          abs_zero]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hpt).trans ?_)
  rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const, nsmul_eq_mul,
    nsmul_eq_mul]
  have hcard : ((Icc 1 n).filter (fun k => N + w ≤ n / k)).card ≤ n / (N + w) := by
    calc _ ≤ (Icc 1 (n / (N + w))).card := card_le_card fun k hk => by
          simp only [mem_filter, mem_Icc] at hk ⊢
          refine ⟨hk.1.1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
          calc k * (N + w) ≤ k * (n / k) := Nat.mul_le_mul_left k hk.2
            _ ≤ n := Nat.mul_div_le n k
      _ = n / (N + w) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hcard' : (((Icc 1 n).filter (fun k => N + w ≤ n / k)).card : ℝ) ≤ ((n / (N + w) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hD : (((Icc 1 n).filter (fun k => N - w < n / k ∧ n / k < N + w)).card : ℝ) =
      (windowMiddleCount N w n : ℝ) := rfl
  rw [hD]
  nlinarith [mul_le_mul_of_nonneg_right hcard' hP]

/-- Two indices `a < b` cannot both see the window when `2wn ≤ (N−w+1)²`. -/
theorem windowMiddle_not_two {N w n a b : ℕ} (hw : w ≤ N) (hn : 2 * w * n ≤ (N - w + 1) ^ 2)
    (ha : 1 ≤ a) (hab : a < b) (hal : n / a < N + w) (hbl : N - w < n / b) : False := by
  set l := N - w + 1 with hl
  have hl1 : 1 ≤ l := by omega
  have hNw : N + w + 1 = l + 2 * w := by omega
  have h1 : l * b ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
  have h2 : n < (N + w) * a := (Nat.div_lt_iff_lt_mul (by omega)).mp hal
  have h3 : l * (a + 1) ≤ n := le_trans (Nat.mul_le_mul_left l (Nat.succ_le_of_lt hab)) h1
  have h2' : (N + w) * a + a = l * a + 2 * w * a :=
    calc (N + w) * a + a = (N + w + 1) * a := by ring
      _ = (l + 2 * w) * a := by rw [hNw]
      _ = l * a + 2 * w * a := by ring
  have h4 : l < 2 * w * a := by nlinarith [mul_add l a 1]
  have h5 : l * a ≤ n := by nlinarith [mul_add l a 1]
  nlinarith [Nat.mul_lt_mul_of_pos_right h4 (by omega : 0 < l), Nat.mul_le_mul_left (2 * w) h5]

/-- Below the cut the middle count is at most one. -/
theorem windowMiddleCount_le_one {N w n : ℕ} (hw : w ≤ N) (hn : 2 * w * n ≤ (N - w + 1) ^ 2) :
    windowMiddleCount N w n ≤ 1 := by
  rw [windowMiddleCount, card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_Icc] at ha hb
  by_contra hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact windowMiddle_not_two hw hn ha.1.1 h ha.2.2 hb.2.1
  · exact windowMiddle_not_two hw hn hb.1.1 h hb.2.2 ha.2.1

/-- Each `k` sees the window on at most `k(2w−1) ≤ 2wk` integers `n ≥ k(N−w+1)`, so the pronic mass
of those `n` is at most `2w/(N−w+1)²`, and only `k ≤ X/(N−w+1)` occur below `X`. -/
theorem sum_windowMiddleCount_le {N w : ℕ} (hw : w ≤ N) (X : ℕ) :
    ∑ n ∈ Ico 1 X, (windowMiddleCount N w n : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      ((X / (N - w + 1) : ℕ) : ℝ) * (2 * w / ((N - w + 1 : ℕ) : ℝ) ^ 2) := by
  set l := N - w + 1 with hl
  have hl1 : 1 ≤ l := by omega
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
  set cond : ℕ → ℕ → Prop := fun k n => N - w < n / k ∧ n / k < N + w with hcond
  -- the count over `k ≤ n` is the count over `k ≤ X`
  have hcount : ∀ n ∈ Ico 1 X, (windowMiddleCount N w n : ℝ) =
      ∑ k ∈ Icc 1 X, if cond k n then (1 : ℝ) else 0 := by
    intro n hn
    have hnX : n < X := (mem_Ico.mp hn).2
    rw [sum_boole, windowMiddleCount]
    congr 2
    ext k
    simp only [mem_filter, mem_Icc, hcond]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      by_contra hkn
      have : n / k = 0 := Nat.div_eq_of_lt (by omega)
      omega
  have hswap : ∑ n ∈ Ico 1 X, (windowMiddleCount N w n : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) =
      ∑ k ∈ Icc 1 X, ∑ n ∈ Ico 1 X, if cond k n then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0 := by
    rw [sum_congr rfl fun n hn => by rw [hcount n hn, sum_div], sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  rw [hswap]
  have hinner : ∀ k ∈ Icc 1 X, ∑ n ∈ Ico 1 X, (if cond k n then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0)
      ≤ if k * l < X then 2 * w / (l : ℝ) ^ 2 else 0 := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    split_ifs with hkl
    · rw [← sum_filter]
      have hsub : (Ico 1 X).filter (cond k) ⊆ Ico (l * k) ((N + w) * k) := fun n hn => by
        simp only [mem_filter, mem_Ico, hcond] at hn ⊢
        exact ⟨(Nat.le_div_iff_mul_le (by omega)).mp (by omega),
          (Nat.div_lt_iff_lt_mul (by omega)).mp hn.2.2⟩
      have hterm : ∀ n ∈ (Ico 1 X).filter (cond k),
          1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ 1 / ((l : ℝ) * k) ^ 2 := by
        intro n hn
        have hn' := mem_Ico.mp (hsub hn)
        have hlk : (l : ℝ) * k ≤ n := by exact_mod_cast hn'.1
        have hlk0 : (0 : ℝ) < (l : ℝ) * k := by positivity
        rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
        nlinarith
      calc ∑ n ∈ (Ico 1 X).filter (cond k), 1 / ((n : ℝ) * ((n : ℝ) + 1))
          ≤ ∑ n ∈ (Ico 1 X).filter (cond k), 1 / ((l : ℝ) * k) ^ 2 := sum_le_sum hterm
        _ = ((Ico 1 X).filter (cond k)).card * (1 / ((l : ℝ) * k) ^ 2) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ((2 * w * k : ℕ) : ℝ) * (1 / ((l : ℝ) * k) ^ 2) := by
            gcongr
            calc ((Ico 1 X).filter (cond k)).card ≤ (Ico (l * k) ((N + w) * k)).card :=
                  card_le_card hsub
              _ = (N + w) * k - l * k := Nat.card_Ico _ _
              _ ≤ 2 * w * k := by
                  rw [← Nat.sub_mul]
                  exact Nat.mul_le_mul_right k (by omega)
        _ = 2 * w / (l : ℝ) ^ 2 * (1 / k) := by
            push_cast
            field_simp
        _ ≤ 2 * w / (l : ℝ) ^ 2 * 1 := by
            gcongr
            rw [div_le_one hk0]
            exact_mod_cast hk1
        _ = 2 * w / (l : ℝ) ^ 2 := mul_one _
    · refine (sum_eq_zero fun n hn => ?_).le
      have hnX : n < X := (mem_Ico.mp hn).2
      rw [if_neg]
      simp only [hcond, not_and, not_lt]
      intro h
      have h1 : l * k ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
      have h2 : X ≤ k * l := not_lt.mp hkl
      rw [mul_comm] at h1
      omega
  calc ∑ k ∈ Icc 1 X, ∑ n ∈ Ico 1 X, (if cond k n then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0)
      ≤ ∑ k ∈ Icc 1 X, if k * l < X then 2 * w / (l : ℝ) ^ 2 else 0 := sum_le_sum hinner
    _ = ((Icc 1 X).filter (fun k => k * l < X)).card * (2 * w / (l : ℝ) ^ 2) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ((X / l : ℕ) : ℝ) * (2 * w / (l : ℝ) ^ 2) := by
        gcongr
        calc ((Icc 1 X).filter (fun k => k * l < X)).card ≤ (Icc 1 (X / l)).card :=
              card_le_card fun k hk => by
                simp only [mem_filter, mem_Icc] at hk ⊢
                exact ⟨hk.1.1, (Nat.le_div_iff_mul_le (by omega)).mpr hk.2.le⟩
          _ = X / l := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- **The energy of one dipole.** With `P = αw²`, `B = 2wα(N+w)`, `l = N−w+1` and a cut `X` with
`N + w ≤ X`, `2wX ≤ l²`, for every horizon `T`:
`E_T(b) ≤ 2P²X/(N+w)² + 2B²·⌊X/l⌋·2w/l² + B²/X`. -/
theorem weightPronicEnergy_windowDipole_le {N w X : ℕ} {α : ℝ} (hα : 0 ≤ α) (hN : 1 ≤ N)
    (hw : w ≤ N) (hX : N + w ≤ X) (hXw : 2 * w * X ≤ (N - w + 1) ^ 2) (T : ℕ) :
    weightPronicEnergy (windowDipole N w α) 0 T ≤
      2 * (α * (w : ℝ) ^ 2) ^ 2 * X / ((N : ℝ) + w) ^ 2 +
        2 * (2 * w * (α * ((N : ℝ) + w))) ^ 2 *
          (((X / (N - w + 1) : ℕ) : ℝ) * (2 * w / ((N - w + 1 : ℕ) : ℝ) ^ 2)) +
        (2 * w * (α * ((N : ℝ) + w))) ^ 2 / X := by
  set P := α * (w : ℝ) ^ 2 with hPdef
  set B := 2 * w * (α * ((N : ℝ) + w)) with hBdef
  have hP : 0 ≤ P := by positivity
  have hB : 0 ≤ B := by positivity
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNw : (0 : ℝ) < (N : ℝ) + w := by linarith [(Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
  have hX1 : 1 ≤ X := by omega
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  set A := fun n => weightCenteredPrefix (windowDipole N w α) 0 n with hAdef
  rw [weightPronicEnergy, ← sum_filter_add_sum_filter_not (Icc 1 T) (· < X)]
  -- below the cut
  have hlow : ∀ n ∈ (Icc 1 T).filter (· < X), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      2 * P ^ 2 / ((N : ℝ) + w) ^ 2 + 2 * B ^ 2 * ((windowMiddleCount N w n : ℝ) /
        ((n : ℝ) * ((n : ℝ) + 1))) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
    have hpron : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    have hD1 : windowMiddleCount N w n ≤ 1 :=
      windowMiddleCount_le_one hw (le_trans (Nat.mul_le_mul_left _ hn.2.le) hXw)
    have hD : (windowMiddleCount N w n : ℝ) ^ 2 ≤ windowMiddleCount N w n := by
      have h0 : (0 : ℝ) ≤ windowMiddleCount N w n := Nat.cast_nonneg _
      have h1 : (windowMiddleCount N w n : ℝ) ≤ 1 := by exact_mod_cast hD1
      nlinarith
    have hq : ((n / (N + w) : ℕ) : ℝ) ≤ (n : ℝ) / ((N : ℝ) + w) := by
      have := Nat.cast_div_le (m := n) (n := N + w) (α := ℝ)
      simpa using this
    have hq0 : (0 : ℝ) ≤ ((n / (N + w) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hA := abs_weightCenteredPrefix_windowDipole_le hα hN hw n
    have hsq : A n ^ 2 ≤ 2 * P ^ 2 * ((n / (N + w) : ℕ) : ℝ) ^ 2 +
        2 * B ^ 2 * (windowMiddleCount N w n : ℝ) ^ 2 := by
      have h1 : |A n| ≤ P * ((n / (N + w) : ℕ) : ℝ) + B * windowMiddleCount N w n := hA
      have h2 : A n ^ 2 ≤ (P * ((n / (N + w) : ℕ) : ℝ) + B * windowMiddleCount N w n) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith [sq_nonneg (P * ((n / (N + w) : ℕ) : ℝ) - B * windowMiddleCount N w n)]
    have hq2 : ((n / (N + w) : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / ((N : ℝ) + w) ^ 2 := by
      rw [← div_pow]; exact pow_le_pow_left₀ hq0 hq 2
    have hn2 : (n : ℝ) ^ 2 / ((N : ℝ) + w) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        1 / ((N : ℝ) + w) ^ 2 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ (2 * P ^ 2 * ((n : ℝ) ^ 2 / ((N : ℝ) + w) ^ 2) +
            2 * B ^ 2 * (windowMiddleCount N w n : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1)) := by
          gcongr
          nlinarith [mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ 2 * P ^ 2),
            mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 2 * B ^ 2)]
      _ = 2 * P ^ 2 * ((n : ℝ) ^ 2 / ((N : ℝ) + w) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
            2 * B ^ 2 * ((windowMiddleCount N w n : ℝ) / ((n : ℝ) * ((n : ℝ) + 1))) := by ring
      _ ≤ 2 * P ^ 2 * (1 / ((N : ℝ) + w) ^ 2) +
            2 * B ^ 2 * ((windowMiddleCount N w n : ℝ) / ((n : ℝ) * ((n : ℝ) + 1))) := by
          gcongr
      _ = _ := by ring
  have hsub : (Icc 1 T).filter (· < X) ⊆ Ico 1 X := fun n hn => by
    simp only [mem_filter, mem_Icc, mem_Ico] at hn ⊢; exact ⟨hn.1.1, hn.2⟩
  have hpart1 : ∑ n ∈ (Icc 1 T).filter (· < X), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      2 * P ^ 2 * X / ((N : ℝ) + w) ^ 2 +
        2 * B ^ 2 * (((X / (N - w + 1) : ℕ) : ℝ) * (2 * w / ((N - w + 1 : ℕ) : ℝ) ^ 2)) := by
    refine (sum_le_sum hlow).trans ?_
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    have hc : (((Icc 1 T).filter (· < X)).card : ℝ) ≤ X := by
      have := card_le_card hsub
      rw [Nat.card_Ico] at this
      exact_mod_cast this.trans (Nat.sub_le X 1)
    have hm : ∑ n ∈ (Icc 1 T).filter (· < X), (windowMiddleCount N w n : ℝ) /
        ((n : ℝ) * ((n : ℝ) + 1)) ≤
        ((X / (N - w + 1) : ℕ) : ℝ) * (2 * w / ((N - w + 1 : ℕ) : ℝ) ^ 2) :=
      (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity).trans
        (sum_windowMiddleCount_le hw X)
    have h2P : 0 ≤ 2 * P ^ 2 / ((N : ℝ) + w) ^ 2 := by positivity
    calc (((Icc 1 T).filter (· < X)).card : ℝ) * (2 * P ^ 2 / ((N : ℝ) + w) ^ 2) +
          2 * B ^ 2 * ∑ n ∈ (Icc 1 T).filter (· < X), (windowMiddleCount N w n : ℝ) /
            ((n : ℝ) * ((n : ℝ) + 1))
        ≤ X * (2 * P ^ 2 / ((N : ℝ) + w) ^ 2) +
          2 * B ^ 2 * (((X / (N - w + 1) : ℕ) : ℝ) * (2 * w / ((N - w + 1 : ℕ) : ℝ) ^ 2)) := by
          gcongr
      _ = _ := by ring
  -- beyond the cut
  have hpart2 : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < X), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      B ^ 2 / X := by
    have hfil : (Icc 1 T).filter (fun n => ¬ n < X) = Icc X T := by
      ext n; simp only [mem_filter, mem_Icc, not_lt]; omega
    rw [hfil]
    calc ∑ n ∈ Icc X T, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ Icc X T, B ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
          refine sum_le_sum fun n hn => ?_
          have hnX := (mem_Icc.mp hn).1
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hA := abs_weightCenteredPrefix_windowDipole_le_of_ge hα hw (n := n) (by omega)
          have h2 : A n ^ 2 ≤ B ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
          rw [mul_one_div]
          gcongr
      _ = B ^ 2 * ∑ n ∈ Icc X T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by rw [mul_sum]
      _ ≤ B ^ 2 * (1 / (X : ℝ)) := by
          gcongr
          exact sum_Icc_pronic_tail_le hX1 T
      _ = B ^ 2 / X := by ring
  linarith

/-! ### Exponent bookkeeping -/

theorem cast_two_pow_eq_rpow (k : ℕ) : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k : ℝ) := by
  rw [Real.rpow_natCast]; push_cast; ring

theorem two_rpow_mul_natCast (e : ℝ) (t : ℕ) : (2 : ℝ) ^ (e * t) = ((2 : ℝ) ^ e) ^ t := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- `Σ_{1 ≤ t ≤ n} 2^{-t} ≤ 1`. -/
theorem sum_Icc_half_pow_le (n : ℕ) : ∑ t ∈ Icc 1 n, (1 / 2 : ℝ) ^ t ≤ 1 := by
  have h : ∀ n : ℕ, ∑ t ∈ Icc 1 n, (1 / 2 : ℝ) ^ t = 1 - (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_Icc_succ_top (by omega), ih, pow_succ]; ring
  rw [h]
  have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  linarith

/-- Weighted Cauchy–Schwarz: `(Σ_{1≤t≤n} a_t)² ≤ Σ_{1≤t≤n} 2^t a_t²`. -/
theorem sq_sum_le_sum_two_pow_mul_sq (a : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Icc 1 n, a t) ^ 2 ≤ ∑ t ∈ Icc 1 n, (2 : ℝ) ^ t * a t ^ 2 := by
  have hg : ∀ t ∈ Icc 1 n, (0 : ℝ) < (1 / 2) ^ t := fun t _ => by positivity
  have h := sq_sum_div_le_sum_sq_div (Icc 1 n) a hg
  have hS := sum_Icc_half_pow_le n
  have hS0 : 0 < ∑ t ∈ Icc 1 n, (1 / 2 : ℝ) ^ t ∨ Icc 1 n = ∅ := by
    rcases (Icc 1 n).eq_empty_or_nonempty with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (sum_pos hg h0)
  have hR : ∑ t ∈ Icc 1 n, a t ^ 2 / (1 / 2 : ℝ) ^ t = ∑ t ∈ Icc 1 n, (2 : ℝ) ^ t * a t ^ 2 :=
    sum_congr rfl fun t _ => by rw [one_div, inv_pow, div_inv_eq_mul, mul_comm]
  rw [hR] at h
  rcases hS0 with hS0 | h0
  · have hR0 : 0 ≤ ∑ t ∈ Icc 1 n, (2 : ℝ) ^ t * a t ^ 2 := sum_nonneg fun t _ => by positivity
    rw [div_le_iff₀ hS0] at h
    nlinarith
  · rw [h0, sum_empty, sum_empty]; norm_num

/-- Geometric tails: `Σ_{a ≤ t ≤ b} r^t ≤ r^a/(1−r)` for `0 ≤ r < 1`. -/
theorem sum_Icc_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a b : ℕ) :
    ∑ t ∈ Icc a b, r ^ t ≤ r ^ a / (1 - r) := by
  have hsum : Summable (fun k : ℕ => r ^ (k + a)) :=
    (summable_geometric_of_lt_one hr0 hr1).comp_injective (add_left_injective a)
  calc ∑ t ∈ Icc a b, r ^ t ≤ ∑ k ∈ range (b + 1 - a), r ^ (k + a) := by
        rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
        exact le_of_eq (sum_congr rfl fun k _ => by rw [add_comm])
    _ ≤ ∑' k : ℕ, r ^ (k + a) := hsum.sum_le_tsum _ fun _ _ => by positivity
    _ = r ^ a / (1 - r) := by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
        field_simp

/-! ### The lacunary superposition -/

section Lacunary

variable (L M Q : ℕ) (ε : ℝ)

/-- Centre `2^{Lt}` of the stage-`t` dipole. -/
def lacN (t : ℕ) : ℕ := 2 ^ (L * t)

/-- Half-width `2^{Mt}`. -/
def lacW (t : ℕ) : ℕ := 2 ^ (M * t)

/-- Amplitude `(2N)^{-1-ε}`, which puts the dipole in `𝒞(1, ε)`. -/
def lacAmp (t : ℕ) : ℝ := ((2 * lacN L t : ℕ) : ℝ) ^ (-1 - ε)

/-- The stage-`t` dipole. -/
def lacBlock (t : ℕ) : ℕ → ℝ := windowDipole (lacN L t) (lacW M t) (lacAmp L ε t)

/-- The lacunary superposition of the dipoles of all stages `t ≥ 1`. -/
def lacWeight (d : ℕ) : ℝ := ∑ t ∈ Icc 1 d, lacBlock L M ε t d

end Lacunary

section LacunaryFacts

variable {L M : ℕ} (hLM : M + 3 ≤ L)
include hLM

theorem lac_mul_eight_pow_le {t : ℕ} : lacW M t * 8 ^ t ≤ lacN L t := by
  unfold lacW lacN
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem lac_add_le {t : ℕ} (_ht : 1 ≤ t) : lacW M t + t ≤ lacN L t := by
  have h := lac_mul_eight_pow_le hLM (t := t)
  have hw : 1 ≤ lacW M t := Nat.one_le_two_pow
  have h8 : t + 1 ≤ 8 ^ t := by
    have h2 : t < 2 ^ t := Nat.lt_two_pow_self
    have h3 : 2 ^ t ≤ 8 ^ t := Nat.pow_le_pow_left (by norm_num) t
    omega
  nlinarith

theorem lac_eight_le {t : ℕ} (ht : 1 ≤ t) : 8 * lacW M t ≤ lacN L t := by
  have h := lac_mul_eight_pow_le hLM (t := t)
  have h8 : 8 ≤ 8 ^ t := Nat.le_self_pow (by omega) 8
  nlinarith [Nat.mul_le_mul_left (lacW M t) h8]

theorem lacW_le {t : ℕ} (ht : 1 ≤ t) : lacW M t ≤ lacN L t := by
  have := lac_eight_le hLM ht; omega

/-- The windows of distinct stages are disjoint and ordered. -/
theorem lac_window_lt {s t : ℕ} (hs : 1 ≤ s) (hst : s < t) :
    lacN L s + lacW M s ≤ lacN L t - lacW M t := by
  have ht : 1 ≤ t := by omega
  have h1 : lacW M s ≤ lacN L s := lacW_le hLM hs
  have h2 : 8 * lacW M t ≤ lacN L t := lac_eight_le hLM ht
  have h3 : lacN L s * 2 ^ L ≤ lacN L t := by
    unfold lacN; rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h4 : 8 ≤ 2 ^ L := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 8 * lacN L s ≤ lacN L t :=
    le_trans (by rw [mul_comm]; exact Nat.mul_le_mul_left _ h4) h3
  omega

theorem lacBlock_eq_zero_of_lt {ε : ℝ} {t d : ℕ} (ht : 1 ≤ t) (hdt : d < t) :
    lacBlock L M ε t d = 0 :=
  windowDipole_eq_zero_of_not_mem (by
    have := lac_add_le hLM ht
    simp only [mem_Ioc, not_and, not_le]; omega)

/-- On `[1, n]` the weight is the sum of the stages `t ≤ n`. -/
theorem lacWeight_eq_sum {ε : ℝ} {d n : ℕ} (hdn : d ≤ n) :
    lacWeight L M ε d = ∑ t ∈ Icc 1 n, lacBlock L M ε t d := by
  unfold lacWeight
  refine sum_subset (Icc_subset_Icc le_rfl hdn) fun t ht ht' => ?_
  simp only [mem_Icc, not_and, not_le] at ht ht'
  exact lacBlock_eq_zero_of_lt hLM ht.1 (ht' ht.1)

omit hLM in
theorem lacBlock_ne_zero_mem {ε : ℝ} {t d : ℕ} (h : lacBlock L M ε t d ≠ 0) :
    d ∈ Ioc (lacN L t - lacW M t) (lacN L t + lacW M t) := by
  by_contra hd; exact h (windowDipole_eq_zero_of_not_mem hd)

/-- At most one stage is active at each `d`. -/
theorem lacBlock_eq_zero_of_ne {ε : ℝ} {s t d : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hst : s ≠ t)
    (hne : lacBlock L M ε t d ≠ 0) : lacBlock L M ε s d = 0 := by
  by_contra hs0
  have h1 := mem_Ioc.mp (lacBlock_ne_zero_mem hs0)
  have h2 := mem_Ioc.mp (lacBlock_ne_zero_mem hne)
  rcases lt_or_gt_of_ne hst with h | h
  · have := lac_window_lt hLM hs h; omega
  · have := lac_window_lt hLM ht h; omega

end LacunaryFacts

/-- The absolute harmonic mass of the dipole is at most `2αw`. -/
theorem sum_abs_windowDipole_div_le {N w : ℕ} {α : ℝ} (hα : 0 ≤ α) (x : ℕ) :
    ∑ d ∈ Icc 1 x, |windowDipole N w α d / d| ≤ 2 * (α * w) := by
  rw [sum_congr rfl fun d hd => by rw [windowDipole_div N w α (mem_Icc.mp hd).1]]
  calc ∑ d ∈ Icc 1 x, |(if N < d ∧ d ≤ N + w then α else 0) - (if N - w < d ∧ d ≤ N then α else 0)|
      ≤ ∑ d ∈ Icc 1 x, ((if N < d ∧ d ≤ N + w then α else 0) +
          (if N - w < d ∧ d ≤ N then α else 0)) := sum_le_sum fun d _ => by
        refine (abs_sub _ _).trans ?_
        split_ifs <;> simp [abs_of_nonneg hα]
    _ = α * ((Icc 1 x).filter (fun d => N < d ∧ d ≤ N + w)).card +
          α * ((Icc 1 x).filter (fun d => N - w < d ∧ d ≤ N)).card := by
        rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const, nsmul_eq_mul,
          nsmul_eq_mul, mul_comm, mul_comm (((Icc 1 x).filter (fun d => N - w < d ∧ d ≤ N)).card : ℝ)]
    _ ≤ α * w + α * w := by
        gcongr
        · exact_mod_cast card_filter_right_le N w x
        · exact_mod_cast card_filter_left_le N w x
    _ = 2 * (α * w) := by ring

section LacunaryWeight

variable {L M Q : ℕ} {ε : ℝ}

theorem lacAmp_pos (t : ℕ) : 0 < lacAmp L ε t := by
  unfold lacAmp lacN; exact Real.rpow_pos_of_pos (by positivity) _

theorem lacN_pos (t : ℕ) : 0 < lacN L t := Nat.two_pow_pos _

/-- The weight lies in the damped class `𝒞(1, ε)`. -/
theorem dampedClass_lacWeight (hLM : M + 3 ≤ L) (hε : 0 ≤ ε) :
    DampedClass 1 ε (lacWeight L M ε) := by
  intro d
  rw [one_mul]
  by_cases h : ∃ t ∈ Icc 1 d, lacBlock L M ε t d ≠ 0
  · obtain ⟨t, ht, hne⟩ := h
    have ht1 := (mem_Icc.mp ht).1
    rw [lacWeight, sum_eq_single t
      (fun s hs hst => lacBlock_eq_zero_of_ne hLM (mem_Icc.mp hs).1 ht1 hst hne)
      (fun h => absurd ht h)]
    have hmem := mem_Ioc.mp (lacBlock_ne_zero_mem hne)
    have hd1 : 1 ≤ d := ht1.trans (mem_Icc.mp ht).2
    have hw := lacW_le hLM ht1
    have hd2 : d ≤ 2 * lacN L t := by omega
    have hα := lacAmp_pos (L := L) (ε := ε) t
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have habs : |lacBlock L M ε t d| ≤ lacAmp L ε t * d := by
      unfold lacBlock windowDipole
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
      · rw [abs_neg, abs_of_nonneg (by positivity)]
      · rw [abs_zero]; positivity
    have hcmp : lacAmp L ε t ≤ (d : ℝ) ^ (-1 - ε) := by
      unfold lacAmp
      exact Real.rpow_le_rpow_of_nonpos hd0 (by exact_mod_cast hd2) (by linarith)
    calc |lacBlock L M ε t d| ≤ lacAmp L ε t * d := habs
      _ ≤ (d : ℝ) ^ (-1 - ε) * d := by gcongr
      _ = (d : ℝ) ^ (-ε) := by
          rw [← Real.rpow_add_one hd0.ne', show -1 - ε + 1 = -ε by ring]
  · push Not at h
    rw [lacWeight, sum_eq_zero h, abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg d) _

/-- The stage masses are geometrically small: `αw ≤ 8^{-t}`. -/
theorem lacAmp_mul_lacW_le (hLM : M + 3 ≤ L) (hε : 0 ≤ ε) (t : ℕ) :
    lacAmp L ε t * lacW M t ≤ (1 / 8 : ℝ) ^ t := by
  have hN1 : (1 : ℝ) ≤ ((2 * lacN L t : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * lacN L t by have := lacN_pos (L := L) t; omega)
  have h1 : lacAmp L ε t ≤ ((2 * lacN L t : ℕ) : ℝ)⁻¹ := by
    unfold lacAmp
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h8 : ((lacW M t * 8 ^ t : ℕ) : ℝ) ≤ (lacN L t : ℝ) := by
    exact_mod_cast lac_mul_eight_pow_le hLM (t := t)
  have hNpos : (0 : ℝ) < lacN L t := by exact_mod_cast lacN_pos (L := L) t
  push_cast at h8 h1
  have hw0 : (0 : ℝ) ≤ lacW M t := Nat.cast_nonneg _
  have h8t : (0 : ℝ) < 8 ^ t := by positivity
  calc lacAmp L ε t * lacW M t ≤ (2 * (lacN L t : ℝ))⁻¹ * lacW M t := by gcongr
    _ ≤ (lacN L t : ℝ)⁻¹ * lacW M t := by
        gcongr
        linarith
    _ ≤ (1 / 8 : ℝ) ^ t := by
        rw [one_div_pow, inv_mul_le_iff₀ hNpos, mul_one_div, le_div_iff₀ h8t]
        exact h8

/-- **The weight has mean zero.** -/
theorem hasSum_lacWeight_div (hLM : M + 3 ≤ L) (hε : 0 ≤ ε) :
    HasSum (fun d : ℕ => lacWeight L M ε d / d) 0 := by
  have hr : (0 : ℝ) ≤ 1 / 8 := by norm_num
  have hr1 : (1 / 8 : ℝ) < 1 := by norm_num
  -- the harmonic partial sums decompose into the stages
  have hdecomp : ∀ x : ℕ, ∑ d ∈ Icc 1 x, lacWeight L M ε d / d =
      ∑ t ∈ Icc 1 x, ∑ d ∈ Icc 1 x, lacBlock L M ε t d / d := by
    intro x
    rw [sum_comm]
    refine sum_congr rfl fun d hd => ?_
    rw [lacWeight_eq_sum hLM (mem_Icc.mp hd).2, sum_div]
  have habs : ∀ x : ℕ, ∑ d ∈ Icc 1 x, |lacWeight L M ε d / d| ≤ 2 * ((1 / 8) / (1 - 1 / 8)) := by
    intro x
    calc ∑ d ∈ Icc 1 x, |lacWeight L M ε d / d|
        ≤ ∑ d ∈ Icc 1 x, ∑ t ∈ Icc 1 x, |lacBlock L M ε t d / d| := sum_le_sum fun d hd => by
          rw [lacWeight_eq_sum hLM (mem_Icc.mp hd).2, sum_div]
          exact abs_sum_le_sum_abs _ _
      _ = ∑ t ∈ Icc 1 x, ∑ d ∈ Icc 1 x, |lacBlock L M ε t d / d| := sum_comm
      _ ≤ ∑ t ∈ Icc 1 x, 2 * (1 / 8 : ℝ) ^ t := sum_le_sum fun t _ =>
          (sum_abs_windowDipole_div_le (lacAmp_pos t).le x).trans
            (by linarith [lacAmp_mul_lacW_le hLM hε t])
      _ = 2 * ∑ t ∈ Icc 1 x, (1 / 8 : ℝ) ^ t := by rw [mul_sum]
      _ ≤ 2 * ((1 / 8) ^ 1 / (1 - 1 / 8)) := by gcongr; exact sum_Icc_geom_le hr hr1 1 x
      _ = 2 * ((1 / 8) / (1 - 1 / 8)) := by norm_num
  have hsumm : Summable (fun d : ℕ => lacWeight L M ε d / d) := by
    refine Summable.of_norm (summable_of_sum_range_le (c := 2 * ((1 / 8) / (1 - 1 / 8)))
      (fun d => norm_nonneg _) fun D => ?_)
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · simp; norm_num
    · obtain ⟨x, rfl⟩ : ∃ x, D = x + 1 := ⟨D - 1, by omega⟩
      rw [sum_range_succ_eq_sum_Icc_one (f := fun d => ‖lacWeight L M ε d / d‖) (by simp)]
      exact habs x
  rw [hsumm.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
  have hsimp : ∀ x : ℕ, ∑ d ∈ range (x + 1), lacWeight L M ε d / d =
      ∑ d ∈ Icc 1 x, lacWeight L M ε d / d :=
    fun x => sum_range_succ_eq_sum_Icc_one (by simp) x
  simp_rw [hsimp]
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨t0, ht0⟩ : ∃ t0 : ℕ, (1 / 8 : ℝ) ^ t0 / (1 - 1 / 8) < δ := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).div_const (1 - 1 / 8 : ℝ)
    rw [zero_div] at h
    exact (h.eventually (gt_mem_nhds hδ)).exists
  refine ⟨lacN L (t0 + 1) + lacW M (t0 + 1), fun x hx => ?_⟩
  rw [Real.dist_eq, sub_zero, hdecomp]
  calc |∑ t ∈ Icc 1 x, ∑ d ∈ Icc 1 x, lacBlock L M ε t d / d|
      ≤ ∑ t ∈ Icc 1 x, |∑ d ∈ Icc 1 x, lacBlock L M ε t d / d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Icc (t0 + 1) x, (1 / 8 : ℝ) ^ t := by
        rw [← sum_filter_add_sum_filter_not (Icc 1 x) (· ≤ t0)]
        have h0 : ∑ t ∈ (Icc 1 x).filter (· ≤ t0), |∑ d ∈ Icc 1 x, lacBlock L M ε t d / d| = 0 := by
          refine sum_eq_zero fun t ht => ?_
          simp only [mem_filter, mem_Icc] at ht
          have hlt := lac_window_lt hLM ht.1.1 (show t < t0 + 1 by omega)
          rw [abs_eq_zero]
          exact sum_windowDipole_div_of_le _ (lacW_le hLM ht.1.1) (by omega)
        rw [h0, zero_add]
        refine (sum_le_sum fun t ht => ?_).trans
          (sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun _ _ _ => by positivity)
        · exact (abs_sum_windowDipole_div_le (lacAmp_pos t).le x).trans
            (lacAmp_mul_lacW_le hLM hε t)
        · simp only [mem_filter, mem_Icc, not_le] at ht ⊢; omega
    _ ≤ (1 / 8 : ℝ) ^ (t0 + 1) / (1 - 1 / 8) := sum_Icc_geom_le hr hr1 _ _
    _ ≤ (1 / 8 : ℝ) ^ t0 / (1 - 1 / 8) :=
        div_le_div_of_nonneg_right (pow_le_pow_of_le_one hr hr1.le (Nat.le_succ t0)) (by norm_num)
    _ < δ := ht0

/-- The prefix of the weight is the sum of the prefixes of its stages. -/
theorem weightCenteredPrefix_lacWeight (hLM : M + 3 ≤ L) {n T : ℕ} (hnT : n ≤ T) :
    weightCenteredPrefix (lacWeight L M ε) 0 n =
      ∑ t ∈ Icc 1 T, weightCenteredPrefix (lacBlock L M ε t) 0 n := by
  simp only [weightCenteredPrefix, zero_mul, sub_zero]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  exact (lacWeight_eq_sum hLM ((Nat.divisor_le hd).trans ((mem_Icc.mp hj).2.trans hnT))).symm

/-- The receiver energy of the weight is controlled by the weighted stage energies. -/
theorem weightPronicEnergy_lacWeight_le (hLM : M + 3 ≤ L) (T : ℕ) :
    weightPronicEnergy (lacWeight L M ε) 0 T ≤
      ∑ t ∈ Icc 1 T, (2 : ℝ) ^ t * weightPronicEnergy (lacBlock L M ε t) 0 T := by
  unfold weightPronicEnergy
  calc ∑ n ∈ Icc 1 T, weightCenteredPrefix (lacWeight L M ε) 0 n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
      = ∑ n ∈ Icc 1 T, (∑ t ∈ Icc 1 T, weightCenteredPrefix (lacBlock L M ε t) 0 n) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) :=
        sum_congr rfl fun n hn => by rw [weightCenteredPrefix_lacWeight hLM (mem_Icc.mp hn).2]
    _ ≤ ∑ n ∈ Icc 1 T, (∑ t ∈ Icc 1 T, (2 : ℝ) ^ t *
          weightCenteredPrefix (lacBlock L M ε t) 0 n ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) :=
        sum_le_sum fun n hn => by
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
          gcongr
          exact sq_sum_le_sum_two_pow_mul_sq _ T
    _ = ∑ t ∈ Icc 1 T, (2 : ℝ) ^ t * ∑ n ∈ Icc 1 T,
          weightCenteredPrefix (lacBlock L M ε t) 0 n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        simp_rw [sum_div, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun t _ => sum_congr rfl fun n _ => ?_
        ring

end LacunaryWeight

/-! ### The stage energies are summable and the rows diverge -/

section Stages

variable {L M Q : ℕ} {ε : ℝ}

/-- The cut `2^{Qt}` of stage `t`. -/
def lacX (Q t : ℕ) : ℕ := 2 ^ (Q * t)

theorem cast_lacN (t : ℕ) : (lacN L t : ℝ) = (2 : ℝ) ^ ((L : ℝ) * t) := by
  rw [lacN, cast_two_pow_eq_rpow]; push_cast; ring_nf

theorem cast_lacW (t : ℕ) : (lacW M t : ℝ) = (2 : ℝ) ^ ((M : ℝ) * t) := by
  rw [lacW, cast_two_pow_eq_rpow]; push_cast; ring_nf

theorem cast_lacX (t : ℕ) : (lacX Q t : ℝ) = (2 : ℝ) ^ ((Q : ℝ) * t) := by
  rw [lacX, cast_two_pow_eq_rpow]; push_cast; ring_nf

theorem two_rpow_mul_two_rpow (a b : ℝ) : (2 : ℝ) ^ a * (2 : ℝ) ^ b = (2 : ℝ) ^ (a + b) :=
  (Real.rpow_add two_pos a b).symm

theorem two_rpow_div_two_rpow (a b : ℝ) : (2 : ℝ) ^ a / (2 : ℝ) ^ b = (2 : ℝ) ^ (a - b) :=
  (Real.rpow_sub two_pos a b).symm

/-- `α² ≤ N^{-2-2ε}` in base-two exponents. -/
theorem lacAmp_sq_le (hε : 0 ≤ ε) (t : ℕ) :
    lacAmp L ε t ^ 2 ≤ (2 : ℝ) ^ ((-2 - 2 * ε) * ((L : ℝ) * t)) := by
  have hN0 : (0 : ℝ) < lacN L t := by exact_mod_cast lacN_pos (L := L) t
  have h1 : lacAmp L ε t ≤ (lacN L t : ℝ) ^ (-1 - ε) := by
    unfold lacAmp
    exact Real.rpow_le_rpow_of_nonpos hN0 (by push_cast; linarith) (by linarith)
  have h0 := (lacAmp_pos (L := L) (ε := ε) t).le
  calc lacAmp L ε t ^ 2 ≤ ((lacN L t : ℝ) ^ (-1 - ε)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (2 : ℝ) ^ ((-2 - 2 * ε) * ((L : ℝ) * t)) := by
        rw [cast_lacN, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        congr 1; push_cast; ring

/-- **The explicit stage bound.** For `t ≥ 1`, `2^t E_T(b_t) ≤ 514 (q₁^t + q₂^t)` with
`q₁ = 2^{1+3M+Q−L−(2+2ε)L}`, `q₂ = 2^{1+2M+2L−Q−(2+2ε)L}`. -/
theorem two_pow_mul_energy_lacBlock_le (hLM : M + 3 ≤ L) (hLQ : L + 1 ≤ Q)
    (hMQ : Q + M + 3 ≤ 2 * L) (hε : 0 ≤ ε) {t : ℕ} (ht : 1 ≤ t) (T : ℕ) :
    (2 : ℝ) ^ t * weightPronicEnergy (lacBlock L M ε t) 0 T ≤
      514 * (((2 : ℝ) ^ ((1 + 3 * M + Q - L : ℝ) - (2 + 2 * ε) * L)) ^ t +
        ((2 : ℝ) ^ ((1 + 2 * M + 2 * L - Q : ℝ) - (2 + 2 * ε) * L)) ^ t) := by
  set N := lacN L t with hNdef
  set w := lacW M t with hwdef
  set X := lacX Q t with hXdef
  set α := lacAmp L ε t with hαdef
  have hα0 : 0 ≤ α := (lacAmp_pos t).le
  have hN1 : 1 ≤ N := lacN_pos t
  have hwN : w ≤ N := lacW_le hLM ht
  have h8w : 8 * w ≤ N := lac_eight_le hLM ht
  have hw1 : 1 ≤ w := Nat.one_le_two_pow
  -- the cut lies beyond the window and below the doubling threshold
  have hNX : 2 * N ≤ X := by
    have : 2 ^ (L * t) * 2 ^ t ≤ 2 ^ (Q * t) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h2 : 2 ≤ 2 ^ t := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    show 2 * 2 ^ (L * t) ≤ 2 ^ (Q * t)
    calc 2 * 2 ^ (L * t) ≤ 2 ^ t * 2 ^ (L * t) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (L * t) * 2 ^ t := mul_comm _ _
      _ ≤ 2 ^ (Q * t) := this
  have hX : N + w ≤ X := by omega
  have h8wX : 8 * (w * X) ≤ N * N := by
    show 8 * (2 ^ (M * t) * 2 ^ (Q * t)) ≤ 2 ^ (L * t) * 2 ^ (L * t)
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hl : N ≤ 2 * (N - w + 1) := by omega
  have hXw : 2 * w * X ≤ (N - w + 1) ^ 2 := by nlinarith
  have hE := weightPronicEnergy_windowDipole_le hα0 hN1 hwN hX hXw T
  -- real bookkeeping
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hwr0 : (0 : ℝ) < w := by exact_mod_cast hw1
  have hwNr : (w : ℝ) ≤ N := by exact_mod_cast hwN
  have hXr0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlr : (N : ℝ) / 2 ≤ ((N - w + 1 : ℕ) : ℝ) := by
    have : (N : ℝ) ≤ 2 * ((N - w + 1 : ℕ) : ℝ) := by exact_mod_cast hl
    linarith
  have hl0 : (0 : ℝ) < ((N - w + 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - w + 1 by omega)
  have hdivX : ((X / (N - w + 1) : ℕ) : ℝ) ≤ 2 * X / N := by
    calc ((X / (N - w + 1) : ℕ) : ℝ) ≤ (X : ℝ) / ((N - w + 1 : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ (X : ℝ) / ((N : ℝ) / 2) := by gcongr
      _ = 2 * X / N := by field_simp
  have hinvl : 2 * (w : ℝ) / ((N - w + 1 : ℕ) : ℝ) ^ 2 ≤ 8 * w / (N : ℝ) ^ 2 := by
    calc 2 * (w : ℝ) / ((N - w + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * w / ((N : ℝ) / 2) ^ 2 := by gcongr
      _ = 8 * w / (N : ℝ) ^ 2 := by field_simp; ring
  have hNw2 : (N : ℝ) + w ≤ 2 * N := by linarith
  have hNw0 : (N : ℝ) ≤ (N : ℝ) + w := by linarith
  have hT1 : 2 * (α * (w : ℝ) ^ 2) ^ 2 * X / ((N : ℝ) + w) ^ 2 ≤ 2 * α ^ 2 * ((w : ℝ) ^ 3 * X / N) := by
    have hN0 : (0 : ℝ) < N := by linarith
    rw [div_le_iff₀ (by positivity)]
    have e : 2 * α ^ 2 * ((w : ℝ) ^ 3 * X / N) * ((N : ℝ) + w) ^ 2 =
        2 * α ^ 2 * (w : ℝ) ^ 3 * X * (((N : ℝ) + w) ^ 2 / N) := by ring
    rw [e]
    -- `w ≤ (N + w)²/N`
    have h1 : (w : ℝ) ≤ ((N : ℝ) + w) ^ 2 / N := by
      rw [le_div_iff₀ hN0]; nlinarith [mul_pos hN0 hwr0, sq_nonneg (N : ℝ), sq_nonneg (w : ℝ)]
    have h2 : 0 ≤ 2 * α ^ 2 * (w : ℝ) ^ 3 * X := by positivity
    calc 2 * (α * (w : ℝ) ^ 2) ^ 2 * X = 2 * α ^ 2 * (w : ℝ) ^ 3 * X * w := by ring
      _ ≤ 2 * α ^ 2 * (w : ℝ) ^ 3 * X * (((N : ℝ) + w) ^ 2 / N) :=
          mul_le_mul_of_nonneg_left h1 h2
  have hT2 : 2 * (2 * w * (α * ((N : ℝ) + w))) ^ 2 *
      (((X / (N - w + 1) : ℕ) : ℝ) * (2 * w / ((N - w + 1 : ℕ) : ℝ) ^ 2)) ≤
      512 * α ^ 2 * ((w : ℝ) ^ 3 * X / N) := by
    have hsq : (2 * w * (α * ((N : ℝ) + w))) ^ 2 ≤ (2 * w * (α * (2 * N))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by gcongr) 2
    have hprod : ((X / (N - w + 1) : ℕ) : ℝ) * (2 * w / ((N - w + 1 : ℕ) : ℝ) ^ 2) ≤
        (2 * X / N) * (8 * w / (N : ℝ) ^ 2) :=
      mul_le_mul hdivX hinvl (by positivity) (by positivity)
    have hN0 : (0 : ℝ) < N := by linarith
    calc 2 * (2 * w * (α * ((N : ℝ) + w))) ^ 2 *
          (((X / (N - w + 1) : ℕ) : ℝ) * (2 * w / ((N - w + 1 : ℕ) : ℝ) ^ 2))
        ≤ 2 * (2 * w * (α * (2 * N))) ^ 2 * ((2 * X / N) * (8 * w / (N : ℝ) ^ 2)) := by
          gcongr
      _ = 512 * α ^ 2 * ((w : ℝ) ^ 3 * X / N) := by field_simp; ring
  have hT3 : (2 * w * (α * ((N : ℝ) + w))) ^ 2 / X ≤ 16 * α ^ 2 * ((w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X) := by
    have hsq : (2 * w * (α * ((N : ℝ) + w))) ^ 2 ≤ (2 * w * (α * (2 * N))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by gcongr) 2
    calc (2 * w * (α * ((N : ℝ) + w))) ^ 2 / X ≤ (2 * w * (α * (2 * N))) ^ 2 / X := by gcongr
      _ = 16 * α ^ 2 * ((w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X) := by ring
  have hEb : weightPronicEnergy (lacBlock L M ε t) 0 T ≤
      514 * α ^ 2 * ((w : ℝ) ^ 3 * X / N + (w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X) := by
    have h1 : weightPronicEnergy (lacBlock L M ε t) 0 T ≤
        2 * α ^ 2 * ((w : ℝ) ^ 3 * X / N) + 512 * α ^ 2 * ((w : ℝ) ^ 3 * X / N) +
          16 * α ^ 2 * ((w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X) :=
      le_trans hE (add_le_add (add_le_add hT1 hT2) hT3)
    have hpos : 0 ≤ α ^ 2 * ((w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X) := by positivity
    linarith
  have hα2 := lacAmp_sq_le (L := L) (ε := ε) hε t
  -- the base-two exponents
  have hq1 : (2 : ℝ) ^ t * ((2 : ℝ) ^ ((-2 - 2 * ε) * ((L : ℝ) * t)) * ((w : ℝ) ^ 3 * X / N)) =
      ((2 : ℝ) ^ ((1 + 3 * M + Q - L : ℝ) - (2 + 2 * ε) * L)) ^ t := by
    rw [hwdef, hXdef, hNdef, cast_lacW, cast_lacX, cast_lacN, ← Real.rpow_natCast (2 : ℝ) t,
      ← Real.rpow_natCast ((2 : ℝ) ^ ((M : ℝ) * t)) 3, ← Real.rpow_mul (by norm_num),
      two_rpow_mul_two_rpow, two_rpow_div_two_rpow, two_rpow_mul_two_rpow,
      two_rpow_mul_two_rpow, ← two_rpow_mul_natCast]
    congr 1; push_cast; ring
  have hq2 : (2 : ℝ) ^ t * ((2 : ℝ) ^ ((-2 - 2 * ε) * ((L : ℝ) * t)) *
      ((w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X)) =
      ((2 : ℝ) ^ ((1 + 2 * M + 2 * L - Q : ℝ) - (2 + 2 * ε) * L)) ^ t := by
    rw [hwdef, hXdef, hNdef, cast_lacW, cast_lacX, cast_lacN, ← Real.rpow_natCast (2 : ℝ) t,
      ← Real.rpow_natCast ((2 : ℝ) ^ ((M : ℝ) * t)) 2,
      ← Real.rpow_natCast ((2 : ℝ) ^ ((L : ℝ) * t)) 2, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), two_rpow_mul_two_rpow, two_rpow_div_two_rpow,
      two_rpow_mul_two_rpow, two_rpow_mul_two_rpow, ← two_rpow_mul_natCast]
    congr 1; push_cast; ring
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have hb1 : 0 ≤ (w : ℝ) ^ 3 * X / N := by positivity
  have hb2 : 0 ≤ (w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X := by positivity
  calc (2 : ℝ) ^ t * weightPronicEnergy (lacBlock L M ε t) 0 T
      ≤ (2 : ℝ) ^ t * (514 * α ^ 2 * ((w : ℝ) ^ 3 * X / N + (w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X)) := by
        gcongr
    _ ≤ (2 : ℝ) ^ t * (514 * (2 : ℝ) ^ ((-2 - 2 * ε) * ((L : ℝ) * t)) *
          ((w : ℝ) ^ 3 * X / N + (w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X)) := by
        gcongr
    _ = 514 * ((2 : ℝ) ^ t * ((2 : ℝ) ^ ((-2 - 2 * ε) * ((L : ℝ) * t)) * ((w : ℝ) ^ 3 * X / N)) +
          (2 : ℝ) ^ t * ((2 : ℝ) ^ ((-2 - 2 * ε) * ((L : ℝ) * t)) *
            ((w : ℝ) ^ 2 * (N : ℝ) ^ 2 / X))) := by ring
    _ = _ := by rw [hq1, hq2]

end Stages

/-! ### The row that splits a dipole -/

section Rows

variable {L M : ℕ} {ε : ℝ}

/-- The row of horizon `N_t = 2^{Lt}` keeps the negative half of the stage-`t` dipole: its mean is
`−αw`. -/
theorem dyadicRowMean_lacWeight (hLM : M + 3 ≤ L) {t : ℕ} (ht : 1 ≤ t) :
    dyadicRowMean (lacWeight L M ε) (L * t) = -(lacAmp L ε t * lacW M t) := by
  rw [dyadicRowMean_eq]
  change ∑ d ∈ Icc 1 (lacN L t), lacWeight L M ε d / d = _
  rw [sum_congr rfl fun d hd => by rw [lacWeight_eq_sum hLM (mem_Icc.mp hd).2, sum_div], sum_comm]
  have htmem : t ∈ Icc 1 (lacN L t) := mem_Icc.mpr ⟨ht, by have := lac_add_le hLM ht; omega⟩
  rw [sum_eq_single t (fun s hs hst => ?_) (fun h => absurd htmem h)]
  · exact sum_windowDipole_div_center _ (lacW_le hLM ht)
  · have hs1 := (mem_Icc.mp hs).1
    rcases lt_or_gt_of_ne hst with h | h
    · have := lac_window_lt hLM hs1 h
      exact sum_windowDipole_div_of_le _ (lacW_le hLM hs1) (by omega)
    · have := lac_window_lt hLM ht h
      exact sum_eq_zero fun d hd => by
        rw [show lacBlock L M ε s d = 0 from windowDipole_eq_zero_of_not_mem (by
          simp only [mem_Icc] at hd; simp only [mem_Ioc, not_and, not_le]; omega), zero_div]

/-- Below its horizon the row is the weight plus the drift `αw · n`. -/
theorem weightCenteredPrefix_dyadicRow_lacWeight (hLM : M + 3 ≤ L) {t n : ℕ} (ht : 1 ≤ t)
    (hn : n ≤ lacN L t) :
    weightCenteredPrefix (dyadicRow (lacWeight L M ε) (L * t))
        (dyadicRowMean (lacWeight L M ε) (L * t)) n =
      weightCenteredPrefix (lacWeight L M ε) 0 n + lacAmp L ε t * lacW M t * n := by
  rw [dyadicRowMean_lacWeight hLM ht]
  simp only [weightCenteredPrefix]
  have h : ∑ j ∈ Icc 1 n, ∑ d ∈ j.divisors, dyadicRow (lacWeight L M ε) (L * t) d =
      ∑ j ∈ Icc 1 n, ∑ d ∈ j.divisors, lacWeight L M ε d :=
    sum_congr rfl fun j hj => sum_congr rfl fun d hd => by
      have : d ≤ 2 ^ (L * t) :=
        (Nat.divisor_le hd).trans ((mem_Icc.mp hj).2.trans hn)
      simp [dyadicRow, this]
  rw [h]
  ring

/-- **The drift energy of the splitting row.** If the weight is paid by `E₀`, the row of horizon
`N_t` has energy at least `(αw)² N_t / 4 − E₀` at the cutoff `N_t`. -/
theorem rowEnergy_lacWeight_ge (hLM : M + 3 ≤ L) {t : ℕ} (ht : 1 ≤ t) {E₀ : ℝ}
    (hE₀ : ∀ T, weightPronicEnergy (lacWeight L M ε) 0 T ≤ E₀) :
    (lacAmp L ε t * lacW M t) ^ 2 * lacN L t / 4 - E₀ ≤
      weightPronicEnergy (dyadicRow (lacWeight L M ε) (L * t))
        (dyadicRowMean (lacWeight L M ε) (L * t)) (lacN L t) := by
  set τ := lacAmp L ε t * lacW M t
  set A := fun n => weightCenteredPrefix (lacWeight L M ε) 0 n
  have hcell : ∀ n ∈ Icc 1 (lacN L t),
      τ ^ 2 / 4 - A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        weightCenteredPrefix (dyadicRow (lacWeight L M ε) (L * t))
          (dyadicRowMean (lacWeight L M ε) (L * t)) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [weightCenteredPrefix_dyadicRow_lacWeight hLM ht (mem_Icc.mp hn).2]
    have hp : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hp, sub_mul, div_mul_cancel₀ _ hp.ne']
    nlinarith [sq_nonneg (2 * A n + τ * n), sq_nonneg τ]
  calc τ ^ 2 * lacN L t / 4 - E₀
      ≤ ∑ n ∈ Icc 1 (lacN L t), τ ^ 2 / 4 - weightPronicEnergy (lacWeight L M ε) 0 (lacN L t) := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        linarith [hE₀ (lacN L t)]
    _ = ∑ n ∈ Icc 1 (lacN L t), (τ ^ 2 / 4 - A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        rw [sum_sub_distrib, weightPronicEnergy]
    _ ≤ _ := by rw [weightPronicEnergy]; exact sum_le_sum hcell

/-- The drift energy grows like `2^{(2M − (1+2ε)L)t}`. -/
theorem drift_lacWeight_eq {t : ℕ} :
    (lacAmp L ε t * lacW M t) ^ 2 * lacN L t / 4 =
      (2 : ℝ) ^ (-2 - 2 * ε) / 4 * ((2 : ℝ) ^ ((2 * M + L : ℝ) - (2 + 2 * ε) * L)) ^ t := by
  unfold lacAmp
  rw [mul_pow, ← Real.rpow_natCast (((2 * lacN L t : ℕ) : ℝ) ^ (-1 - ε)) 2,
    ← Real.rpow_mul (by positivity)]
  push_cast
  rw [cast_lacN, cast_lacW, ← Real.rpow_natCast ((2 : ℝ) ^ ((M : ℝ) * t)) 2,
    ← Real.rpow_mul (by norm_num), show (2 : ℝ) * (2 : ℝ) ^ ((L : ℝ) * t) =
      (2 : ℝ) ^ (1 + (L : ℝ) * t) by rw [Real.rpow_add two_pos, Real.rpow_one],
    ← Real.rpow_mul (by norm_num), ← two_rpow_mul_natCast, two_rpow_mul_two_rpow,
    two_rpow_mul_two_rpow]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm ((2 : ℝ) ^ (-2 - 2 * ε)) _,
    mul_assoc ((4 : ℝ)⁻¹) ((2 : ℝ) ^ (-2 - 2 * ε)), two_rpow_mul_two_rpow, mul_comm ((4 : ℝ)⁻¹)]
  congr 2
  push_cast
  ring

end Rows

/-! ### The exponents -/

/-- For every `0 ≤ ε < 1/2` there are exponents `L, M, Q` making the stage energies summable
(`3M + Q + 1 < (3+2ε)L`, `2M + 1 < Q + 2εL`) while the splitting rows diverge (`(1+2ε)L < 2M`). -/
theorem exists_lacExponents {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ∃ L M Q : ℕ, M + 3 ≤ L ∧ L + 1 ≤ Q ∧ Q + M + 3 ≤ 2 * L ∧
      (1 + 2 * ε) * L < 2 * M ∧ (3 * M + Q + 1 : ℝ) < (3 + 2 * ε) * L ∧
      (2 * M + 1 : ℝ) < Q + 2 * ε * L := by
  set x := (1 + 2 * ε) / 2 with hx
  have hgap : 0 < 1 / 2 - ε := by linarith
  set L := ⌈26 / (1 - 2 * ε)⌉₊ with hLdef
  have hL : 13 ≤ (1 / 2 - ε) * L := by
    have h1 : 26 / (1 - 2 * ε) ≤ (L : ℝ) := Nat.le_ceil _
    have h2 : (0 : ℝ) < 1 - 2 * ε := by linarith
    rw [div_le_iff₀ h2] at h1
    linarith
  set M := ⌈x * L⌉₊ + 1 with hMdef
  have hM1 : x * L + 1 ≤ (M : ℝ) := by
    have := Nat.le_ceil (x * L); push_cast [hMdef]; linarith
  have hM2 : (M : ℝ) < x * L + 2 := by
    have hxL : 0 ≤ x * L := by positivity
    have := Nat.ceil_lt_add_one hxL; push_cast [hMdef]; linarith
  refine ⟨L, M, L + 6, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · have : (M : ℝ) + 3 ≤ L := by nlinarith
    exact_mod_cast this
  · have : ((L + 6 : ℕ) : ℝ) + M + 3 ≤ 2 * L := by push_cast; nlinarith
    exact_mod_cast this
  · nlinarith
  · push_cast; nlinarith
  · push_cast; nlinarith

/-! ### The capstone -/

/-- **Below half damping the horizon limit does not commute with the receiver.** For every
`0 ≤ ε < 1/2` there is a weight in `𝒞(1, ε)` with mean zero whose receiver is bounded while the
receivers of its dyadic rows are not uniformly bounded. -/
theorem exists_paid_weight_with_unbounded_rows {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ∃ c : ℕ → ℝ, DampedClass 1 ε c ∧ HasSum (fun d : ℕ => c d / d) 0 ∧ ReceiverBounded c ∧
      ∀ E : ℝ, ∃ J T : ℕ, E < weightPronicEnergy (dyadicRow c J) (dyadicRowMean c J) T := by
  obtain ⟨L, M, Q, hLM, hLQ, hMQ, hgrow, hq1, hq2⟩ := exists_lacExponents hε0 hε
  set q₁ := (2 : ℝ) ^ ((1 + 3 * M + Q - L : ℝ) - (2 + 2 * ε) * L)
  set q₂ := (2 : ℝ) ^ ((1 + 2 * M + 2 * L - Q : ℝ) - (2 + 2 * ε) * L)
  have hq₁ : q₁ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hq₂ : q₂ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hq₁0 : 0 ≤ q₁ := (Real.rpow_pos_of_pos two_pos _).le
  have hq₂0 : 0 ≤ q₂ := (Real.rpow_pos_of_pos two_pos _).le
  set E₀ := 514 * (q₁ ^ 1 / (1 - q₁) + q₂ ^ 1 / (1 - q₂)) with hE₀def
  have hE : ∀ T, weightPronicEnergy (lacWeight L M ε) 0 T ≤ E₀ := fun T => by
    refine (weightPronicEnergy_lacWeight_le hLM T).trans ?_
    calc ∑ t ∈ Icc 1 T, (2 : ℝ) ^ t * weightPronicEnergy (lacBlock L M ε t) 0 T
        ≤ ∑ t ∈ Icc 1 T, 514 * (q₁ ^ t + q₂ ^ t) := sum_le_sum fun t ht =>
          two_pow_mul_energy_lacBlock_le hLM hLQ hMQ hε0 (mem_Icc.mp ht).1 T
      _ = 514 * (∑ t ∈ Icc 1 T, q₁ ^ t + ∑ t ∈ Icc 1 T, q₂ ^ t) := by
          rw [← mul_sum, sum_add_distrib]
      _ ≤ E₀ := by
          rw [hE₀def]
          gcongr
          · exact sum_Icc_geom_le hq₁0 hq₁ 1 T
          · exact sum_Icc_geom_le hq₂0 hq₂ 1 T
  have hmean := hasSum_lacWeight_div hLM hε0 (L := L) (M := M) (ε := ε)
  refine ⟨lacWeight L M ε, dampedClass_lacWeight hLM hε0, hmean,
    ⟨E₀, fun T => by rw [hmean.tsum_eq]; exact hE T⟩, fun E => ?_⟩
  -- the drift energy of the splitting rows is unbounded
  set q₃ := (2 : ℝ) ^ ((2 * M + L : ℝ) - (2 + 2 * ε) * L)
  have hq₃ : 1 < q₃ := Real.one_lt_rpow one_lt_two (by linarith)
  have hc : 0 < (2 : ℝ) ^ (-2 - 2 * ε) / 4 := by positivity
  have hdiv := (tendsto_pow_atTop_atTop_of_one_lt hq₃).const_mul_atTop hc
  obtain ⟨t, ht, ht1⟩ := ((hdiv.eventually_gt_atTop (E + E₀)).and (eventually_ge_atTop 1)).exists
  refine ⟨L * t, lacN L t, ?_⟩
  have hrow := rowEnergy_lacWeight_ge hLM ht1 hE (ε := ε)
  rw [drift_lacWeight_eq] at hrow
  linarith

/-- **The horizon limit commutes with the receiver exactly from half damping on.** For every
`ε ≥ 0`: the dyadic rows of every weight of `𝒞(1, ε)` are uniformly paid exactly when the weight is
paid, if and only if `ε ≥ 1/2`. -/
theorem horizonLimit_commutes_with_receiver_iff {ε : ℝ} (hε0 : 0 ≤ ε) :
    (∀ c : ℕ → ℝ, DampedClass 1 ε c →
      ((∃ E : ℝ, ∀ J T : ℕ, weightPronicEnergy (dyadicRow c J) (dyadicRowMean c J) T ≤ E) ↔
        ReceiverBounded c)) ↔ 1 / 2 ≤ ε := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc, -, hpaid, hrows⟩ := exists_paid_weight_with_unbounded_rows hε0 hlt
    obtain ⟨E, hE⟩ := (h c hc).mpr hpaid
    obtain ⟨J, T, hJT⟩ := hrows E
    exact absurd (hE J T) (not_le.mpr hJT)
  · intro hε c hc
    exact rows_bounded_iff_receiverBounded_of_half_le hε hc

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
