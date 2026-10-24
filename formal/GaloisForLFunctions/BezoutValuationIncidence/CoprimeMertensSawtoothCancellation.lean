import GaloisForLFunctions.BezoutValuationIncidence.TheCofinalMobiusProfileIsAsymptoticallyLinear
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMoebiusHarmonicSumsDecay

/-!
# Coprime Möbius sums against sawtooth weights

For `f ≥ 1` let `M_f(s) = Σ_{b ≤ s, (b,f)=1} μ(b)` (`coprimeMoebiusSum`) and
`m_f(s) = Σ_{b ≤ s, (b,f)=1} μ(b)/b`, and let `Π(f) = ∏_{p ∣ f}(1 - p^{-3/4})^{-1}`.

* `exists_abs_coprimeMoebiusHarmonicSum_le_four`: `|m_f(s)| ≤ C Π(f) (1 + log s)^{-4}`;
* `exists_abs_coprimeMoebiusSum_le`: `|M_f(s)| ≤ C Π(f) s (1 + log s)^{-4}`;
* `exists_abs_sum_coprime_moebius_fract_le`: for `t = ⌊M/c⌋ ≥ 256` and every `X`,
  `|Σ_{b ≤ X, (b,f)=1} μ(b) {M/(cb)}| ≤ C Π(f) t (1 + log t)^{-3} + √t`.

Mechanism. The harmonic decay is the Rankin-kernel bound of `CoprimeMoebiusHarmonicSumsDecay` with
the fourth logarithmic power kept; Abel summation moves it to `M_f`. On a piece `⌊t/b⌋ = n` the
sawtooth `{M/(cb)} = M/(cb) − n` decreases in `b`, so Abel summation bounds the piece by the
oscillation of `M_f` on it (`abs_sum_Ioc_mul_le_of_antitone`). The pieces `n ≤ √t` carry
`Π(f) t/(1 + log t)³`, the integers `b ≤ √t` carry `√t`, and the range `b > t`, where the sawtooth is
`M/(cb)`, is `M/c · (m_f(X) − m_f(t))`.
-/

open Finset Filter Topology ArithmeticFunction

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### Coprime harmonic sums with the fourth logarithmic power -/

/-- `|m_f(Y)| ≤ 2²⁰ C Π(f) (1 + log Y)^{-4}` from `|m(N)| ≤ C (1 + log N)^{-4}`. -/
theorem abs_coprimeMoebiusHarmonicSum_le_four_of {C : ℝ}
    (hC : ∀ N : ℕ, 1 ≤ N → |moebiusHarmonicSum N| ≤ C / (1 + Real.log N) ^ 4)
    {f : ℕ} (hf : f ≠ 0) {Y : ℕ} (hY : 1 ≤ Y) :
    |coprimeMoebiusHarmonicSum f Y| ≤ 1048576 * C * rankinProduct f / (1 + Real.log Y) ^ 4 := by
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl
    rw [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
    exact (abs_nonneg _).trans h1
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hYR
  have hLY : 0 < (1 + Real.log Y) ^ 4 := by positivity
  rw [coprimeMoebiusHarmonicSum_eq_kernel hf]
  have hpt : ∀ d ∈ Icc 1 Y, |smoothHarmonicKernel f d * moebiusHarmonicSum (Y / d)| ≤
      1048576 * C / (1 + Real.log Y) ^ 4 * smoothHarmonicKernelRankin f d := by
    intro d hd
    obtain ⟨hd1, hdY⟩ := mem_Icc.mp hd
    have hq : 1 ≤ Y / d := (Nat.one_le_div_iff (by omega)).mpr hdY
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hqR : (1 : ℝ) ≤ ((Y / d : ℕ) : ℝ) := by exact_mod_cast hq
    have hlq : 0 ≤ Real.log ((Y / d : ℕ) : ℝ) := Real.log_nonneg hqR
    have hld : 0 ≤ Real.log d := Real.log_nonneg hdR
    have hsplit := one_add_log_le_two_mul_log_div hd1 hdY
    have hm := hC (Y / d) hq
    have hβ := smoothHarmonicKernel_nonneg f d
    have hlog4 := one_add_log_pow_four_le_rpow_quarter hdR
    rw [abs_mul, abs_of_nonneg hβ, smoothHarmonicKernelRankin_apply]
    have hstep : C / (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4 ≤
        16 * C * (1 + Real.log d) ^ 4 / (1 + Real.log Y) ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) hLY]
      have hA : (1 + Real.log Y) ^ 4 ≤
          (2 * (1 + Real.log ((Y / d : ℕ) : ℝ)) * (1 + Real.log d)) ^ 4 :=
        pow_le_pow_left₀ (by linarith) hsplit 4
      have hA' : (2 * (1 + Real.log ((Y / d : ℕ) : ℝ)) * (1 + Real.log d)) ^ 4 =
          16 * (1 + Real.log d) ^ 4 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4 := by ring
      calc C * (1 + Real.log Y) ^ 4
          ≤ C * (16 * (1 + Real.log d) ^ 4 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4) :=
            mul_le_mul_of_nonneg_left (hA.trans hA'.le) hC0
        _ = 16 * C * (1 + Real.log d) ^ 4 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4 := by ring
    calc smoothHarmonicKernel f d * |moebiusHarmonicSum (Y / d)|
        ≤ smoothHarmonicKernel f d * (16 * C * (1 + Real.log d) ^ 4 / (1 + Real.log Y) ^ 4) :=
          mul_le_mul_of_nonneg_left (hm.trans hstep) hβ
      _ ≤ smoothHarmonicKernel f d *
            (16 * C * (65536 * (d : ℝ) ^ (1 / 4 : ℝ)) / (1 + Real.log Y) ^ 4) := by gcongr
      _ = 1048576 * C / (1 + Real.log Y) ^ 4 *
            (smoothHarmonicKernel f d * (d : ℝ) ^ (1 / 4 : ℝ)) := by ring
  calc |∑ d ∈ Icc 1 Y, smoothHarmonicKernel f d * moebiusHarmonicSum (Y / d)|
      ≤ ∑ d ∈ Icc 1 Y, |smoothHarmonicKernel f d * moebiusHarmonicSum (Y / d)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 Y, 1048576 * C / (1 + Real.log Y) ^ 4 * smoothHarmonicKernelRankin f d :=
        sum_le_sum hpt
    _ = 1048576 * C / (1 + Real.log Y) ^ 4 * ∑ d ∈ Icc 1 Y, smoothHarmonicKernelRankin f d := by
        rw [mul_sum]
    _ ≤ 1048576 * C / (1 + Real.log Y) ^ 4 * rankinProduct f :=
        mul_le_mul_of_nonneg_left (sum_Icc_smoothHarmonicKernelRankin_le f Y) (by positivity)
    _ = _ := by ring

theorem exists_abs_coprimeMoebiusHarmonicSum_le_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℕ, f ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |coprimeMoebiusHarmonicSum f Y| ≤ C * rankinProduct f / (1 + Real.log Y) ^ 4 := by
  obtain ⟨C, hC⟩ := exists_abs_moebiusHarmonicSum_le
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl
    rw [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
    exact (abs_nonneg _).trans h1
  exact ⟨1048576 * C, by positivity,
    fun f hf Y hY => abs_coprimeMoebiusHarmonicSum_le_four_of hC hf hY⟩

/-! ### Plain coprime Möbius sums -/

/-- `M_f(s) = Σ_{b ≤ s, (b,f)=1} μ(b)`. -/
def coprimeMoebiusSum (f s : ℕ) : ℝ :=
  ∑ b ∈ Icc 1 s, if Nat.Coprime b f then (moebius b : ℝ) else 0

/-- Abel summation: `Σ_{b ≤ s} b h(b) = s H(s) − Σ_{j < s} H(j)` with `H(j) = Σ_{b ≤ j} h(b)`. -/
theorem sum_Icc_natCast_mul_eq (h : ℕ → ℝ) (s : ℕ) :
    ∑ b ∈ Icc 1 s, (b : ℝ) * h b =
      s * ∑ b ∈ Icc 1 s, h b - ∑ j ∈ range s, ∑ b ∈ Icc 1 j, h b := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih,
      Finset.sum_range_succ]
    push_cast
    ring

theorem coprimeMoebiusSum_eq (f s : ℕ) :
    coprimeMoebiusSum f s =
      s * coprimeMoebiusHarmonicSum f s - ∑ j ∈ range s, coprimeMoebiusHarmonicSum f j := by
  have h := sum_Icc_natCast_mul_eq
    (fun b => if Nat.Coprime b f then (moebius b : ℝ) / b else 0) s
  unfold coprimeMoebiusSum coprimeMoebiusHarmonicSum
  rw [← h]
  refine sum_congr rfl fun b hb => ?_
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hb).1; omega)
  split_ifs
  · field_simp
  · rw [mul_zero]

/-- `√s (1 + log s)⁴ ≤ 2¹⁶ s`. -/
theorem sqrt_mul_one_add_log_pow_four_le {s : ℝ} (hs : 1 ≤ s) :
    Real.sqrt s * (1 + Real.log s) ^ 4 ≤ 65536 * s := by
  have hs0 : 0 < s := by linarith
  have h4 := one_add_log_pow_four_le_rpow_quarter hs
  have hq : s ^ (1 / 4 : ℝ) ≤ Real.sqrt s := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0.le
  have hsq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  calc Real.sqrt s * (1 + Real.log s) ^ 4 ≤ Real.sqrt s * (65536 * s ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left h4 hsq0
    _ ≤ Real.sqrt s * (65536 * Real.sqrt s) := by gcongr
    _ = 65536 * (Real.sqrt s * Real.sqrt s) := by ring
    _ = 65536 * s := by rw [hsq]

/-- `Σ_{j < s} (1 + log j)^{-4} ≤ 2¹⁷ s (1 + log s)^{-4}` (the `j = 0` term is `1`). -/
theorem sum_range_inv_one_add_log_pow_four_le {s : ℕ} (hs : 1 ≤ s) :
    ∑ j ∈ range s, ((1 + Real.log j) ^ 4)⁻¹ ≤ 131088 * s / (1 + Real.log s) ^ 4 := by
  classical
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hls : 0 ≤ Real.log s := Real.log_nonneg hsR
  have hL : 0 < (1 + Real.log s) ^ 4 := by positivity
  have hle1 : ∀ j : ℕ, ((1 + Real.log j) ^ 4)⁻¹ ≤ 1 := by
    intro j
    have : 0 ≤ Real.log j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · exact Real.log_nonneg (by exact_mod_cast hj)
    have h1 : 1 ≤ (1 + Real.log j) ^ 4 := one_le_pow₀ (by linarith)
    exact inv_le_one_of_one_le₀ h1
  rw [← sum_filter_add_sum_filter_not (range s) (fun j => j * j < s)]
  have hsmall : ∑ j ∈ (range s).filter (fun j => j * j < s), ((1 + Real.log j) ^ 4)⁻¹ ≤
      2 * Real.sqrt s := by
    have hsub : (range s).filter (fun j => j * j < s) ⊆ range (Nat.sqrt s + 1) := by
      intro j hj
      simp only [mem_filter, mem_range] at hj ⊢
      exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr hj.2.le)
    calc _ ≤ ∑ j ∈ (range s).filter (fun j => j * j < s), (1 : ℝ) := sum_le_sum fun j _ => hle1 j
      _ = (#((range s).filter (fun j => j * j < s)) : ℝ) := by simp
      _ ≤ (Nat.sqrt s + 1 : ℕ) := by exact_mod_cast (card_le_card hsub).trans (card_range _).le
      _ ≤ 2 * Real.sqrt s := by
          have h1 : (1 : ℝ) ≤ Real.sqrt s := by rw [Real.one_le_sqrt]; exact hsR
          have h2 : (Nat.sqrt s : ℝ) ≤ Real.sqrt s := Real.nat_sqrt_le_real_sqrt
          push_cast
          linarith
  have hlarge : ∑ j ∈ (range s).filter (fun j => ¬ j * j < s), ((1 + Real.log j) ^ 4)⁻¹ ≤
      16 * s / (1 + Real.log s) ^ 4 := by
    have hpt : ∀ j ∈ (range s).filter (fun j => ¬ j * j < s),
        ((1 + Real.log j) ^ 4)⁻¹ ≤ 16 / (1 + Real.log s) ^ 4 := by
      intro j hj
      have hj2 : s ≤ j * j := by simp only [mem_filter] at hj; omega
      have hj1 : 1 ≤ j := by nlinarith
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have hlj : Real.log s ≤ 2 * Real.log j := by
        have : (s : ℝ) ≤ (j : ℝ) ^ 2 := by exact_mod_cast (by nlinarith : s ≤ j ^ 2)
        calc Real.log s ≤ Real.log ((j : ℝ) ^ 2) := Real.log_le_log (by linarith) this
          _ = 2 * Real.log j := by rw [Real.log_pow]; norm_num
      have hlj0 : 0 ≤ Real.log j := Real.log_nonneg hjR
      have hbase : (1 + Real.log s) / 2 ≤ 1 + Real.log j := by linarith
      have hpow : ((1 + Real.log s) / 2) ^ 4 ≤ (1 + Real.log j) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbase 4
      rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
      calc (1 + Real.log s) ^ 4 / 16 = ((1 + Real.log s) / 2) ^ 4 := by ring
        _ ≤ (1 + Real.log j) ^ 4 := hpow
    calc _ ≤ ∑ j ∈ (range s).filter (fun j => ¬ j * j < s), 16 / (1 + Real.log s) ^ 4 :=
          sum_le_sum hpt
      _ = (#((range s).filter (fun j => ¬ j * j < s)) : ℝ) * (16 / (1 + Real.log s) ^ 4) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (s : ℝ) * (16 / (1 + Real.log s) ^ 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (card_filter_le _ _).trans (card_range s).le
      _ = 16 * s / (1 + Real.log s) ^ 4 := by ring
  have hsqrt : 2 * Real.sqrt s ≤ 131072 * s / (1 + Real.log s) ^ 4 := by
    rw [le_div_iff₀ hL]
    have := sqrt_mul_one_add_log_pow_four_le hsR
    linarith
  calc _ ≤ 2 * Real.sqrt s + 16 * s / (1 + Real.log s) ^ 4 := add_le_add hsmall hlarge
    _ ≤ 131072 * s / (1 + Real.log s) ^ 4 + 16 * s / (1 + Real.log s) ^ 4 := by linarith
    _ = 131088 * s / (1 + Real.log s) ^ 4 := by ring

/-- **Coprime Mertens bound.** `|M_f(s)| ≤ 131089 C Π(f) s (1 + log s)^{-4}`. -/
theorem abs_coprimeMoebiusSum_le_of {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ f : ℕ, f ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |coprimeMoebiusHarmonicSum f Y| ≤ C * rankinProduct f / (1 + Real.log Y) ^ 4)
    {f : ℕ} (hf : f ≠ 0) {s : ℕ} (hs : 1 ≤ s) :
    |coprimeMoebiusSum f s| ≤ 131089 * C * rankinProduct f * s / (1 + Real.log s) ^ 4 := by
  have hP := one_le_rankinProduct f
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hls : 0 ≤ Real.log s := Real.log_nonneg hsR
  have hL : 0 < (1 + Real.log s) ^ 4 := by positivity
  have hall : ∀ j : ℕ, |coprimeMoebiusHarmonicSum f j| ≤
      C * rankinProduct f * ((1 + Real.log j) ^ 4)⁻¹ := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have h0 : coprimeMoebiusHarmonicSum f 0 = 0 := by simp [coprimeMoebiusHarmonicSum]
      rw [h0, abs_zero]
      exact mul_nonneg (mul_nonneg hC0 (by linarith)) (inv_nonneg.mpr (by positivity))
    · rw [← div_eq_mul_inv]; exact hC f hf j hj
  have hsum := sum_range_inv_one_add_log_pow_four_le hs
  rw [coprimeMoebiusSum_eq]
  calc |(s : ℝ) * coprimeMoebiusHarmonicSum f s - ∑ j ∈ range s, coprimeMoebiusHarmonicSum f j|
      ≤ s * |coprimeMoebiusHarmonicSum f s| + ∑ j ∈ range s, |coprimeMoebiusHarmonicSum f j| := by
        refine (abs_sub _ _).trans (add_le_add ?_ (abs_sum_le_sum_abs _ _))
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ s * (C * rankinProduct f / (1 + Real.log s) ^ 4) +
          ∑ j ∈ range s, C * rankinProduct f * ((1 + Real.log j) ^ 4)⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_left (hC f hf s hs) (Nat.cast_nonneg _))
          (sum_le_sum fun j _ => hall j)
    _ = C * rankinProduct f * s / (1 + Real.log s) ^ 4 +
          C * rankinProduct f * ∑ j ∈ range s, ((1 + Real.log j) ^ 4)⁻¹ := by
        rw [mul_sum]; ring
    _ ≤ C * rankinProduct f * s / (1 + Real.log s) ^ 4 +
          C * rankinProduct f * (131088 * s / (1 + Real.log s) ^ 4) := by
        gcongr
    _ = 131089 * C * rankinProduct f * s / (1 + Real.log s) ^ 4 := by ring

theorem exists_abs_coprimeMoebiusSum_le :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ f : ℕ, f ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |coprimeMoebiusHarmonicSum f Y| ≤ K * rankinProduct f / (1 + Real.log Y) ^ 4) ∧
      ∀ f : ℕ, f ≠ 0 → ∀ s : ℕ, 1 ≤ s →
        |coprimeMoebiusSum f s| ≤ K * rankinProduct f * s / (1 + Real.log s) ^ 4 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_coprimeMoebiusHarmonicSum_le_four
  refine ⟨131089 * C, by positivity, fun f hf Y hY => ?_,
    fun f hf s hs => abs_coprimeMoebiusSum_le_of hC0 hC hf hs⟩
  have hP := one_le_rankinProduct f
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hYR
  refine (hC f hf Y hY).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

/-! ### Abel summation against monotone weights -/

/-- **Abel bound.** If `0 ≤ w ≤ 1` decreases on `(u, v]` and every partial sum `Σ_{u < n ≤ s} a(n)`,
`u ≤ s ≤ v`, has modulus at most `T`, then `|Σ_{u < n ≤ v} a(n) w(n)| ≤ T`. -/
theorem abs_sum_Ioc_mul_le_of_antitone {a w : ℕ → ℝ} {u v : ℕ} {T : ℝ} (hT0 : 0 ≤ T)
    (hw0 : ∀ n ∈ Ioc u v, 0 ≤ w n) (hw1 : ∀ n ∈ Ioc u v, w n ≤ 1)
    (hanti : ∀ n, u < n → n < v → w (n + 1) ≤ w n)
    (hT : ∀ s, u ≤ s → s ≤ v → |∑ n ∈ Ioc u s, a n| ≤ T) :
    |∑ n ∈ Ioc u v, a n * w n| ≤ T := by
  rcases Nat.lt_or_ge u v with huv | huv
  · have key : ∀ k, u + 1 + k ≤ v → ∃ R : ℝ, ∑ n ∈ Ioc u (u + 1 + k), a n * w n =
        (∑ n ∈ Ioc u (u + 1 + k), a n) * w (u + 1 + k) + R ∧
        |R| ≤ T * (w (u + 1) - w (u + 1 + k)) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨0, ?_, by simp⟩
        rw [add_zero, Nat.Ioc_succ_singleton, sum_singleton, sum_singleton, add_zero]
      | succ k ih =>
        intro hk
        obtain ⟨R, hR, hRb⟩ := ih (by omega)
        refine ⟨R + (∑ n ∈ Ioc u (u + 1 + k), a n) * (w (u + 1 + k) - w (u + 1 + k + 1)), ?_, ?_⟩
        · rw [show u + 1 + (k + 1) = u + 1 + k + 1 by ring,
            Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega), hR]
          ring
        · have hA := hT (u + 1 + k) (by omega) (by omega)
          have hd : 0 ≤ w (u + 1 + k) - w (u + 1 + k + 1) := by
            have := hanti (u + 1 + k) (by omega) (by omega); linarith
          rw [show u + 1 + (k + 1) = u + 1 + k + 1 by ring]
          calc |R + (∑ n ∈ Ioc u (u + 1 + k), a n) * (w (u + 1 + k) - w (u + 1 + k + 1))|
              ≤ |R| + |∑ n ∈ Ioc u (u + 1 + k), a n| * (w (u + 1 + k) - w (u + 1 + k + 1)) := by
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_of_nonneg hd]
            _ ≤ T * (w (u + 1) - w (u + 1 + k)) + T * (w (u + 1 + k) - w (u + 1 + k + 1)) :=
                add_le_add hRb (mul_le_mul_of_nonneg_right hA hd)
            _ = T * (w (u + 1) - w (u + 1 + k + 1)) := by ring
    obtain ⟨R, hR, hRb⟩ := key (v - (u + 1)) (by omega)
    rw [show u + 1 + (v - (u + 1)) = v by omega] at hR hRb
    have hAv := hT v huv.le le_rfl
    have hwv0 := hw0 v (mem_Ioc.mpr ⟨huv, le_rfl⟩)
    have hwu1 := hw1 (u + 1) (mem_Ioc.mpr ⟨by omega, by omega⟩)
    rw [hR]
    calc |(∑ n ∈ Ioc u v, a n) * w v + R| ≤ |∑ n ∈ Ioc u v, a n| * w v + |R| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hwv0]
      _ ≤ T * w v + T * (w (u + 1) - w v) := add_le_add (mul_le_mul_of_nonneg_right hAv hwv0) hRb
      _ = T * w (u + 1) := by ring
      _ ≤ T * 1 := mul_le_mul_of_nonneg_left hwu1 hT0
      _ = T := mul_one T
  · rw [Ioc_eq_empty (by omega), sum_empty, abs_zero]; exact hT0

/-! ### The sawtooth -/

/-- On the piece `⌊⌊M/c⌋/b⌋ = n`: `{M/(cb)} = M/(cb) − n`. -/
theorem fract_div_eq_of_div_div_eq {M c b n : ℕ} (hc : 1 ≤ c) (hb : 1 ≤ b) (h : M / c / b = n) :
    Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ)) = (M : ℝ) / ((c * b : ℕ) : ℝ) - n := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hcb : 0 < c * b := Nat.mul_pos hc hb
  have hdiv : M / (c * b) = n := by rw [← Nat.div_div_eq_div_mul]; exact h
  have hmod := Nat.mod_add_div M (c * b)
  rw [hdiv] at hmod
  have hcbR : ((c * b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hcb.ne'
  have hmodR : ((M % (c * b) : ℕ) : ℝ) = (M : ℝ) - ((c * b : ℕ) : ℝ) * n := by
    have : ((M % (c * b) : ℕ) : ℝ) + ((c * b : ℕ) : ℝ) * n = M := by exact_mod_cast hmod
    linarith
  rw [hmodR, sub_div, mul_div_cancel_left₀ _ hcbR]

/-- The pieces of `⌊t/b⌋`: for `1 ≤ n`, `{b ≤ X : b ≤ t, ⌊t/b⌋ = n} = (⌊t/(n+1)⌋, min(⌊t/n⌋, X)]`. -/
theorem filter_div_eq_Ioc_min {t X n : ℕ} (hn : 1 ≤ n) :
    (Icc 1 X).filter (fun b => b ≤ t ∧ t / b = n) = Ioc (t / (n + 1)) (min (t / n) X) := by
  have key := filter_div_eq_Ioc (t := t) hn
  ext b
  have hb : b ∈ (Icc 1 t).filter (fun g => t / g = n) ↔ b ∈ Ioc (t / (n + 1)) (t / n) := by
    rw [key]
  simp only [mem_filter, mem_Icc, mem_Ioc, le_min_iff] at hb ⊢
  constructor
  · rintro ⟨⟨h1, hX⟩, ht, hd⟩
    exact ⟨(hb.mp ⟨⟨h1, ht⟩, hd⟩).1, (hb.mp ⟨⟨h1, ht⟩, hd⟩).2, hX⟩
  · rintro ⟨hlo, hhi, hX⟩
    obtain ⟨⟨h1, ht⟩, hd⟩ := hb.mpr ⟨hlo, hhi⟩
    exact ⟨⟨h1, hX⟩, ht, hd⟩

/-- The weight `μ(b) [(b,f)=1]`. -/
def coprimeMoebiusWeight (f b : ℕ) : ℝ := if Nat.Coprime b f then (moebius b : ℝ) else 0

theorem abs_coprimeMoebiusWeight_le (f b : ℕ) : |coprimeMoebiusWeight f b| ≤ 1 := by
  unfold coprimeMoebiusWeight
  split_ifs
  · exact_mod_cast abs_moebius_le_one
  · rw [abs_zero]; exact zero_le_one

theorem abs_coprimeMoebiusWeight_mul_fract_le (f b : ℕ) (x : ℝ) :
    |coprimeMoebiusWeight f b * Int.fract x| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (Int.fract_nonneg x)]
  exact mul_le_one₀ (abs_coprimeMoebiusWeight_le f b) (Int.fract_nonneg _) (Int.fract_lt_one _).le

theorem Ioc_zero_eq_Icc_one (Y : ℕ) : Ioc 0 Y = Icc 1 Y := by
  ext b; simp only [mem_Ioc, mem_Icc]; omega

/-- `Σ_{u < b ≤ s} μ(b)[(b,f)=1] = M_f(s) − M_f(u)`. -/
theorem sum_Ioc_coprimeMoebiusWeight {f u s : ℕ} (hus : u ≤ s) :
    ∑ b ∈ Ioc u s, coprimeMoebiusWeight f b = coprimeMoebiusSum f s - coprimeMoebiusSum f u := by
  have hcons := Finset.sum_Ioc_consecutive (coprimeMoebiusWeight f) (Nat.zero_le u) hus
  rw [Ioc_zero_eq_Icc_one, Ioc_zero_eq_Icc_one] at hcons
  have e1 : coprimeMoebiusSum f s = ∑ b ∈ Icc 1 s, coprimeMoebiusWeight f b := rfl
  have e2 : coprimeMoebiusSum f u = ∑ b ∈ Icc 1 u, coprimeMoebiusWeight f b := rfl
  rw [e1, e2]
  linarith

/-- The range `b > t = ⌊M/c⌋`, where the sawtooth is `M/(cb)`:
`|Σ| ≤ 4 K Π(f) t (1 + log t)^{-3}`. -/
theorem abs_sum_fract_above_le {K : ℝ} (hK0 : 0 ≤ K)
    (hKh : ∀ f : ℕ, f ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |coprimeMoebiusHarmonicSum f Y| ≤ K * rankinProduct f / (1 + Real.log Y) ^ 4)
    {f c M X t : ℕ} (hf : f ≠ 0) (hc : 1 ≤ c) (htM : M / c = t) (ht : 1 ≤ t) :
    |∑ b ∈ (Icc 1 X).filter (fun b => t < b),
        coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
      4 * K * rankinProduct f * t / (1 + Real.log t) ^ 3 := by
  have hP1 := one_le_rankinProduct f
  have hKP0 : 0 ≤ K * rankinProduct f := mul_nonneg hK0 (by linarith)
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hlt : 0 ≤ Real.log t := Real.log_nonneg htR
  have hL : 0 < 1 + Real.log t := by linarith
  have hL4 : 0 < (1 + Real.log t) ^ 4 := pow_pos hL 4
  have hL3 : 0 < (1 + Real.log t) ^ 3 := pow_pos hL 3
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hMc : (M : ℝ) / c ≤ 2 * t := by
    have h := Nat.lt_mul_div_succ M (show 0 < c by omega)
    rw [htM] at h
    have hR : (M : ℝ) < c * ((t : ℝ) + 1) := by exact_mod_cast h
    rw [div_le_iff₀ hcR]
    nlinarith
  have hset : (Icc 1 X).filter (fun b => t < b) = Ioc t X := by
    ext b; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  have hpt : ∀ b ∈ Ioc t X, coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ)) =
      (M : ℝ) / c * (if Nat.Coprime b f then (moebius b : ℝ) / b else 0) := by
    intro b hb
    have hb1 : t < b := (mem_Ioc.mp hb).1
    have hlt' : M < c * b := by
      have h := Nat.lt_mul_div_succ M (show 0 < c by omega)
      rw [htM] at h
      exact h.trans_le (Nat.mul_le_mul_left c hb1)
    have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Int.fract_div_natCast_eq_div_natCast_mod, Nat.mod_eq_of_lt hlt']
    unfold coprimeMoebiusWeight
    split_ifs
    · push_cast; field_simp
    · rw [zero_mul, mul_zero]
  rw [hset, sum_congr rfl hpt, ← mul_sum]
  rcases Nat.lt_or_ge X t with hXt | hXt
  · rw [Ioc_eq_empty (by omega), sum_empty, mul_zero, abs_zero]
    exact div_nonneg (by nlinarith) hL3.le
  have hcons := Finset.sum_Ioc_consecutive
    (fun b => if Nat.Coprime b f then (moebius b : ℝ) / b else 0) (Nat.zero_le t) hXt
  rw [Ioc_zero_eq_Icc_one, Ioc_zero_eq_Icc_one] at hcons
  have hdiff : ∑ b ∈ Ioc t X, (if Nat.Coprime b f then (moebius b : ℝ) / b else 0) =
      coprimeMoebiusHarmonicSum f X - coprimeMoebiusHarmonicSum f t := by
    unfold coprimeMoebiusHarmonicSum; linarith
  rw [hdiff]
  have hXR : (t : ℝ) ≤ X := by exact_mod_cast hXt
  have hLX : (1 + Real.log t) ^ 4 ≤ (1 + Real.log X) ^ 4 :=
    pow_le_pow_left₀ hL.le (by linarith [Real.log_le_log ht0 hXR]) 4
  have hmX' : |coprimeMoebiusHarmonicSum f X| ≤ K * rankinProduct f / (1 + Real.log t) ^ 4 :=
    (hKh f hf X (by omega)).trans (div_le_div_of_nonneg_left hKP0 hL4 hLX)
  have hmt := hKh f hf t ht
  have hMc0 : 0 ≤ (M : ℝ) / c := by positivity
  have h34 : (1 + Real.log t) ^ 3 ≤ (1 + Real.log t) ^ 4 := by
    have : 1 ≤ 1 + Real.log t := by linarith
    calc (1 + Real.log t) ^ 3 = (1 + Real.log t) ^ 3 * 1 := (mul_one _).symm
      _ ≤ (1 + Real.log t) ^ 3 * (1 + Real.log t) := mul_le_mul_of_nonneg_left this hL3.le
      _ = (1 + Real.log t) ^ 4 := by ring
  calc |(M : ℝ) / c * (coprimeMoebiusHarmonicSum f X - coprimeMoebiusHarmonicSum f t)|
      ≤ (M : ℝ) / c * (K * rankinProduct f / (1 + Real.log t) ^ 4 +
          K * rankinProduct f / (1 + Real.log t) ^ 4) := by
        rw [abs_mul, abs_of_nonneg hMc0]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hmX' hmt)) hMc0
    _ = (M : ℝ) / c * (2 * (K * rankinProduct f) / (1 + Real.log t) ^ 4) := by ring
    _ ≤ 2 * t * (2 * (K * rankinProduct f) / (1 + Real.log t) ^ 4) :=
        mul_le_mul_of_nonneg_right hMc (div_nonneg (by linarith) hL4.le)
    _ = 4 * (K * rankinProduct f * t) / (1 + Real.log t) ^ 4 := by ring
    _ ≤ 4 * (K * rankinProduct f * t) / (1 + Real.log t) ^ 3 :=
        div_le_div_of_nonneg_left (by nlinarith) hL3 h34
    _ = 4 * K * rankinProduct f * t / (1 + Real.log t) ^ 3 := by ring

/-- The integers with `⌊t/b⌋ > √t`, all below `√t`, contribute at most `√t`. -/
theorem abs_sum_fract_small_le {f c M X t : ℕ} :
    |∑ b ∈ ((Icc 1 X).filter (fun b => ¬ t < b)).filter (fun b => ¬ t / b ≤ Nat.sqrt t),
        coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤ Real.sqrt t := by
  have hsub : ((Icc 1 X).filter (fun b => ¬ t < b)).filter (fun b => ¬ t / b ≤ Nat.sqrt t) ⊆
      Icc 1 (t / (Nat.sqrt t + 1)) := by
    intro b hb
    simp only [mem_filter, mem_Icc, not_lt, not_le] at hb ⊢
    obtain ⟨⟨⟨h1, -⟩, -⟩, hlt⟩ := hb
    refine ⟨h1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
    have := (Nat.le_div_iff_mul_le (by omega : 0 < b)).mp hlt
    linarith
  have hcount : t / (Nat.sqrt t + 1) ≤ Nat.sqrt t := by
    have h := Nat.lt_succ_sqrt' t
    have : t / (Nat.sqrt t + 1) < Nat.sqrt t + 1 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith)
    omega
  calc _ ≤ ∑ b ∈ ((Icc 1 X).filter (fun b => ¬ t < b)).filter (fun b => ¬ t / b ≤ Nat.sqrt t),
        |coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ ((Icc 1 X).filter (fun b => ¬ t < b)).filter (fun b => ¬ t / b ≤ Nat.sqrt t),
        (1 : ℝ) := sum_le_sum fun b _ => abs_coprimeMoebiusWeight_mul_fract_le f b _
    _ ≤ ((t / (Nat.sqrt t + 1) : ℕ) : ℝ) := by
        rw [sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast (card_le_card hsub).trans (by rw [Nat.card_Icc, Nat.add_sub_cancel])
    _ ≤ (Nat.sqrt t : ℝ) := by exact_mod_cast hcount
    _ ≤ Real.sqrt t := Real.nat_sqrt_le_real_sqrt

/-- On a piece `n ≤ √t` the coprime Mertens function is `≤ 256 K Π(f) t/(n (1 + log t)⁴)`:
the piece lies in `[t^{1/4}, t/n]`. -/
theorem abs_coprimeMoebiusSum_on_piece_le {K : ℝ} (hK0 : 0 ≤ K)
    (hKs : ∀ f : ℕ, f ≠ 0 → ∀ s : ℕ, 1 ≤ s →
      |coprimeMoebiusSum f s| ≤ K * rankinProduct f * s / (1 + Real.log s) ^ 4)
    {f t n x : ℕ} (hf : f ≠ 0) (ht : 256 ≤ t) (hn1 : 1 ≤ n) (hn : n ≤ Nat.sqrt t)
    (hux : t / (n + 1) ≤ x) (hxv : x ≤ t / n) :
    |coprimeMoebiusSum f x| ≤ 256 * K * rankinProduct f * t / (n * (1 + Real.log t) ^ 4) := by
  have hP1 := one_le_rankinProduct f
  have hKP0 : 0 ≤ K * rankinProduct f := mul_nonneg hK0 (by linarith)
  have htR : (256 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hL : 0 < 1 + Real.log t := by linarith
  have hL4 : 0 < (1 + Real.log t) ^ 4 := pow_pos hL 4
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnsq : (n : ℝ) ≤ Real.sqrt t :=
    (by exact_mod_cast hn : (n : ℝ) ≤ Nat.sqrt t).trans Real.nat_sqrt_le_real_sqrt
  have hsq16 : (16 : ℝ) ≤ Real.sqrt t := by
    rw [show (16 : ℝ) = Real.sqrt 256 by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt htR
  have hr4 : (4 : ℝ) ≤ Real.sqrt (Real.sqrt t) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hsq16
  have hrr : Real.sqrt (Real.sqrt t) * Real.sqrt (Real.sqrt t) = Real.sqrt t :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hlogr : Real.log (Real.sqrt (Real.sqrt t)) = Real.log t / 4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt ht0.le]; ring
  -- the lower end of the piece is at least `t^{1/4}`
  have hu_lo : Real.sqrt (Real.sqrt t) ≤ ((t / (n + 1) : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := t) (show 0 < n + 1 by omega)
    have hR : (t : ℝ) < (((t / (n + 1) : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) := by
      have : t < (t / (n + 1) + 1) * (n + 1) := by nlinarith
      exact_mod_cast this
    have hn2 : (n : ℝ) + 1 ≤ 2 * Real.sqrt t := by linarith
    have hsqt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have h1 : Real.sqrt t / 2 ≤ ((t / (n + 1) : ℕ) : ℝ) + 1 := by
      by_contra hcon
      have hcon' := lt_of_not_ge hcon
      have : (((t / (n + 1) : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) ≤ Real.sqrt t / 2 * (2 * Real.sqrt t) :=
        mul_le_mul hcon'.le hn2 (by positivity) (by positivity)
      nlinarith
    nlinarith
  have hxr : Real.sqrt (Real.sqrt t) ≤ (x : ℝ) := hu_lo.trans (by exact_mod_cast hux)
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ x := by linarith
    exact_mod_cast this
  have hxt : (x : ℝ) ≤ (t : ℝ) / n :=
    (by exact_mod_cast hxv : (x : ℝ) ≤ ((t / n : ℕ) : ℝ)).trans Nat.cast_div_le
  have hlx : Real.log t / 4 ≤ Real.log x := by
    rw [← hlogr]; exact Real.log_le_log (by linarith) hxr
  have hlx0 : 0 ≤ Real.log x := by linarith
  have hbase : (1 + Real.log t) / 4 ≤ 1 + Real.log x := by linarith
  have hpow : ((1 + Real.log t) / 4) ^ 4 ≤ (1 + Real.log x) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hbase 4
  refine (hKs f hf x hx1).trans ?_
  rw [div_le_div_iff₀ (pow_pos (by linarith) 4) (mul_pos (by linarith) hL4)]
  have hxn : (x : ℝ) * n ≤ t := by rwa [le_div_iff₀ (by linarith)] at hxt
  have h256 : (1 + Real.log t) ^ 4 ≤ 256 * (1 + Real.log x) ^ 4 := by
    calc (1 + Real.log t) ^ 4 = 256 * ((1 + Real.log t) / 4) ^ 4 := by ring
      _ ≤ 256 * (1 + Real.log x) ^ 4 := by linarith
  calc K * rankinProduct f * x * (n * (1 + Real.log t) ^ 4)
      = K * rankinProduct f * (x * n) * (1 + Real.log t) ^ 4 := by ring
    _ ≤ K * rankinProduct f * t * (256 * (1 + Real.log x) ^ 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hxn hKP0) h256 hL4.le (mul_nonneg hKP0 ht0.le)
    _ = 256 * K * rankinProduct f * t * (1 + Real.log x) ^ 4 := by ring

/-- **One piece.** For `1 ≤ n ≤ √t`, `t = ⌊M/c⌋ ≥ 256`:
`|Σ_{⌊t/(n+1)⌋ < b ≤ min(⌊t/n⌋, X)} μ(b)[(b,f)=1] {M/(cb)}| ≤ 512 K Π(f) t/(n (1 + log t)⁴)`. -/
theorem abs_sum_fract_piece_le {K : ℝ} (hK0 : 0 ≤ K)
    (hKs : ∀ f : ℕ, f ≠ 0 → ∀ s : ℕ, 1 ≤ s →
      |coprimeMoebiusSum f s| ≤ K * rankinProduct f * s / (1 + Real.log s) ^ 4)
    {f c M X t n : ℕ} (hf : f ≠ 0) (hc : 1 ≤ c) (htM : M / c = t) (ht : 256 ≤ t) (hn1 : 1 ≤ n)
    (hn : n ≤ Nat.sqrt t) :
    |∑ b ∈ Ioc (t / (n + 1)) (min (t / n) X),
        coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
      512 * K * rankinProduct f * t / (n * (1 + Real.log t) ^ 4) := by
  have hP1 := one_le_rankinProduct f
  have hlt : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
  have hL4 : 0 < (1 + Real.log t) ^ 4 := pow_pos (by linarith) 4
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hmem : ∀ b ∈ Ioc (t / (n + 1)) (min (t / n) X), 1 ≤ b ∧ t / b = n := by
    intro b hb
    rw [← filter_div_eq_Ioc_min hn1] at hb
    simp only [mem_filter, mem_Icc] at hb
    exact ⟨hb.1.1, hb.2.2⟩
  have hw : ∀ b ∈ Ioc (t / (n + 1)) (min (t / n) X), Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ)) =
      (M : ℝ) / ((c * b : ℕ) : ℝ) - n := fun b hb =>
    fract_div_eq_of_div_div_eq hc (hmem b hb).1 (by rw [htM]; exact (hmem b hb).2)
  rw [sum_congr rfl fun b hb => by rw [hw b hb]]
  have hT0 : 0 ≤ 512 * K * rankinProduct f * t / (n * (1 + Real.log t) ^ 4) :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Nat.cast_nonneg _))
      (mul_nonneg (by linarith) hL4.le)
  refine abs_sum_Ioc_mul_le_of_antitone hT0 ?_ ?_ ?_ ?_
  · intro b hb
    rw [← hw b hb]; exact Int.fract_nonneg _
  · intro b hb
    rw [← hw b hb]; exact (Int.fract_lt_one _).le
  · intro b hub _
    have hb1 : 1 ≤ b := lt_of_le_of_lt (Nat.zero_le _) hub
    apply sub_le_sub_right
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    · have : 0 < c * b := Nat.mul_pos (by omega) hb1
      exact_mod_cast this
    · exact_mod_cast Nat.mul_le_mul_left c (Nat.le_succ b)
  · intro s hus hsv
    have hsv' : s ≤ t / n := hsv.trans (min_le_left _ _)
    rw [sum_Ioc_coprimeMoebiusWeight hus]
    calc |coprimeMoebiusSum f s - coprimeMoebiusSum f (t / (n + 1))|
        ≤ |coprimeMoebiusSum f s| + |coprimeMoebiusSum f (t / (n + 1))| := abs_sub _ _
      _ ≤ 256 * K * rankinProduct f * t / (n * (1 + Real.log t) ^ 4) +
            256 * K * rankinProduct f * t / (n * (1 + Real.log t) ^ 4) :=
          add_le_add (abs_coprimeMoebiusSum_on_piece_le hK0 hKs hf ht hn1 hn hus hsv')
            (abs_coprimeMoebiusSum_on_piece_le hK0 hKs hf ht hn1 hn le_rfl (hus.trans hsv'))
      _ = 512 * K * rankinProduct f * t / (n * (1 + Real.log t) ^ 4) := by ring

/-- The pieces `1 ≤ ⌊t/b⌋ ≤ √t` together: `≤ 512 K Π(f) t (1 + log t)^{-3}`. -/
theorem abs_sum_fract_pieces_le {K : ℝ} (hK0 : 0 ≤ K)
    (hKs : ∀ f : ℕ, f ≠ 0 → ∀ s : ℕ, 1 ≤ s →
      |coprimeMoebiusSum f s| ≤ K * rankinProduct f * s / (1 + Real.log s) ^ 4)
    {f c M X t : ℕ} (hf : f ≠ 0) (hc : 1 ≤ c) (htM : M / c = t) (ht : 256 ≤ t) :
    |∑ b ∈ ((Icc 1 X).filter (fun b => ¬ t < b)).filter (fun b => t / b ≤ Nat.sqrt t),
        coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
      512 * K * rankinProduct f * t / (1 + Real.log t) ^ 3 := by
  have hP1 := one_le_rankinProduct f
  have htR : (256 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hL : 0 < 1 + Real.log t := by linarith
  have hL4 : 0 < (1 + Real.log t) ^ 4 := pow_pos hL 4
  rw [← sum_fiberwise_of_maps_to
    (s := ((Icc 1 X).filter (fun b => ¬ t < b)).filter (fun b => t / b ≤ Nat.sqrt t))
    (t := Icc 1 (Nat.sqrt t)) (g := fun b => t / b) (fun b hb => by
      simp only [mem_filter, mem_Icc, not_lt] at hb ⊢
      obtain ⟨⟨⟨h1, -⟩, hbt⟩, hn⟩ := hb
      exact ⟨(Nat.one_le_div_iff (by omega)).mpr hbt, hn⟩)]
  have hset : ∀ n ∈ Icc 1 (Nat.sqrt t),
      (((Icc 1 X).filter (fun b => ¬ t < b)).filter (fun b => t / b ≤ Nat.sqrt t)).filter
        (fun b => t / b = n) = Ioc (t / (n + 1)) (min (t / n) X) := by
    intro n hn
    obtain ⟨hn1, hnn0⟩ := mem_Icc.mp hn
    rw [← filter_div_eq_Ioc_min hn1]
    ext b
    simp only [mem_filter, mem_Icc, not_lt]
    constructor
    · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩; exact ⟨⟨h1, h2⟩, h3, h5⟩
    · rintro ⟨⟨h1, h2⟩, h3, h5⟩; exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, by rw [h5]; exact hnn0⟩, h5⟩
  rw [sum_congr rfl fun n hn => by rw [hset n hn]]
  have hharm : ∑ n ∈ Icc 1 (Nat.sqrt t), ((n : ℝ))⁻¹ ≤ 1 + Real.log t := by
    have h1 : ∑ n ∈ Icc 1 (Nat.sqrt t), ((n : ℝ))⁻¹ = (harmonic (Nat.sqrt t) : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [h1]
    refine (harmonic_le_one_add_log _).trans ?_
    have hn0t : (Nat.sqrt t : ℝ) ≤ t := by exact_mod_cast Nat.sqrt_le_self t
    rcases Nat.eq_zero_or_pos (Nat.sqrt t) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
    · have : (0 : ℝ) < Nat.sqrt t := by exact_mod_cast h0
      linarith [Real.log_le_log this hn0t]
  have hc0 : 0 ≤ 512 * K * rankinProduct f * t / (1 + Real.log t) ^ 4 :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) ht0.le) hL4.le
  calc _ ≤ ∑ n ∈ Icc 1 (Nat.sqrt t), |∑ b ∈ Ioc (t / (n + 1)) (min (t / n) X),
          coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 (Nat.sqrt t), 512 * K * rankinProduct f * t / (n * (1 + Real.log t) ^ 4) :=
        sum_le_sum fun n hn => abs_sum_fract_piece_le hK0 hKs hf hc htM ht (mem_Icc.mp hn).1
          (mem_Icc.mp hn).2
    _ = 512 * K * rankinProduct f * t / (1 + Real.log t) ^ 4 *
          ∑ n ∈ Icc 1 (Nat.sqrt t), ((n : ℝ))⁻¹ := by
        rw [mul_sum]
        refine sum_congr rfl fun n hn => ?_
        have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hn).1; omega)
        field_simp
    _ ≤ 512 * K * rankinProduct f * t / (1 + Real.log t) ^ 4 * (1 + Real.log t) :=
        mul_le_mul_of_nonneg_left hharm hc0
    _ = 512 * K * rankinProduct f * t / (1 + Real.log t) ^ 3 := by field_simp

/-- **Sawtooth cancellation.** For `c ≥ 1`, `t = ⌊M/c⌋ ≥ 256`, `f ≥ 1` and every `X`,
`|Σ_{b ≤ X, (b,f)=1} μ(b) {M/(cb)}| ≤ 516 K Π(f) t (1 + log t)^{-3} + √t`. -/
theorem abs_sum_coprime_moebius_fract_le_of {K : ℝ} (hK0 : 0 ≤ K)
    (hKh : ∀ f : ℕ, f ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |coprimeMoebiusHarmonicSum f Y| ≤ K * rankinProduct f / (1 + Real.log Y) ^ 4)
    (hKs : ∀ f : ℕ, f ≠ 0 → ∀ s : ℕ, 1 ≤ s →
      |coprimeMoebiusSum f s| ≤ K * rankinProduct f * s / (1 + Real.log s) ^ 4)
    {f c M X t : ℕ} (hf : f ≠ 0) (hc : 1 ≤ c) (htM : M / c = t) (ht : 256 ≤ t) :
    |∑ b ∈ Icc 1 X, coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
      516 * K * rankinProduct f * t / (1 + Real.log t) ^ 3 + Real.sqrt t := by
  rw [← sum_filter_add_sum_filter_not (Icc 1 X) (fun b => t < b),
    ← sum_filter_add_sum_filter_not ((Icc 1 X).filter (fun b => ¬ t < b))
      (fun b => t / b ≤ Nat.sqrt t)]
  have hA := abs_sum_fract_above_le hK0 hKh (X := X) hf hc htM (by omega)
  have hB := abs_sum_fract_pieces_le hK0 hKs (X := X) hf hc htM ht
  have hC := abs_sum_fract_small_le (f := f) (c := c) (M := M) (X := X) (t := t)
  calc _ ≤ _ := (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ 4 * K * rankinProduct f * t / (1 + Real.log t) ^ 3 +
          (512 * K * rankinProduct f * t / (1 + Real.log t) ^ 3 + Real.sqrt t) :=
        add_le_add hA (add_le_add hB hC)
    _ = 516 * K * rankinProduct f * t / (1 + Real.log t) ^ 3 + Real.sqrt t := by ring

theorem exists_abs_sum_coprime_moebius_fract_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f c M X t : ℕ, f ≠ 0 → 1 ≤ c → M / c = t → 256 ≤ t →
      |∑ b ∈ Icc 1 X, coprimeMoebiusWeight f b * Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
        K * rankinProduct f * t / (1 + Real.log t) ^ 3 + Real.sqrt t := by
  obtain ⟨K, hK0, hKh, hKs⟩ := exists_abs_coprimeMoebiusSum_le
  exact ⟨516 * K, by positivity, fun f c M X t hf hc htM ht =>
    abs_sum_coprime_moebius_fract_le_of hK0 hKh hKs hf hc htM ht⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
