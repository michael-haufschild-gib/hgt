import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWirsingBoundForFlipTwins
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo

/-!
# The rough Wirsing bound is uniform

Let `ω` be completely multiplicative with `|ω| ≤ 1` and prime mean
`Σ_{p ≤ n} ω(p) log p/p = β log n + O((1 + log n)^α)`, `0 ≤ α < β ≤ 1`. Restrict `ω` to the `Q`-rough
numbers
(`roughGauge Q ω`: every prime factor `≥ Q`). Then

  `|Σ_{r ≤ Y, Q-rough} ω(r)/r| ≤ A (log Y/log Q)^β + B`

with `A, B` independent of `Q ≥ 3` (`exists_abs_gaugeHarmonicSum_roughGauge_le`).

* The Wirsing equation holds with the absolute harmonic weight `W(N) = Σ_{n ≤ N} |ω(n)|/n` in place of
  `H_N` (`abs_wirsing_equation_le_absHarmonic`): the total variation of `k ↦ L(N/k)` is at most `W(N)`.
* For the rough gauge `W ≤ F_Q(N) ≤ 1 + (1 + 2 log N)/log Q` (`roughHarmonic_le_one_add_div_log`, the
  smooth–rough fibration of `[1, N²]` restricted to `a < Q`), and the prime mean deviates from
  `β log n` by at most `2C(1 + log n)^α + β log Q`: the forcing is
  `K (log Q + log N) + K₂ (log N)^{1+α}/log Q`.
* The integrating factor `I(Y)/(log Y)^{1+β}` (`integrating_factor_le`, `le_of_sharp_wirsing`) turns
  this forcing into the sharp exponent: `I(Q) = log Q` and the forcing sum is `≪ (log Q)^{−β}` because
  `α < β` (`sum_forcing_le`).

The mass bounds `F_Q(X) ≥ c log(X + 1)/log Q` (`exists_roughHarmonic_ge`) and
`Σ_{a ≤ N, Q-smooth} 1/a ≤ K log Q` (`exists_sum_smoothSet_inv_le`) complete the toolkit for rough
means.
-/

open Finset Filter
open scoped ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (gaugeHarmonicSum)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (roughInterval roughHarmonic smoothSet
  mem_roughInterval mem_smoothSet sum_Icc_eq_smooth_rough eq_one_of_mem_roughInterval_of_le
  roughInterval_mono mertensPrimeProduct_mul_log_le_roughHarmonic
  exists_mertensPrimeProduct_mul_log_ge)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

section AbsHarmonic

variable (ω : ℕ → ℝ)

/-- The **absolute harmonic weight** `W(n) = Σ_{m ≤ n} |ω(m)|/m`. -/
def absHarmonic (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, |ω m| / m

theorem absHarmonic_nonneg (n : ℕ) : 0 ≤ absHarmonic ω n :=
  sum_nonneg fun _ _ => by positivity

theorem absHarmonic_mono {a b : ℕ} (h : a ≤ b) : absHarmonic ω a ≤ absHarmonic ω b :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun _ _ _ => by positivity

theorem abs_gaugeHarmonicSum_le_absHarmonic (n : ℕ) :
    |gaugeHarmonicSum ω n| ≤ absHarmonic ω n := by
  unfold gaugeHarmonicSum absHarmonic
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun m _ => ?_))
  rw [abs_div, Nat.abs_cast]

/-- `L` moves by at most the increment of the absolute harmonic weight. -/
theorem abs_gaugeHarmonicSum_sub_le_absHarmonic {a b : ℕ} (hab : a ≤ b) :
    |gaugeHarmonicSum ω b - gaugeHarmonicSum ω a| ≤ absHarmonic ω b - absHarmonic ω a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have eL : gaugeHarmonicSum ω (b + 1) =
        gaugeHarmonicSum ω b + ω (b + 1) / ((b + 1 : ℕ) : ℝ) := by
      unfold gaugeHarmonicSum; rw [sum_Icc_succ_top (by omega)]
    have eW : absHarmonic ω (b + 1) = absHarmonic ω b + |ω (b + 1)| / ((b + 1 : ℕ) : ℝ) := by
      unfold absHarmonic; rw [sum_Icc_succ_top (by omega)]
    have h1 : |ω (b + 1) / ((b + 1 : ℕ) : ℝ)| = |ω (b + 1)| / ((b + 1 : ℕ) : ℝ) := by
      rw [abs_div, Nat.abs_cast]
    rw [eL, eW]
    calc |gaugeHarmonicSum ω b + ω (b + 1) / ((b + 1 : ℕ) : ℝ) - gaugeHarmonicSum ω a|
        ≤ |gaugeHarmonicSum ω b - gaugeHarmonicSum ω a| + |ω (b + 1) / ((b + 1 : ℕ) : ℝ)| := by
          rw [show gaugeHarmonicSum ω b + ω (b + 1) / ((b + 1 : ℕ) : ℝ) - gaugeHarmonicSum ω a =
            (gaugeHarmonicSum ω b - gaugeHarmonicSum ω a) + ω (b + 1) / ((b + 1 : ℕ) : ℝ) by ring]
          exact abs_add_le _ _
      _ ≤ _ := by rw [h1]; linarith

/-- The total variation of `k ↦ L(N/k)` is at most `W(N)`. -/
theorem sum_abs_sub_gaugeHarmonicSum_div_le_absHarmonic (N : ℕ) :
    ∑ i ∈ range (N - 1),
      |gaugeHarmonicSum ω (N / (i + 1 + 1)) - gaugeHarmonicSum ω (N / (i + 1))| ≤
        absHarmonic ω N := by
  have h : ∀ i ∈ range (N - 1),
      |gaugeHarmonicSum ω (N / (i + 1 + 1)) - gaugeHarmonicSum ω (N / (i + 1))| ≤
        absHarmonic ω (N / (i + 1)) - absHarmonic ω (N / (i + 1 + 1)) := fun i _ => by
    rw [abs_sub_comm]
    exact abs_gaugeHarmonicSum_sub_le_absHarmonic ω (Nat.div_le_div_left (by omega) (by omega))
  refine (sum_le_sum h).trans ?_
  rw [sum_range_sub' (fun i => absHarmonic ω (N / (i + 1)))]
  simp only [zero_add, Nat.div_one]
  linarith [absHarmonic_nonneg ω (N / (N - 1 + 1))]

/-- **Abel summation of the prime terms against `W`.** -/
theorem abs_primePart_sub_le_absHarmonic (hbd : ∀ n, |ω n| ≤ 1) {β C : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA : ∀ n, 1 ≤ n → n ≤ N → |primeMean ω n - β * Real.log n| ≤ C) :
    |∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
        β * logWeightSum ω N| ≤ C * (1 + absHarmonic ω N) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hA 1 le_rfl hN)
  set a : ℕ → ℝ := fun k => if k.Prime then ω k * Real.log k / k else 0
  set g : ℕ → ℝ := fun i => a (i + 1) - β * (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ))
  set f : ℕ → ℝ := fun i => gaugeHarmonicSum ω (N / (i + 1))
  have hsplit : ∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
      β * logWeightSum ω N = ∑ i ∈ range N, f i • g i := by
    rw [sum_filter, logWeightSum, mul_sum, ← sum_sub_distrib, sumIcc_eq_sumRange]
    refine sum_congr rfl fun i _ => ?_
    simp only [f, g, a, smul_eq_mul, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    split_ifs <;> ring
  have hG : ∀ n, ∑ i ∈ range n, g i = primeMean ω n - β * Real.log n := fun n => by
    simp only [g]
    rw [sum_sub_distrib, ← mul_sum]
    push_cast
    rw [sum_range_log_succ_sub, primeMean, sum_filter, sumIcc_eq_sumRange]
  have hGb : ∀ n, n ≤ N → |∑ i ∈ range n, g i| ≤ C := fun n hnN => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hC]
    · rw [hG]; exact hA n hn hnN
  rw [hsplit, sum_range_by_parts]
  have hf1 : |f (N - 1)| ≤ 1 := by
    simp only [f, Nat.sub_add_cancel hN, Nat.div_self hN]
    unfold gaugeHarmonicSum
    simp only [Icc_self, sum_singleton, Nat.cast_one, div_one]
    exact hbd 1
  have htv := sum_abs_sub_gaugeHarmonicSum_div_le_absHarmonic ω N
  calc |f (N - 1) • ∑ i ∈ range N, g i -
        ∑ i ∈ range (N - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j|
      ≤ |f (N - 1)| * C + ∑ i ∈ range (N - 1), |f (i + 1) - f i| * C := by
        refine (abs_sub _ _).trans (add_le_add ?_ ((abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun i hi => ?_)))
        · rw [smul_eq_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hGb N le_rfl) (abs_nonneg _)
        · rw [smul_eq_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hGb _ (by have := mem_range.mp hi; omega))
            (abs_nonneg _)
    _ ≤ 1 * C + absHarmonic ω N * C := by
        rw [← sum_mul]
        refine add_le_add (mul_le_mul_of_nonneg_right hf1 hC)
          (mul_le_mul_of_nonneg_right ?_ hC)
        simpa only [f, Nat.add_assoc] using htv
    _ = C * (1 + absHarmonic ω N) := by ring

/-- The constant bounding the non-prime terms of `Σ_{d ≤ N} Λ(d)/d`. -/
theorem nonprime_const_nonneg :
    0 ≤ 2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) := by
  have h := sum_vonMangoldt_nonprime_le (N := 1) le_rfl
  have h0 : (0 : ℝ) ≤ ∑ d ∈ Icc 1 1 with ¬ d.Prime, Λ d / d :=
    sum_nonneg fun d _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
  linarith

/-- **The Wirsing equation against `W`**: if the prime mean is `β log n + O(C)`, then
`|L(N) log N − (1 + β) M(N)| ≤ (C + C') (1 + W(N)) + 2|β|`. -/
theorem abs_wirsing_equation_le_absHarmonic
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (hbd : ∀ n, |ω n| ≤ 1) {β C : ℝ}
    {N : ℕ} (hN : 1 ≤ N) (hA : ∀ n, 1 ≤ n → n ≤ N → |primeMean ω n - β * Real.log n| ≤ C) :
    |gaugeHarmonicSum ω N * Real.log N - (1 + β) * polarMoment ω N| ≤
      (C + (2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail))) *
        (1 + absHarmonic ω N) + 2 * |β| := by
  set Cpp := 2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  have hCpp : 0 ≤ Cpp := nonprime_const_nonneg
  have hW := absHarmonic_nonneg ω N
  have hcheb := logMoment_eq_vonMangoldt ω hmul N
  rw [logMoment_eq] at hcheb
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime
    (fun d => Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d))
  have hprime : ∑ d ∈ Icc 1 N with d.Prime, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d) =
      ∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) :=
    sum_congr rfl fun d hd => by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hd).2]; ring
  rw [hprime] at hsplit
  -- non-prime terms: `|L(N/d)| ≤ W(N/d) ≤ W(N)`
  have hnp : |∑ d ∈ Icc 1 N with ¬ d.Prime, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d)| ≤
      Cpp * absHarmonic ω N := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ (Icc 1 N).filter (fun d => ¬ d.Prime),
        |Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d)| ≤ Λ d / d * absHarmonic ω N := by
      intro d hd
      have hd1 := (mem_Icc.mp (mem_filter.mp hd).1)
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1.1
      have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
      rw [abs_mul, abs_mul, abs_of_nonneg hΛ, abs_div, abs_of_pos hd0]
      have hL := (abs_gaugeHarmonicSum_le_absHarmonic ω (N / d)).trans
        (absHarmonic_mono ω (Nat.div_le_self N d))
      calc Λ d * (|ω d| / d) * |gaugeHarmonicSum ω (N / d)|
          ≤ Λ d * (1 / d) * absHarmonic ω N :=
            mul_le_mul (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (hbd d) hd0.le) hΛ) hL (abs_nonneg _) (by positivity)
        _ = Λ d / d * absHarmonic ω N := by ring
    refine (sum_le_sum hterm).trans ?_
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_vonMangoldt_nonprime_le hN) hW
  have hab := abs_primePart_sub_le_absHarmonic ω hbd hN hA
  have hpm := abs_polarMoment_sub_logWeightSum_le hbd hN
  have heq : gaugeHarmonicSum ω N * Real.log N - (1 + β) * polarMoment ω N =
      (∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
          β * logWeightSum ω N) +
        ∑ d ∈ Icc 1 N with ¬ d.Prime, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d) -
        β * (polarMoment ω N - logWeightSum ω N) := by
    linarith [hcheb, hsplit]
  rw [heq]
  have hβ : |β * (polarMoment ω N - logWeightSum ω N)| ≤ 2 * |β| := by
    rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hpm (abs_nonneg _)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hA 1 le_rfl hN)
  calc _ ≤ |∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
          β * logWeightSum ω N| +
        |∑ d ∈ Icc 1 N with ¬ d.Prime, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d)| +
        |β * (polarMoment ω N - logWeightSum ω N)| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C * (1 + absHarmonic ω N) + Cpp * absHarmonic ω N + 2 * |β| :=
        add_le_add (add_le_add hab hnp) hβ
    _ ≤ (C + Cpp) * (1 + absHarmonic ω N) + 2 * |β| := by nlinarith

/-- `M(Y) = Σ_{1 ≤ n < Y} L(n) Δlog n`. -/
theorem polarMoment_eq_sum (Y : ℕ) :
    polarMoment ω Y =
      ∑ n ∈ Ico 1 Y, gaugeHarmonicSum ω n * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  rcases Nat.eq_zero_or_pos Y with rfl | hY
  · simp [polarMoment]
  induction Y, hY using Nat.le_induction with
  | base => simp [polarMoment]
  | succ Y hY ih =>
    have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
    rw [polarMoment_succ ω hY, ih, sum_Ico_succ_top hY,
      Real.log_div (by positivity) hY0.ne']

end AbsHarmonic

section RoughGauge

variable {ω : ℕ → ℝ}

/-- `ω` restricted to the `Q`-rough numbers (every prime factor at least `Q`). -/
def roughGauge (Q : ℕ) (ω : ℕ → ℝ) (n : ℕ) : ℝ :=
  if ∀ p ∈ n.primeFactors, Q ≤ p then ω n else 0

theorem roughGauge_mul (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (Q : ℕ) :
    ∀ a b, a ≠ 0 → b ≠ 0 → roughGauge Q ω (a * b) = roughGauge Q ω a * roughGauge Q ω b := by
  intro a b ha hb
  unfold roughGauge
  rw [Nat.primeFactors_mul ha hb, hmul a b ha hb]
  by_cases h1 : ∀ p ∈ a.primeFactors, Q ≤ p <;> by_cases h2 : ∀ p ∈ b.primeFactors, Q ≤ p
  · rw [if_pos fun p hp => (mem_union.mp hp).elim (h1 p) (h2 p), if_pos h1, if_pos h2]
  · rw [if_neg fun h => h2 fun p hp => h p (mem_union_right _ hp), if_pos h1, if_neg h2,
      mul_zero]
  · rw [if_neg fun h => h1 fun p hp => h p (mem_union_left _ hp), if_neg h1, zero_mul]
  · rw [if_neg fun h => h1 fun p hp => h p (mem_union_left _ hp), if_neg h1, zero_mul]

theorem abs_roughGauge_le (hbd : ∀ n, |ω n| ≤ 1) (Q n : ℕ) : |roughGauge Q ω n| ≤ 1 := by
  unfold roughGauge
  split_ifs
  · exact hbd n
  · simp

theorem roughGauge_prime {Q p : ℕ} (hp : p.Prime) :
    roughGauge Q ω p = if Q ≤ p then ω p else 0 := by
  unfold roughGauge
  simp only [hp.primeFactors, mem_singleton, forall_eq]

/-- The absolute harmonic weight of the rough gauge is at most the rough mass. -/
theorem absHarmonic_roughGauge_le (hbd : ∀ n, |ω n| ≤ 1) (Q n : ℕ) :
    absHarmonic (roughGauge Q ω) n ≤ roughHarmonic Q n := by
  unfold absHarmonic roughHarmonic roughInterval
  rw [sum_filter]
  refine sum_le_sum fun m _ => ?_
  unfold roughGauge
  by_cases h : ∀ p ∈ m.primeFactors, Q ≤ p
  · rw [if_pos h, if_pos h]
    exact div_le_div_of_nonneg_right (hbd m) (Nat.cast_nonneg m)
  · rw [if_neg h, if_neg h]; simp

theorem roughHarmonic_le_one_of_lt {Q n : ℕ} (h : n < Q) : roughHarmonic Q n ≤ 1 := by
  unfold roughHarmonic
  calc ∑ K ∈ roughInterval Q n, (1 : ℝ) / K ≤ ∑ K ∈ ({1} : Finset ℕ), (1 : ℝ) / K :=
        sum_le_sum_of_subset_of_nonneg
          (fun K hK => mem_singleton.mpr (eq_one_of_mem_roughInterval_of_le hK h))
          fun _ _ _ => by positivity
    _ = 1 := by simp

/-- The prime mean of the rough gauge is `β log n` up to `2C(1 + log n)^α + β log Q`. -/
theorem abs_primeMean_roughGauge_sub_le {β C α : ℝ} (hβ : 0 ≤ β) (hα : 0 ≤ α)
    (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C * (1 + Real.log n) ^ α) {Q : ℕ}
    (hQ : 2 ≤ Q) {n : ℕ} (hn : 1 ≤ n) :
    |primeMean (roughGauge Q ω) n - β * Real.log n| ≤
      2 * (C * (1 + Real.log n) ^ α) + β * Real.log Q := by
  set m := min n (Q - 1)
  have hm1 : 1 ≤ m := le_min hn (by omega)
  -- the primes below `Q` are exactly those up to `m`
  have hsplit : primeMean ω n = primeMean (roughGauge Q ω) n + primeMean ω m := by
    unfold primeMean
    rw [← sum_filter_add_sum_filter_not ((Icc 1 n).filter Nat.Prime) (fun k => Q ≤ k)]
    congr 1
    · rw [filter_filter, sum_filter, sum_filter]
      refine sum_congr rfl fun k _ => ?_
      by_cases hk : k.Prime
      · rw [roughGauge_prime hk]
        by_cases hQk : Q ≤ k
        · simp [hk, hQk]
        · simp [hk, hQk]
      · simp [hk]
    · rw [filter_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [mem_filter, mem_Icc, m, le_min_iff, not_le]
      constructor
      · intro h
        exact ⟨⟨h.1.1, h.1.2, by have := h.2.2; omega⟩, h.2.1⟩
      · intro h
        exact ⟨⟨h.1.1, h.1.2.1⟩, h.2, by have := h.1.2.2; omega⟩
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (hA 1 le_rfl)
  have h1 := hA n hn
  have h2 : |primeMean ω m - β * Real.log m| ≤ C * (1 + Real.log n) ^ α := by
    refine (hA m hm1).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (by linarith [Real.log_natCast_nonneg m]) ?_ hα) hC)
    have := Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
      (show (m : ℝ) ≤ n by exact_mod_cast (show m ≤ n by omega))
    linarith
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hmQ : Real.log m ≤ Real.log Q :=
    Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast (show m ≤ Q by omega))
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end RoughGauge

section Mass

/-- **Rough mass, upper bound**: `F_Q(N) ≤ 1 + (1 + 2 log N)/log Q`. The smooth–rough fibration of
`[1, N²]` restricted to `a < Q` and `b ≤ N` gives `H(Q − 1) F_Q(N) ≤ H(N²)`. -/
theorem roughHarmonic_le_one_add_div_log {Q : ℕ} (hQ : 2 ≤ Q) (N : ℕ) :
    roughHarmonic Q N ≤ 1 + (1 + 2 * Real.log N) / Real.log Q := by
  have hlQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rcases lt_or_ge N Q with hNQ | hNQ
  · have h := roughHarmonic_le_one_of_lt hNQ
    have : 0 ≤ (1 + 2 * Real.log N) / Real.log Q := div_nonneg (by linarith) hlQ.le
    linarith
  have hsmall : (∑ a ∈ Icc 1 (Q - 1), (1 : ℝ) / a) * roughHarmonic Q N ≤
      ∑ n ∈ Icc 1 (N * N), (1 : ℝ) / n := by
    rw [sum_Icc_eq_smooth_rough Q (N * N), sum_mul]
    calc ∑ a ∈ Icc 1 (Q - 1), (1 : ℝ) / a * roughHarmonic Q N
        ≤ ∑ a ∈ Icc 1 (Q - 1), ∑ b ∈ roughInterval Q (N * N / a), (1 : ℝ) / ((a * b : ℕ) : ℝ) := by
          refine sum_le_sum fun a ha => ?_
          obtain ⟨ha1, haQ⟩ := mem_Icc.mp ha
          rw [roughHarmonic, mul_sum]
          have hsub : roughInterval Q N ⊆ roughInterval Q (N * N / a) :=
            roughInterval_mono ((Nat.le_div_iff_mul_le (by omega)).mpr
              (Nat.mul_le_mul_left N (by omega)))
          refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans'
            (le_of_eq (sum_congr rfl fun b _ => ?_))
          push_cast
          field_simp
      _ ≤ ∑ a ∈ smoothSet Q (N * N), ∑ b ∈ roughInterval Q (N * N / a),
            (1 : ℝ) / ((a * b : ℕ) : ℝ) := by
          refine sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
            fun _ _ _ => sum_nonneg fun _ _ => by positivity
          obtain ⟨ha1, haQ⟩ := mem_Icc.mp ha
          refine mem_smoothSet.mpr ⟨ha1, le_trans (by omega : a ≤ N) (Nat.le_mul_self N),
            fun p hp => ?_⟩
          have := Nat.le_of_mem_primeFactors hp
          omega
  have hH : ∑ n ∈ Icc 1 (N * N), (1 : ℝ) / n ≤ 1 + 2 * Real.log N := by
    have h := hsum_le (N * N)
    unfold hsum at h
    simp only [one_div]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [Nat.cast_mul, Real.log_mul hN0 hN0] at h
    linarith
  have hHQ : Real.log Q ≤ ∑ a ∈ Icc 1 (Q - 1), (1 : ℝ) / a := by
    have h := log_add_one_le_harmonic (Q - 1)
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel] at h
    simpa [one_div] using h
  have hR := RenormalizedArithmeticPotentialTheory.roughHarmonic_nonneg Q N
  have hdiv : roughHarmonic Q N ≤ (1 + 2 * Real.log N) / Real.log Q := by
    rw [le_div_iff₀ hlQ]
    nlinarith
  linarith

/-- **Rough mass, lower bound**: `F_Q(X) ≥ c log(X + 1)/log Q` for `Q ≥ 3`. -/
theorem exists_roughHarmonic_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ Q : ℕ, 3 ≤ Q → ∀ X : ℕ,
      c * Real.log (X + 1) / Real.log Q ≤ roughHarmonic Q X := by
  obtain ⟨c, hc, hcM⟩ := exists_mertensPrimeProduct_mul_log_ge
  refine ⟨c, hc, fun Q hQ X => ?_⟩
  have hM := mertensPrimeProduct_mul_log_le_roughHarmonic (Q - 1) X
  rw [Nat.sub_add_cancel (by omega)] at hM
  have hcQ := hcM (Q - 1) (by omega)
  have hlQ1 : 0 < Real.log ((Q - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q - 1 by omega))
  have hlQ : Real.log ((Q - 1 : ℕ) : ℝ) ≤ Real.log Q :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q - 1 by omega))
      (by exact_mod_cast Nat.sub_le Q 1)
  have hX : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  have hP : c / Real.log Q ≤ RHTower.mertensPrimeProduct (Q - 1) := by
    rw [div_le_iff₀ (hlQ1.trans_le hlQ)]
    calc c ≤ RHTower.mertensPrimeProduct (Q - 1) * Real.log ((Q - 1 : ℕ) : ℝ) := hcQ
      _ ≤ RHTower.mertensPrimeProduct (Q - 1) * Real.log Q :=
          mul_le_mul_of_nonneg_left hlQ
            (RenormalizedArithmeticPotentialTheory.mertensPrimeProduct_pos _).le
  calc c * Real.log (X + 1) / Real.log Q = Real.log (X + 1) * (c / Real.log Q) := by ring
    _ ≤ Real.log (X + 1) * RHTower.mertensPrimeProduct (Q - 1) :=
        mul_le_mul_of_nonneg_left hP hX
    _ ≤ roughHarmonic Q X := hM

/-- **The `Q`-smooth harmonic sum is `O(log Q)`**: `Σ_{a ≤ N, Q-smooth} 1/a ≤ K log Q`. -/
theorem exists_sum_smoothSet_inv_le :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : ℕ, 3 ≤ Q → ∀ N : ℕ,
      ∑ a ∈ smoothSet Q N, (1 : ℝ) / a ≤ K * Real.log Q := by
  obtain ⟨c, hc, hR⟩ := exists_roughHarmonic_ge
  refine ⟨4 / c, by positivity, fun Q hQ N => ?_⟩
  have hlQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [smoothSet]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlN1 : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  -- `(Σ 1/a) F_Q(N) ≤ H(N²) ≤ 1 + 2 log N`
  have hfib : (∑ a ∈ smoothSet Q N, (1 : ℝ) / a) * roughHarmonic Q N ≤ 1 + 2 * Real.log N := by
    have hH : ∑ n ∈ Icc 1 (N * N), (1 : ℝ) / n ≤ 1 + 2 * Real.log N := by
      have h := hsum_le (N * N)
      unfold hsum at h
      simp only [one_div]
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      rw [Nat.cast_mul, Real.log_mul hN0 hN0] at h
      linarith
    refine le_trans ?_ hH
    rw [sum_Icc_eq_smooth_rough Q (N * N), sum_mul]
    calc ∑ a ∈ smoothSet Q N, (1 : ℝ) / a * roughHarmonic Q N
        ≤ ∑ a ∈ smoothSet Q N, ∑ b ∈ roughInterval Q (N * N / a), (1 : ℝ) / ((a * b : ℕ) : ℝ) := by
          refine sum_le_sum fun a ha => ?_
          obtain ⟨ha1, haN, -⟩ := mem_smoothSet.mp ha
          rw [roughHarmonic, mul_sum]
          have hsub : roughInterval Q N ⊆ roughInterval Q (N * N / a) :=
            roughInterval_mono ((Nat.le_div_iff_mul_le (by omega)).mpr
              (Nat.mul_le_mul_left N haN))
          refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans'
            (le_of_eq (sum_congr rfl fun b _ => ?_))
          push_cast
          field_simp
      _ ≤ ∑ a ∈ smoothSet Q (N * N), ∑ b ∈ roughInterval Q (N * N / a),
            (1 : ℝ) / ((a * b : ℕ) : ℝ) := by
          refine sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
            fun _ _ _ => sum_nonneg fun _ _ => by positivity
          obtain ⟨ha1, haN, hap⟩ := mem_smoothSet.mp ha
          exact mem_smoothSet.mpr ⟨ha1, haN.trans (Nat.le_mul_self N), hap⟩
  have hRN := hR Q hQ N
  have hS0 : 0 ≤ ∑ a ∈ smoothSet Q N, (1 : ℝ) / a := sum_nonneg fun _ _ => by positivity
  have hlN : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast hN) (by linarith)
  have hl2 : Real.log 2 ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hl2' := Real.log_two_gt_d9
  -- `(1 + 2 log N)/log(N + 1) ≤ 4`
  have hratio : 1 + 2 * Real.log N ≤ 4 * Real.log ((N : ℝ) + 1) := by linarith
  have hmain : (∑ a ∈ smoothSet Q N, (1 : ℝ) / a) * (c * Real.log ((N : ℝ) + 1) / Real.log Q) ≤
      4 * Real.log ((N : ℝ) + 1) :=
    (mul_le_mul_of_nonneg_left hRN hS0).trans (hfib.trans hratio)
  rw [show (∑ a ∈ smoothSet Q N, (1 : ℝ) / a) * (c * Real.log ((N : ℝ) + 1) / Real.log Q) =
    (∑ a ∈ smoothSet Q N, (1 : ℝ) / a) * c / Real.log Q * Real.log ((N : ℝ) + 1) by ring] at hmain
  have h4 := le_of_mul_le_mul_right hmain hlN1
  rw [div_le_iff₀ hlQ] at h4
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith

end Mass

section Gronwall

/-- One telescoping step: for `0 < ℓ ≤ ℓ' ≤ 2ℓ` and `0 < a ≤ 2`,
`(ℓ' − ℓ)/ℓ^{1+a} ≤ (8/a)(ℓ^{−a} − ℓ'^{−a})`. -/
theorem sub_div_rpow_le_telescope {ℓ ℓ' a : ℝ} (hℓ : 0 < ℓ) (hle : ℓ ≤ ℓ') (h2 : ℓ' ≤ 2 * ℓ)
    (ha : 0 < a) (ha2 : a ≤ 2) :
    (ℓ' - ℓ) / ℓ ^ (1 + a) ≤ 8 / a * (ℓ ^ (-a) - ℓ' ^ (-a)) := by
  have hℓ' : 0 < ℓ' := hℓ.trans_le hle
  -- `ℓ^{−a} − ℓ'^{−a} ≥ a (ℓ' − ℓ) ℓ'^{−1−a}` from `r^{−a} = e^{−a log r} ≥ 1 + a(1 − r)`
  have hr : 0 < ℓ / ℓ' := div_pos hℓ hℓ'
  have hexp : 1 + a * (1 - ℓ / ℓ') ≤ (ℓ / ℓ') ^ (-a) := by
    rw [Real.rpow_def_of_pos hr]
    have hlog := Real.log_le_sub_one_of_pos hr
    have := Real.add_one_le_exp (Real.log (ℓ / ℓ') * -a)
    nlinarith
  have hsplit : ℓ ^ (-a) = ℓ' ^ (-a) * (ℓ / ℓ') ^ (-a) := by
    have h0 := (Real.rpow_pos_of_pos hℓ' (-a)).ne'
    rw [Real.div_rpow hℓ.le hℓ'.le]
    field_simp
  have hpow : ℓ' ^ (1 + a) = ℓ' * ℓ' ^ a := by
    rw [Real.rpow_add hℓ', Real.rpow_one]
  have hneg : ℓ' ^ (-a) = 1 / ℓ' ^ a := by rw [Real.rpow_neg hℓ'.le, one_div]
  have hpa : 0 < ℓ' ^ a := Real.rpow_pos_of_pos hℓ' a
  have hkey : a * (ℓ' - ℓ) / ℓ' ^ (1 + a) ≤ ℓ ^ (-a) - ℓ' ^ (-a) := by
    rw [hsplit, hpow, hneg]
    have e : a * (ℓ' - ℓ) / (ℓ' * ℓ' ^ a) = 1 / ℓ' ^ a * (a * (1 - ℓ / ℓ')) := by
      field_simp
    rw [e]
    have hpos : 0 ≤ 1 / ℓ' ^ a := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hexp hpos]
  -- `ℓ'^{1+a} ≤ 8 ℓ^{1+a}`
  have h8 : ℓ' ^ (1 + a) ≤ 8 * ℓ ^ (1 + a) := by
    calc ℓ' ^ (1 + a) ≤ (2 * ℓ) ^ (1 + a) :=
          Real.rpow_le_rpow hℓ'.le h2 (by linarith)
      _ = 2 ^ (1 + a) * ℓ ^ (1 + a) := Real.mul_rpow (by norm_num) hℓ.le
      _ ≤ 2 ^ (3 : ℝ) * ℓ ^ (1 + a) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hℓ.le _)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 * ℓ ^ (1 + a) := by norm_num
  have hpl : 0 < ℓ ^ (1 + a) := Real.rpow_pos_of_pos hℓ _
  have hpl' : 0 < ℓ' ^ (1 + a) := Real.rpow_pos_of_pos hℓ' _
  have hd : 0 ≤ ℓ' - ℓ := by linarith
  calc (ℓ' - ℓ) / ℓ ^ (1 + a) ≤ 8 * (ℓ' - ℓ) / ℓ' ^ (1 + a) := by
        rw [div_le_div_iff₀ hpl hpl']
        nlinarith
    _ = 8 / a * (a * (ℓ' - ℓ) / ℓ' ^ (1 + a)) := by field_simp
    _ ≤ 8 / a * (ℓ ^ (-a) - ℓ' ^ (-a)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

/-- `Σ_{Q ≤ n < Y} Δlog n/(log n)^{1+a} ≤ (8/a)(log Q)^{−a}` for `Q ≥ 2`, `0 < a ≤ 2`. -/
theorem sum_Ico_logIncrement_div_rpow_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) {Q : ℕ} (hQ : 2 ≤ Q)
    (Y : ℕ) :
    ∑ n ∈ Ico Q Y, (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log n ^ (1 + a) ≤
      8 / a * Real.log Q ^ (-a) := by
  have hterm : ∀ n ∈ Ico Q Y, (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log n ^ (1 + a) ≤
      8 / a * (Real.log n ^ (-a) - Real.log ((n : ℝ) + 1) ^ (-a)) := by
    intro n hn
    have hn2 : 2 ≤ n := hQ.trans (mem_Ico.mp hn).1
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hl : 0 < Real.log n := Real.log_pos (by linarith)
    refine sub_div_rpow_le_telescope hl (Real.log_le_log (by linarith) (by linarith)) ?_ ha ha2
    rw [← Real.log_rpow (by linarith), Real.rpow_two]
    exact Real.log_le_log (by linarith) (by nlinarith)
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rcases le_or_gt Y Q with hYQ | hYQ
  · rw [Ico_eq_empty_of_le hYQ, sum_empty]
    exact Real.rpow_nonneg (Real.log_natCast_nonneg Q) _
  · have htel : ∀ Z, Q ≤ Z → ∑ n ∈ Ico Q Z, (Real.log n ^ (-a) -
        Real.log ((n : ℝ) + 1) ^ (-a)) = Real.log Q ^ (-a) - Real.log Z ^ (-a) := by
      intro Z hZ
      induction Z, hZ using Nat.le_induction with
      | base => simp
      | succ Z hZ ih => rw [sum_Ico_succ_top hZ, ih]; push_cast; ring
    rw [htel Y hYQ.le]
    have := Real.rpow_nonneg (Real.log_natCast_nonneg Y) (-a)
    linarith

/-- **The integrating factor.** Let `s(n) ≤ 1` for `n < Q` and, for `Y ≥ Q`,
`s(Y) log Y ≤ (1 + β) I(Y) + f(Y)` with `I(Y) = Σ_{1 ≤ n < Y} s(n) Δlog n` and `f ≥ 0`. Then
`I(Y) ≤ ((log Q)^{−β} + Σ_{Q ≤ n < Y} Δlog n f(n)/(log n)^{2+β}) (log Y)^{1+β}`: by Bernoulli,
`I/(log Y)^{1+β}` grows per step by at most `Δlog Y f(Y)/(log Y)^{2+β}`. -/
theorem integrating_factor_le {s f : ℕ → ℝ} {β : ℝ} (hβ : 0 < β) {Q : ℕ} (hQ : 3 ≤ Q)
    (hsmall : ∀ n, n < Q → s n ≤ 1) (hf0 : ∀ n, Q ≤ n → 0 ≤ f n)
    (heq : ∀ Y, Q ≤ Y → s Y * Real.log Y ≤
      (1 + β) * ∑ n ∈ Ico 1 Y, s n * (Real.log ((n : ℝ) + 1) - Real.log n) + f Y) :
    ∀ Y, Q ≤ Y → ∑ n ∈ Ico 1 Y, s n * (Real.log ((n : ℝ) + 1) - Real.log n) ≤
      (Real.log Q ^ (-β) + ∑ n ∈ Ico Q Y, (Real.log ((n : ℝ) + 1) - Real.log n) * f n /
        Real.log n ^ (2 + β)) * Real.log Y ^ (1 + β) := by
  set L := Real.log Q with hLdef
  have hL1 : 1 ≤ L := one_le_log_of_three_le hQ
  have hL0 : 0 < L := by linarith
  set δ : ℕ → ℝ := fun n => Real.log ((n : ℝ) + 1) - Real.log n
  have hδ : ∀ n, 1 ≤ n → 0 ≤ δ n := fun n hn => sub_nonneg.mpr
    (Real.log_le_log (by exact_mod_cast hn) (by linarith))
  set I : ℕ → ℝ := fun Y => ∑ n ∈ Ico 1 Y, s n * δ n
  set T : ℕ → ℝ := fun Y => ∑ n ∈ Ico Q Y, δ n * f n / Real.log n ^ (2 + β)
  have hT0 : ∀ Y, 0 ≤ T Y := fun Y => sum_nonneg fun n hn => by
    have hn3 : 3 ≤ n := hQ.trans (mem_Ico.mp hn).1
    have hl : 0 < Real.log n := by have := one_le_log_of_three_le hn3; linarith
    exact div_nonneg (mul_nonneg (hδ n (by omega)) (hf0 n (mem_Ico.mp hn).1))
      (Real.rpow_nonneg hl.le _)
  intro Y hY
  induction Y, hY using Nat.le_induction with
  | base =>
    have hIQ : I Q ≤ L := by
      calc I Q ≤ ∑ n ∈ Ico 1 Q, δ n := sum_le_sum fun n hn => by
            have hn' := mem_Ico.mp hn
            have := hsmall n hn'.2
            nlinarith [hδ n hn'.1]
        _ = L := by
            have h := sum_range_log_succ_sub Q
            rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)] at h
            simp only [Nat.cast_zero, Real.log_zero, sub_zero, zero_add] at h
            simpa [δ] using h
    have hT : T Q = 0 := by simp [T]
    change I Q ≤ (L ^ (-β) + T Q) * Real.log Q ^ (1 + β)
    rw [hT, add_zero, ← hLdef, ← Real.rpow_add hL0, show -β + (1 + β) = 1 by ring, Real.rpow_one]
    exact hIQ
  | succ Y hY ih =>
    change I (Y + 1) ≤ (L ^ (-β) + T (Y + 1)) * Real.log ((Y + 1 : ℕ) : ℝ) ^ (1 + β)
    change I Y ≤ (L ^ (-β) + T Y) * Real.log Y ^ (1 + β) at ih
    have hY3 : 3 ≤ Y := hQ.trans hY
    have hl1 : 1 ≤ Real.log Y := one_le_log_of_three_le hY3
    have hl : 0 < Real.log Y := by linarith
    set ℓ := Real.log Y
    have hδY := hδ Y (by omega)
    have hℓ' : Real.log ((Y + 1 : ℕ) : ℝ) = ℓ + δ Y := by
      simp only [δ, ℓ]; push_cast; ring
    have hτ0 : 0 ≤ L ^ (-β) + T Y := add_nonneg (Real.rpow_nonneg hL0.le _) (hT0 Y)
    set τ := L ^ (-β) + T Y
    have hfY := hf0 Y hY
    have hsY : s Y ≤ ((1 + β) * I Y + f Y) / ℓ := by
      rw [le_div_iff₀ hl]; exact heq Y hY
    have hIs : I (Y + 1) = I Y + s Y * δ Y := by
      simp only [I]; rw [sum_Ico_succ_top (by omega)]
    have hTs : T (Y + 1) = T Y + δ Y * f Y / ℓ ^ (2 + β) := by
      simp only [T]; rw [sum_Ico_succ_top hY]
    have hB := rpow_add_mul_le hl hδY (show 1 ≤ 1 + β by linarith)
    rw [show 1 + β - 1 = β by ring] at hB
    have hmono : ℓ ^ (1 + β) ≤ (ℓ + δ Y) ^ (1 + β) :=
      Real.rpow_le_rpow hl.le (by linarith) (by linarith)
    have hpow2 : ℓ ^ (2 + β) = ℓ * ℓ ^ (1 + β) := by
      rw [show 2 + β = 1 + (1 + β) by ring, Real.rpow_add hl, Real.rpow_one]
    have hpow1 : ℓ ^ (1 + β) = ℓ * ℓ ^ β := by
      rw [Real.rpow_add hl, Real.rpow_one]
    have hpb : 0 < ℓ ^ β := Real.rpow_pos_of_pos hl β
    have hp1 : 0 < ℓ ^ (1 + β) := Real.rpow_pos_of_pos hl _
    rw [hIs, hTs, hℓ']
    have hstep1 : I Y + s Y * δ Y ≤ I Y + ((1 + β) * I Y + f Y) / ℓ * δ Y :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hsY hδY)
    refine hstep1.trans ?_
    have hI1 : I Y + (1 + β) * I Y / ℓ * δ Y ≤ τ * (ℓ + δ Y) ^ (1 + β) := by
      have e : I Y + (1 + β) * I Y / ℓ * δ Y = I Y * (1 + (1 + β) * δ Y / ℓ) := by
        field_simp
      rw [e]
      have hfac : 0 ≤ 1 + (1 + β) * δ Y / ℓ := by positivity
      calc I Y * (1 + (1 + β) * δ Y / ℓ) ≤ τ * ℓ ^ (1 + β) * (1 + (1 + β) * δ Y / ℓ) :=
            mul_le_mul_of_nonneg_right ih hfac
        _ = τ * (ℓ ^ (1 + β) + (1 + β) * δ Y * ℓ ^ β) := by
            rw [hpow1]; field_simp
        _ ≤ τ * (ℓ + δ Y) ^ (1 + β) := mul_le_mul_of_nonneg_left hB hτ0
    have hF : f Y / ℓ * δ Y ≤ δ Y * f Y / ℓ ^ (2 + β) * (ℓ + δ Y) ^ (1 + β) := by
      rw [hpow2]
      have e : f Y / ℓ * δ Y = δ Y * f Y / (ℓ * ℓ ^ (1 + β)) * ℓ ^ (1 + β) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    have e2 : I Y + ((1 + β) * I Y + f Y) / ℓ * δ Y =
        (I Y + (1 + β) * I Y / ℓ * δ Y) + f Y / ℓ * δ Y := by ring
    rw [e2]
    calc _ ≤ τ * (ℓ + δ Y) ^ (1 + β) + δ Y * f Y / ℓ ^ (2 + β) * (ℓ + δ Y) ^ (1 + β) :=
          add_le_add hI1 hF
      _ = (L ^ (-β) + (T Y + δ Y * f Y / ℓ ^ (2 + β))) * (ℓ + δ Y) ^ (1 + β) := by
          simp only [τ]; ring

/-- `ℓ^α/L ≤ (ℓ/L)^β` for `1 ≤ L ≤ ℓ`, `0 ≤ α ≤ β`, `α ≤ 1`. -/
theorem rpow_div_le_div_rpow {ℓ L α β : ℝ} (hL : 1 ≤ L) (hLℓ : L ≤ ℓ) (hαβ : α ≤ β)
    (hα1 : α ≤ 1) : ℓ ^ α / L ≤ (ℓ / L) ^ β := by
  have hL0 : 0 < L := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  rw [Real.div_rpow hℓ0.le hL0.le, div_le_div_iff₀ hL0 (Real.rpow_pos_of_pos hL0 β)]
  have h1 : ℓ ^ α ≤ ℓ ^ β * L ^ (α - β) := by
    have : ℓ ^ (α - β) ≤ L ^ (α - β) := Real.rpow_le_rpow_of_nonpos hL0 hLℓ (by linarith)
    calc ℓ ^ α = ℓ ^ β * ℓ ^ (α - β) := by rw [← Real.rpow_add hℓ0]; congr 1; ring
      _ ≤ ℓ ^ β * L ^ (α - β) := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hℓ0.le _)
  have h2 : L ^ (α - β) * L ^ β ≤ L := by
    rw [← Real.rpow_add hL0, sub_add_cancel]
    calc L ^ α ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL hα1
      _ = L := Real.rpow_one L
  calc ℓ ^ α * L ^ β ≤ ℓ ^ β * L ^ (α - β) * L ^ β :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hL0.le _)
    _ = ℓ ^ β * (L ^ (α - β) * L ^ β) := by ring
    _ ≤ ℓ ^ β * L := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hℓ0.le _)

/-- The forcing sum: `Σ_{Q ≤ n < Y} Δlog n (K(L + log n) + K₂ (log n)^{1+α}/L)/(log n)^{2+β}
≤ (K (8/(1 + β) + 8/β) + K₂ · 8/(β − α)) L^{−β}`, `L = log Q`. -/
theorem sum_forcing_le {β K K₂ α : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hK : 0 ≤ K) (hK₂ : 0 ≤ K₂)
    (hα0 : 0 ≤ α) (hαβ : α < β) {Q : ℕ} (hQ : 3 ≤ Q) (Y : ℕ) :
    ∑ n ∈ Ico Q Y, (Real.log ((n : ℝ) + 1) - Real.log n) *
        (K * (Real.log Q + Real.log n) + K₂ * Real.log n ^ (1 + α) / Real.log Q) /
          Real.log n ^ (2 + β) ≤
      (K * (8 / (1 + β) + 8 / β) + K₂ * (8 / (β - α))) * Real.log Q ^ (-β) := by
  set L := Real.log Q
  have hL1 : 1 ≤ L := one_le_log_of_three_le hQ
  have hL0 : 0 < L := by linarith
  set δ : ℕ → ℝ := fun n => Real.log ((n : ℝ) + 1) - Real.log n
  have h1 := sum_Ico_logIncrement_div_rpow_le (a := 1 + β) (by linarith) (by linarith)
    (show 2 ≤ Q by omega) Y
  have h2 := sum_Ico_logIncrement_div_rpow_le (a := β) hβ (by linarith) (show 2 ≤ Q by omega) Y
  have h3 := sum_Ico_logIncrement_div_rpow_le (a := β - α) (by linarith) (by linarith)
    (show 2 ≤ Q by omega) Y
  have hsplit : ∑ n ∈ Ico Q Y, δ n * (K * (L + Real.log n) + K₂ * Real.log n ^ (1 + α) / L) /
      Real.log n ^ (2 + β) = K * (L * ∑ n ∈ Ico Q Y, δ n / Real.log n ^ (1 + (1 + β)) +
        ∑ n ∈ Ico Q Y, δ n / Real.log n ^ (1 + β)) +
          K₂ / L * ∑ n ∈ Ico Q Y, δ n / Real.log n ^ (1 + (β - α)) := by
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn : 3 ≤ n := hQ.trans (mem_Ico.mp hn).1
    have hl : 0 < Real.log n := by have := one_le_log_of_three_le hn; linarith
    have e1 : Real.log n ^ (2 + β) = Real.log n * Real.log n ^ (1 + β) := by
      rw [show 2 + β = 1 + (1 + β) by ring, Real.rpow_add hl, Real.rpow_one]
    have e2 : Real.log n ^ (1 + (1 + β)) = Real.log n ^ (2 + β) := by congr 1; ring
    have e3 : Real.log n ^ (2 + β) = Real.log n ^ (1 + α) * Real.log n ^ (1 + (β - α)) := by
      rw [← Real.rpow_add hl]; congr 1; ring
    have hp1 : 0 < Real.log n ^ (1 + β) := Real.rpow_pos_of_pos hl _
    have hp2 : 0 < Real.log n ^ (1 + α) := Real.rpow_pos_of_pos hl _
    have hp3 : 0 < Real.log n ^ (1 + (β - α)) := Real.rpow_pos_of_pos hl _
    rw [e2]
    have hlhs : δ n * (K * (L + Real.log n) + K₂ * Real.log n ^ (1 + α) / L) / Real.log n ^ (2 + β) =
        K * L * (δ n / Real.log n ^ (2 + β)) + K * (δ n * Real.log n / Real.log n ^ (2 + β)) +
          K₂ / L * (δ n * Real.log n ^ (1 + α) / Real.log n ^ (2 + β)) := by
      field_simp
    rw [hlhs]
    have hb : δ n * Real.log n / Real.log n ^ (2 + β) = δ n / Real.log n ^ (1 + β) := by
      rw [e1]; field_simp
    have hc : δ n * Real.log n ^ (1 + α) / Real.log n ^ (2 + β) =
        δ n / Real.log n ^ (1 + (β - α)) := by
      rw [e3]; field_simp
    rw [hb, hc]
    ring
  rw [hsplit]
  have hLL : L * L ^ (-(1 + β)) = L ^ (-β) := by
    rw [show -β = 1 + -(1 + β) by ring, Real.rpow_add hL0, Real.rpow_one]
  have hLα : L ^ (-(β - α)) / L ≤ L ^ (-β) := by
    rw [div_le_iff₀ hL0]
    calc L ^ (-(β - α)) ≤ L ^ (-β + 1) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L ^ (-β) * L := by rw [Real.rpow_add hL0, Real.rpow_one]
  have hK₂L : 0 ≤ K₂ / L := div_nonneg hK₂ hL0.le
  calc K * (L * ∑ n ∈ Ico Q Y, δ n / Real.log n ^ (1 + (1 + β)) +
        ∑ n ∈ Ico Q Y, δ n / Real.log n ^ (1 + β)) +
        K₂ / L * ∑ n ∈ Ico Q Y, δ n / Real.log n ^ (1 + (β - α))
      ≤ K * (L * (8 / (1 + β) * L ^ (-(1 + β))) + 8 / β * L ^ (-β)) +
        K₂ / L * (8 / (β - α) * L ^ (-(β - α))) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left h1 hL0.le) h2) hK)
          (mul_le_mul_of_nonneg_left h3 hK₂L)
    _ = K * (8 / (1 + β) + 8 / β) * L ^ (-β) + K₂ * (8 / (β - α)) * (L ^ (-(β - α)) / L) := by
        rw [show L * (8 / (1 + β) * L ^ (-(1 + β))) = 8 / (1 + β) * (L * L ^ (-(1 + β))) by ring,
          hLL]
        ring
    _ ≤ K * (8 / (1 + β) + 8 / β) * L ^ (-β) + K₂ * (8 / (β - α)) * L ^ (-β) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hLα (by
          have : 0 < β - α := by linarith
          positivity))
    _ = _ := by ring

/-- **Sharp discrete Grönwall.** Let `s(n) ≤ 1` for `n < Q`, and for `Y ≥ Q`
`s(Y) log Y ≤ (1 + β) I(Y) + K (log Q + log Y) + K₂ (log Y)^{1+α}/log Q` with
`I(Y) = Σ_{1 ≤ n < Y} s(n) Δlog n`, `0 ≤ α < β ≤ 1`. Then for `Y ≥ Q`
`s(Y) ≤ ((1 + β) D + K₂)(log Y/log Q)^β + 2K`, `D = 1 + K (8/(1 + β) + 8/β) + K₂ · 8/(β − α)`. -/
theorem le_of_sharp_wirsing {s : ℕ → ℝ} {β K K₂ α : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hK : 0 ≤ K)
    (hK₂ : 0 ≤ K₂) (hα0 : 0 ≤ α) (hαβ : α < β) {Q : ℕ} (hQ : 3 ≤ Q)
    (hsmall : ∀ n, n < Q → s n ≤ 1)
    (heq : ∀ Y, Q ≤ Y → s Y * Real.log Y ≤
      (1 + β) * ∑ n ∈ Ico 1 Y, s n * (Real.log ((n : ℝ) + 1) - Real.log n) +
        (K * (Real.log Q + Real.log Y) + K₂ * Real.log Y ^ (1 + α) / Real.log Q)) {Y : ℕ}
    (hY : Q ≤ Y) :
    s Y ≤ ((1 + β) * (1 + K * (8 / (1 + β) + 8 / β) + K₂ * (8 / (β - α))) + K₂) *
      (Real.log Y / Real.log Q) ^ β + 2 * K := by
  set L := Real.log Q with hLdef
  have hL1 : 1 ≤ L := one_le_log_of_three_le hQ
  have hL0 : 0 < L := by linarith
  have hf0 : ∀ n, Q ≤ n → 0 ≤ K * (L + Real.log n) + K₂ * Real.log n ^ (1 + α) / L :=
    fun n _ => add_nonneg (mul_nonneg hK (by linarith [Real.log_natCast_nonneg n]))
      (div_nonneg (mul_nonneg hK₂ (Real.rpow_nonneg (Real.log_natCast_nonneg n) _)) hL0.le)
  have hclaim := integrating_factor_le (f := fun n => K * (L + Real.log n) +
    K₂ * Real.log n ^ (1 + α) / L) hβ hQ hsmall hf0 heq Y hY
  have hTb := sum_forcing_le hβ hβ1 hK hK₂ hα0 hαβ hQ Y
  have hY3 : 3 ≤ Y := hQ.trans hY
  have hl1 : 1 ≤ Real.log Y := one_le_log_of_three_le hY3
  have hl : 0 < Real.log Y := by linarith
  have hLY : L ≤ Real.log Y := Real.log_le_log (by positivity) (by exact_mod_cast hY)
  set D := 1 + K * (8 / (1 + β) + 8 / β) + K₂ * (8 / (β - α))
  set I := ∑ n ∈ Ico 1 Y, s n * (Real.log ((n : ℝ) + 1) - Real.log n)
  have hIY : I ≤ D * L ^ (-β) * Real.log Y ^ (1 + β) := by
    refine hclaim.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hl.le _))
    simp only [D]
    nlinarith [Real.rpow_nonneg hL0.le (-β)]
  have hsY : s Y * Real.log Y ≤ (1 + β) * (D * L ^ (-β) * Real.log Y ^ (1 + β)) +
      (K * (L + Real.log Y) + K₂ * Real.log Y ^ (1 + α) / L) :=
    (heq Y hY).trans (add_le_add (mul_le_mul_of_nonneg_left hIY (by linarith)) le_rfl)
  have hratio : L ^ (-β) * Real.log Y ^ (1 + β) = (Real.log Y / L) ^ β * Real.log Y := by
    rw [Real.div_rpow hl.le hL0.le, Real.rpow_add hl, Real.rpow_one, Real.rpow_neg hL0.le]
    field_simp
  have hK₂term : K₂ * Real.log Y ^ (1 + α) / L ≤ K₂ * (Real.log Y / L) ^ β * Real.log Y := by
    have h := rpow_div_le_div_rpow hL1 hLY hαβ.le (by linarith)
    have e : K₂ * Real.log Y ^ (1 + α) / L = K₂ * (Real.log Y ^ α / L) * Real.log Y := by
      rw [Real.rpow_add hl, Real.rpow_one]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hK₂) hl.le
  rw [show (1 + β) * (D * L ^ (-β) * Real.log Y ^ (1 + β)) =
    (1 + β) * D * (L ^ (-β) * Real.log Y ^ (1 + β)) by ring, hratio] at hsY
  have hKL : K * (L + Real.log Y) ≤ 2 * K * Real.log Y := by nlinarith
  have hfin : s Y * Real.log Y ≤
      (((1 + β) * D + K₂) * (Real.log Y / L) ^ β + 2 * K) * Real.log Y := by nlinarith
  exact le_of_mul_le_mul_right hfin hl

end Gronwall

section Uniform

variable {ω : ℕ → ℝ}

/-- The forcing of the rough Wirsing equation (real form):
`(2CP + βL + C')(1 + W) + 2β ≤ (12C + 3C' + 5β)(L + ℓ) + 8C ℓ^{1+α}/L` when `P ≤ 2ℓ^α`,
`ℓ^α ≤ ℓ` and `1 + W ≤ 3 + 2ℓ/L`, `1 ≤ L`, `1 ≤ ℓ`. -/
theorem rough_forcing_le {C P β L ℓ W Cpp α : ℝ} (hC : 0 ≤ C) (hCpp : 0 ≤ Cpp) (hβ : 0 < β)
    (hL1 : 1 ≤ L) (hℓ1 : 1 ≤ ℓ) (hP0 : 0 ≤ P) (hPα : P ≤ 2 * ℓ ^ α) (hlα : ℓ ^ α ≤ ℓ)
    (hW' : 1 + W ≤ 3 + 2 * ℓ / L) :
    (2 * (C * P) + β * L + Cpp) * (1 + W) + 2 * |β| ≤
      (12 * C + 3 * Cpp + 5 * β) * (L + ℓ) + 8 * C * ℓ ^ (1 + α) / L := by
  rw [abs_of_pos hβ]
  have hL0 : 0 < L := by linarith
  have hℓα0 : 0 ≤ ℓ ^ α := Real.rpow_nonneg (by linarith) α
  have hCP : 2 * (C * P) * (1 + W) ≤ 12 * C * ℓ + 8 * C * ℓ ^ (1 + α) / L := by
    have h1 : 2 * (C * P) * (1 + W) ≤ 2 * (C * P) * (3 + 2 * ℓ / L) :=
      mul_le_mul_of_nonneg_left hW' (by positivity)
    have h3 : ℓ ^ (1 + α) = ℓ ^ α * ℓ := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]; ring
    have e : 2 * (C * P) * (3 + 2 * ℓ / L) = 6 * (C * P) + 4 * (C * P) * ℓ / L := by ring
    have h4 : 4 * (C * P) * ℓ / L ≤ 8 * C * ℓ ^ (1 + α) / L := by
      refine div_le_div_of_nonneg_right ?_ hL0.le
      rw [h3]
      have := mul_le_mul_of_nonneg_left hPα hC
      nlinarith
    have h5 : 6 * (C * P) ≤ 12 * C * ℓ := by
      have := mul_le_mul_of_nonneg_left hPα hC
      have := mul_le_mul_of_nonneg_left hlα hC
      nlinarith
    linarith
  have hLW : L * (1 + W) ≤ 3 * L + 2 * ℓ := by
    have h := mul_le_mul_of_nonneg_left hW' hL0.le
    have e : L * (3 + 2 * ℓ / L) = 3 * L + 2 * ℓ := by field_simp
    linarith
  have hdiv : 2 * ℓ / L ≤ 2 * ℓ := by rw [div_le_iff₀ hL0]; nlinarith
  have hCW : Cpp * (1 + W) ≤ Cpp * (3 * L + 3 * ℓ) :=
    mul_le_mul_of_nonneg_left (by linarith) hCpp
  have hβW := mul_le_mul_of_nonneg_left hLW hβ.le
  have hβL : 2 * β ≤ 2 * β * L := by nlinarith
  have e : (2 * (C * P) + β * L + Cpp) * (1 + W) =
      2 * (C * P) * (1 + W) + Cpp * (1 + W) + β * (L * (1 + W)) := by ring
  have hCL : 12 * C * ℓ ≤ 12 * C * (L + ℓ) := by nlinarith
  nlinarith

/-- **The rough Wirsing equation.** For the `Q`-rough part `f` of `ω`, `Q ≥ 3`, `Y ≥ Q`:
`|L_f(Y)| log Y ≤ (1 + β) Σ_{n < Y} |L_f(n)| Δlog n + K (log Q + log Y) + K₂ (log Y)^{1+α}/log Q`
with `K = 12C + 3C' + 5β`, `K₂ = 8C`. -/
theorem rough_wirsing_equation_le {ω : ℕ → ℝ}
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (hbd : ∀ n, |ω n| ≤ 1)
    {β C α : ℝ} (hβ : 0 < β) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C * (1 + Real.log n) ^ α)
    {Q : ℕ} (hQ : 3 ≤ Q) {Y : ℕ} (hY : Q ≤ Y) :
    |gaugeHarmonicSum (roughGauge Q ω) Y| * Real.log Y ≤
      (1 + β) * ∑ n ∈ Ico 1 Y, |gaugeHarmonicSum (roughGauge Q ω) n| *
        (Real.log ((n : ℝ) + 1) - Real.log n) +
        ((12 * C + 3 * (2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) + 5 * β) *
          (Real.log Q + Real.log Y) + 8 * C * Real.log Y ^ (1 + α) / Real.log Q) := by
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (hA 1 le_rfl)
  set Cpp := 2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  have hCpp : 0 ≤ Cpp := nonprime_const_nonneg
  set f := roughGauge Q ω
  set L := Real.log Q
  have hL1 : 1 ≤ L := one_le_log_of_three_le hQ
  have hY1 : 1 ≤ Y := by omega
  have hlY1 : 1 ≤ Real.log Y := one_le_log_of_three_le (hQ.trans hY)
  have hlY : 0 ≤ Real.log Y := by linarith
  set P := (1 + Real.log Y) ^ α
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  have hPα : P ≤ 2 * Real.log Y ^ α := by
    calc P ≤ (2 * Real.log Y) ^ α := Real.rpow_le_rpow (by linarith) (by linarith) hα0
      _ = 2 ^ α * Real.log Y ^ α := Real.mul_rpow (by norm_num) hlY
      _ ≤ 2 * Real.log Y ^ α := mul_le_mul_of_nonneg_right
          (by calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
                _ = 2 := Real.rpow_one 2) (Real.rpow_nonneg hlY _)
  have hlα : Real.log Y ^ α ≤ Real.log Y := by
    calc Real.log Y ^ α ≤ Real.log Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlY1 hα1
      _ = Real.log Y := Real.rpow_one _
  have hW := (absHarmonic_roughGauge_le hbd Q Y).trans
    (roughHarmonic_le_one_add_div_log (by omega) Y)
  have hW' : 1 + absHarmonic f Y ≤ 3 + 2 * Real.log Y / L := by
    have : (1 + 2 * Real.log Y) / L ≤ 1 + 2 * Real.log Y / L := by
      rw [add_div]; have : 1 / L ≤ 1 := by rw [div_le_one (by linarith)]; exact hL1
      linarith
    linarith
  have hfA' : ∀ n, 1 ≤ n → n ≤ Y →
      |primeMean f n - β * Real.log n| ≤ 2 * (C * P) + β * L := fun n hn hnY => by
    refine (abs_primeMean_roughGauge_sub_le hβ.le hα0 hA (by omega) hn).trans ?_
    have : (1 + Real.log n) ^ α ≤ P := Real.rpow_le_rpow (by linarith [Real.log_natCast_nonneg n])
      (by have := Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
            (show (n : ℝ) ≤ Y by exact_mod_cast hnY)
          linarith) hα0
    nlinarith
  have hWe := abs_wirsing_equation_le_absHarmonic f (roughGauge_mul hmul Q) (abs_roughGauge_le hbd Q)
    hY1 hfA'
  have hM : |polarMoment f Y| ≤
      ∑ n ∈ Ico 1 Y, |gaugeHarmonicSum f n| * (Real.log ((n : ℝ) + 1) - Real.log n) := by
    rw [polarMoment_eq_sum]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun n hn => ?_))
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith)))]
  have hforce := rough_forcing_le hC hCpp hβ hL1 hlY1 hP0 hPα hlα hW'
  have hfinal : |gaugeHarmonicSum f Y * Real.log Y| ≤ (1 + β) * |polarMoment f Y| +
      ((12 * C + 3 * Cpp + 5 * β) * (L + Real.log Y) + 8 * C * Real.log Y ^ (1 + α) / L) := by
    have := abs_sub_abs_le_abs_sub (gaugeHarmonicSum f Y * Real.log Y) ((1 + β) * polarMoment f Y)
    rw [abs_mul (1 + β), abs_of_pos (by linarith : (0 : ℝ) < 1 + β)] at this
    linarith [hWe.trans hforce]
  rw [abs_mul, abs_of_nonneg hlY] at hfinal
  exact hfinal.trans (add_le_add (mul_le_mul_of_nonneg_left hM (by linarith)) le_rfl)

/-- **The rough Wirsing bound, uniform in the roughness.** If `ω` is completely multiplicative,
`|ω| ≤ 1`, and `Σ_{p ≤ n} ω(p) log p/p = β log n + O((1 + log n)^α)` with `0 ≤ α < β ≤ 1`, then
`|Σ_{r ≤ Y, Q-rough} ω(r)/r| ≤ A (log Y/log Q)^β + B` for all `Q ≥ 3` and `Y`, with `A, B`
independent of `Q`. -/
theorem exists_abs_gaugeHarmonicSum_roughGauge_le
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (hbd : ∀ n, |ω n| ≤ 1)
    {β C α : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hα0 : 0 ≤ α) (hαβ : α < β)
    (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C * (1 + Real.log n) ^ α) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ Q : ℕ, 3 ≤ Q → ∀ Y : ℕ,
      |gaugeHarmonicSum (roughGauge Q ω) Y| ≤ A * (Real.log Y / Real.log Q) ^ β + B := by
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (hA 1 le_rfl)
  have hCpp : 0 ≤ 2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) := nonprime_const_nonneg
  set K := 12 * C + 3 * (2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) + 5 * β
  have hK : 0 ≤ K := by positivity
  set K₂ := 8 * C
  have hK₂ : 0 ≤ K₂ := by positivity
  have hαβ' : 0 < β - α := by linarith
  refine ⟨(1 + β) * (1 + K * (8 / (1 + β) + 8 / β) + K₂ * (8 / (β - α))) + K₂, 2 * K + 1,
    by positivity, by positivity, fun Q hQ Y => ?_⟩
  have hsmall : ∀ n, n < Q → |gaugeHarmonicSum (roughGauge Q ω) n| ≤ 1 := fun n hn =>
    (abs_gaugeHarmonicSum_le_absHarmonic _ n).trans
      ((absHarmonic_roughGauge_le hbd Q n).trans (roughHarmonic_le_one_of_lt hn))
  have hpow0 : 0 ≤ (Real.log Y / Real.log Q) ^ β := Real.rpow_nonneg
    (div_nonneg (Real.log_natCast_nonneg Y) (Real.log_natCast_nonneg Q)) β
  have hA0 : 0 ≤ (1 + β) * (1 + K * (8 / (1 + β) + 8 / β) + K₂ * (8 / (β - α))) + K₂ := by
    positivity
  rcases lt_or_ge Y Q with hYQ | hYQ
  · have := hsmall Y hYQ
    nlinarith [mul_nonneg hA0 hpow0]
  have hG := le_of_sharp_wirsing (s := fun n => |gaugeHarmonicSum (roughGauge Q ω) n|) hβ hβ1 hK
    hK₂ hα0 hαβ hQ hsmall
    (fun Y hY => rough_wirsing_equation_le hmul hbd hβ hα0 (by linarith) hA hQ hY) hYQ
  linarith

end Uniform

end GaloisForLFunctions.RenormalizedIntersectionTheory
