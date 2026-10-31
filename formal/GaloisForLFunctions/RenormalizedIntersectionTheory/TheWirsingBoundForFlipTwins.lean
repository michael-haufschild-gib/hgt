import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.AMarginNeedsHarmonicCorrelation
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The Wirsing bound for flip twins

For a completely multiplicative `ω` with `|ω| ≤ 1` the logarithmic sum
`L(N) = Σ_{n ≤ N} ω(n)/n` (`gaugeHarmonicSum`) obeys a Levin–Fainleib integral equation. With the
**polar moment** `M(N) = Σ_{n ≤ N} (ω(n)/n) log(N/n)` (`polarMoment`):

* `Σ_{n ≤ N} ω(n) log n / n = L(N) log N − M(N)` (`logMoment_eq`), and
  `M(N + 1) = M(N) + L(N) log((N + 1)/N)` (`polarMoment_succ`);
* the Chebyshev identity `log n = Σ_{d ∣ n} Λ(d)` gives
  `Σ_{n ≤ N} ω(n) log n / n = Σ_{d ≤ N} Λ(d) ω(d)/d · L(N/d)` (`logMoment_eq_vonMangoldt`).

If the primes carry the mean `Σ_{p ≤ N} ω(p) log p/p = β log N + O(1)`, the prime terms average `L`
against `β d log t`, the prime powers cost `O(log N)`, and the equation becomes
`L(N) log N = (1 + β) M(N) + O(log N)` (`exists_abs_wirsing_equation_le`). A discrete Gronwall argument
then gives `|L(N)| ≪ (log N)^{b − 1}` for every `b > 1` with `b ≥ |1 + β|`
(`exists_abs_gaugeHarmonicSum_le_rpow`). For `β < 1/2` this is `L(N)² = o(log N)`.

For the flip of a set of primes of relative logarithmic density `κ`, `β = 1 − 2κ`
(`TheWirsingBoundSeparatesTheDenseFlips`).
-/

open Finset Filter
open scoped ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (gaugeHarmonicSum)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The **polar moment** `M(N) = Σ_{n ≤ N} (ω(n)/n) log(N/n)`. -/
def polarMoment (ω : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, ω m / m * Real.log ((N : ℝ) / m)

/-- The **logarithmic moment** `Σ_{n ≤ N} ω(n) log n / n`. -/
def logMoment (ω : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, ω m / m * Real.log m

section Identities

variable (ω : ℕ → ℝ)

theorem logMoment_eq (N : ℕ) :
    logMoment ω N = gaugeHarmonicSum ω N * Real.log N - polarMoment ω N := by
  unfold logMoment polarMoment gaugeHarmonicSum
  rw [sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun m hm => ?_
  have hm0 : (m : ℝ) ≠ 0 := by have := (mem_Icc.mp hm).1; positivity
  have hN0 : (N : ℝ) ≠ 0 := by
    have := (mem_Icc.mp hm).1.trans (mem_Icc.mp hm).2; positivity
  rw [Real.log_div hN0 hm0]
  ring

theorem polarMoment_succ {N : ℕ} (hN : 1 ≤ N) :
    polarMoment ω (N + 1) =
      polarMoment ω N + gaugeHarmonicSum ω N * Real.log (((N : ℝ) + 1) / N) := by
  unfold polarMoment gaugeHarmonicSum
  rw [sum_Icc_succ_top (by omega), sum_mul, ← sum_add_distrib]
  have hlast : ω (N + 1) / ((N + 1 : ℕ) : ℝ) * Real.log (((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) = 0 := by
    rw [div_self (by positivity), Real.log_one, mul_zero]
  rw [hlast, add_zero]
  refine sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by have := (mem_Icc.mp hm).1; exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show (((N + 1 : ℕ) : ℝ) / m) = ((N : ℝ) / m) * (((N : ℝ) + 1) / N) by
    push_cast; field_simp,
    Real.log_mul (by positivity) (by positivity)]
  ring

/-- **The Chebyshev identity for the logarithmic moment.** -/
theorem logMoment_eq_vonMangoldt (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (N : ℕ) :
    logMoment ω N = ∑ d ∈ Icc 1 N, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d) := by
  set f : ℕ → ℂ := fun m => ((ω m / m : ℝ) : ℂ)
  have hf : ∀ a b : ℕ, f (a * b) = f a * f b := by
    intro a b
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [f]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [f]
    simp only [f, hmul a b ha.ne' hb.ne', Nat.cast_mul]
    push_cast
    field_simp
  have h := RHTower.Sieve.sum_mul_log_eq_vonMangoldt hf N
  simp only [f, ← Complex.ofReal_sum, ← Complex.ofReal_mul] at h
  unfold logMoment gaugeHarmonicSum
  exact_mod_cast h

/-- `|L(N)| ≤ 1 + log N`. -/
theorem abs_gaugeHarmonicSum_le (hbd : ∀ n, |ω n| ≤ 1) (N : ℕ) :
    |gaugeHarmonicSum ω N| ≤ 1 + Real.log N := by
  unfold gaugeHarmonicSum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h : ∑ m ∈ Icc 1 N, |ω m / m| ≤ ∑ m ∈ Icc 1 N, ((m : ℝ))⁻¹ := by
    refine sum_le_sum fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by have := (mem_Icc.mp hm).1; exact_mod_cast this
    rw [abs_div, abs_of_pos hm0, div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (hbd m)
  refine h.trans ?_
  have hh := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at hh
  push_cast at hh
  exact hh

end Identities


section Equation

variable {ω : ℕ → ℝ}

/-- Harmonic partial sums `H(n) = Σ_{m ≤ n} 1/m`. -/
def hsum (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, ((m : ℝ))⁻¹

theorem hsum_nonneg (n : ℕ) : 0 ≤ hsum n := sum_nonneg fun _ _ => by positivity

theorem hsum_le (n : ℕ) : hsum n ≤ 1 + Real.log n := by
  have hh := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at hh
  push_cast at hh
  exact hh

theorem sumIcc_eq_sumRange (F : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Icc 1 N, F k = ∑ i ∈ range N, F (i + 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ (fun i => F (i + 1))]

theorem sum_range_log_succ_sub (n : ℕ) :
    ∑ i ∈ range n, (Real.log ((i : ℝ) + 1) - Real.log i) = Real.log n := by
  have h := sum_range_sub (fun i : ℕ => Real.log (i : ℝ)) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Real.log_zero, sub_zero] at h
  exact h

/-- `L` moves by at most the harmonic increment. -/
theorem abs_gaugeHarmonicSum_sub_le (hbd : ∀ n, |ω n| ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    |gaugeHarmonicSum ω b - gaugeHarmonicSum ω a| ≤ hsum b - hsum a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hb : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) := by positivity
    have h1 : |ω (b + 1) / ((b + 1 : ℕ) : ℝ)| ≤ ((b + 1 : ℕ) : ℝ)⁻¹ := by
      rw [abs_div, abs_of_pos hb, div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) (hbd _)
    have eL : gaugeHarmonicSum ω (b + 1) = gaugeHarmonicSum ω b + ω (b + 1) / ((b + 1 : ℕ) : ℝ) := by
      unfold gaugeHarmonicSum; rw [sum_Icc_succ_top (by omega)]
    have eH : hsum (b + 1) = hsum b + ((b + 1 : ℕ) : ℝ)⁻¹ := by
      unfold hsum; rw [sum_Icc_succ_top (by omega)]
    rw [eL, eH]
    calc |gaugeHarmonicSum ω b + ω (b + 1) / ((b + 1 : ℕ) : ℝ) - gaugeHarmonicSum ω a|
        ≤ |gaugeHarmonicSum ω b - gaugeHarmonicSum ω a| + |ω (b + 1) / ((b + 1 : ℕ) : ℝ)| := by
          rw [show gaugeHarmonicSum ω b + ω (b + 1) / ((b + 1 : ℕ) : ℝ) - gaugeHarmonicSum ω a =
            (gaugeHarmonicSum ω b - gaugeHarmonicSum ω a) + ω (b + 1) / ((b + 1 : ℕ) : ℝ) by ring]
          exact abs_add_le _ _
      _ ≤ _ := by linarith

/-- The total variation of `k ↦ L(N/k)` is at most `H(N)`. -/
theorem sum_abs_sub_gaugeHarmonicSum_div_le (hbd : ∀ n, |ω n| ≤ 1) (N : ℕ) :
    ∑ i ∈ range (N - 1),
      |gaugeHarmonicSum ω (N / (i + 1 + 1)) - gaugeHarmonicSum ω (N / (i + 1))| ≤ hsum N := by
  have h : ∀ i ∈ range (N - 1),
      |gaugeHarmonicSum ω (N / (i + 1 + 1)) - gaugeHarmonicSum ω (N / (i + 1))| ≤
        hsum (N / (i + 1)) - hsum (N / (i + 1 + 1)) := fun i _ => by
    rw [abs_sub_comm]
    exact abs_gaugeHarmonicSum_sub_le hbd (Nat.div_le_div_left (by omega) (by omega))
  refine (sum_le_sum h).trans ?_
  rw [sum_range_sub' (fun i => hsum (N / (i + 1)))]
  simp only [zero_add, Nat.div_one]
  linarith [hsum_nonneg (N / (N - 1 + 1))]

/-- The **prime mean** `Σ_{p ≤ n} ω(p) log p / p`. -/
def primeMean (ω : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n with k.Prime, ω k * Real.log k / k

/-- The **log-weighted sum** `Σ_{k ≤ N} (log k − log(k − 1)) L(N/k)`. -/
def logWeightSum (ω : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 N, (Real.log k - Real.log ((k : ℝ) - 1)) * gaugeHarmonicSum ω (N / k)

/-- **Abel summation of the prime terms.** If the prime mean is `β log n + O(C)`, the prime terms of
the Chebyshev identity are `β` times the log-weighted sum, up to `C(1 + H(N))`. -/
theorem abs_primePart_sub_le (hbd : ∀ n, |ω n| ≤ 1) {β C : ℝ}
    (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C) {N : ℕ} (hN : 1 ≤ N) :
    |∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
        β * logWeightSum ω N| ≤ C * (1 + hsum N) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hA 1 le_rfl)
  set a : ℕ → ℝ := fun k => if k.Prime then ω k * Real.log k / k else 0
  set g : ℕ → ℝ := fun i => a (i + 1) - β * (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ))
  set f : ℕ → ℝ := fun i => gaugeHarmonicSum ω (N / (i + 1))
  have hsplit : ∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
      β * logWeightSum ω N = ∑ i ∈ range N, f i • g i := by
    rw [sum_filter, logWeightSum, mul_sum, ← sum_sub_distrib, sumIcc_eq_sumRange]
    refine sum_congr rfl fun i _ => ?_
    simp only [f, g, a, smul_eq_mul, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    split_ifs <;> ring
  -- partial sums of `g` are the prime mean minus `β log`
  have hG : ∀ n, ∑ i ∈ range n, g i = primeMean ω n - β * Real.log n := fun n => by
    simp only [g]
    rw [sum_sub_distrib, ← mul_sum]
    push_cast
    rw [sum_range_log_succ_sub, primeMean, sum_filter, sumIcc_eq_sumRange]
  have hGb : ∀ n, |∑ i ∈ range n, g i| ≤ C := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hC]
    · rw [hG]; exact hA n hn
  rw [hsplit, sum_range_by_parts]
  have hf1 : |f (N - 1)| ≤ 1 := by
    simp only [f, Nat.sub_add_cancel hN, Nat.div_self hN]
    unfold gaugeHarmonicSum
    simp only [Icc_self, sum_singleton, Nat.cast_one, div_one]
    exact hbd 1
  have htv := sum_abs_sub_gaugeHarmonicSum_div_le hbd N
  calc |f (N - 1) • ∑ i ∈ range N, g i -
        ∑ i ∈ range (N - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j|
      ≤ |f (N - 1)| * C + ∑ i ∈ range (N - 1), |f (i + 1) - f i| * C := by
        refine (abs_sub _ _).trans (add_le_add ?_ ((abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun i _ => ?_)))
        · rw [smul_eq_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hGb N) (abs_nonneg _)
        · rw [smul_eq_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hGb _) (abs_nonneg _)
    _ ≤ 1 * C + hsum N * C := by
        rw [← sum_mul]
        refine add_le_add (mul_le_mul_of_nonneg_right hf1 hC)
          (mul_le_mul_of_nonneg_right ?_ hC)
        simpa only [f, Nat.add_assoc] using htv
    _ = C * (1 + hsum N) := by ring

/-- `Σ_{k ≤ K} (log k − log(k − 1)) = log K`. -/
theorem sum_log_sub_log_pred (K : ℕ) :
    ∑ k ∈ Icc 1 K, (Real.log k - Real.log ((k : ℝ) - 1)) = Real.log K := by
  rw [sumIcc_eq_sumRange]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  exact sum_range_log_succ_sub K

/-- **The divisor swap**: `Σ_k (log k − log(k−1)) L(N/k) = Σ_m (ω(m)/m) log⌊N/m⌋`. -/
theorem logWeightSum_eq (N : ℕ) :
    logWeightSum ω N = ∑ m ∈ Icc 1 N, ω m / m * Real.log ((N / m : ℕ) : ℝ) := by
  unfold logWeightSum gaugeHarmonicSum
  simp only [mul_sum]
  rw [sum_comm' (t' := Icc 1 N) (s' := fun m => Icc 1 (N / m))]
  · refine sum_congr rfl fun m _ => ?_
    rw [← sum_log_sub_log_pred (N / m), mul_sum]
    exact sum_congr rfl fun k _ => by ring
  · intro k m
    simp only [mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hkN⟩, hm1, hmk⟩
      have hmk' : m * k ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hmk
      refine ⟨⟨hk1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)⟩, hm1, ?_⟩
      nlinarith
    · rintro ⟨⟨hk1, hkm⟩, hm1, hmN⟩
      have hkm' : k * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hkm
      refine ⟨⟨hk1, by nlinarith⟩, hm1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)⟩

/-- The polar moment and the log-weighted sum differ by at most `2`. -/
theorem abs_polarMoment_sub_logWeightSum_le (hbd : ∀ n, |ω n| ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    |polarMoment ω N - logWeightSum ω N| ≤ 2 := by
  rw [logWeightSum_eq, polarMoment, ← sum_sub_distrib]
  have hterm : ∀ m ∈ Icc 1 N, |ω m / m * Real.log ((N : ℝ) / m) -
      ω m / m * Real.log ((N / m : ℕ) : ℝ)| ≤ 2 / N := fun m hm => by
    obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    set q := N / m with hq
    have hq1 : 1 ≤ q := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    -- `q ≤ N/m < q + 1` and `N ≤ 2 q m`
    have hqm : (q : ℝ) * m ≤ N := by exact_mod_cast Nat.div_mul_le_self N m
    have hlt : (N : ℝ) < ((q : ℝ) + 1) * m := by
      have := Nat.lt_div_mul_add (a := N) (b := m) (by omega)
      have h' : N < (q + 1) * m := by rw [add_mul, one_mul]; simpa [hq] using this
      exact_mod_cast h'
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hy : (q : ℝ) ≤ (N : ℝ) / m := by rw [le_div_iff₀ hm0]; exact hqm
    have hlog0 : 0 ≤ Real.log ((N : ℝ) / m) - Real.log q :=
      sub_nonneg.mpr (Real.log_le_log hq0 hy)
    have hlog1 : Real.log ((N : ℝ) / m) - Real.log q ≤ 2 * m / N := by
      rw [← Real.log_div (by positivity) hq0.ne']
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      have hstep1 : (N : ℝ) / m / q - 1 ≤ 1 / q := by
        rw [div_div, sub_le_iff_le_add, div_le_iff₀ (by positivity)]
        have e : (1 / (q : ℝ) + 1) * (m * q) = m + m * q := by field_simp
        rw [e]; nlinarith
      have hstep2 : 1 / (q : ℝ) ≤ 2 * m / N := by
        rw [div_le_div_iff₀ hq0 hN0]; nlinarith
      linarith
    rw [← mul_sub, abs_mul, abs_of_nonneg hlog0, abs_div, abs_of_pos hm0]
    calc |ω m| / m * (Real.log ((N : ℝ) / m) - Real.log q) ≤ 1 / m * (2 * m / N) := by
          refine mul_le_mul (div_le_div_of_nonneg_right (hbd m) hm0.le) hlog1 hlog0 (by positivity)
      _ = 2 / N := by field_simp
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show ((N + 1 - 1 : ℕ) : ℝ) = N by simp]
  rw [mul_div_cancel₀ _ hN0.ne']

/-- The non-prime terms of `Σ_{d ≤ N} Λ(d)/d` are bounded. -/
theorem sum_vonMangoldt_nonprime_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ d ∈ Icc 1 N with ¬ d.Prime, Λ d / d ≤
      2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) := by
  have h1 := RHTower.Mertens.mertens_first N hN
  have h2 := RHTower.Mertens.mertens_first_prime N hN
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime (fun d => Λ d / d)
  have hprime : ∑ d ∈ Icc 1 N with d.Prime, Λ d / d =
      ∑ n ∈ Icc 1 N with n.Prime, Real.log n / (n : ℝ) :=
    sum_congr rfl fun d hd => by rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hd).2]
  rw [hprime] at hsplit
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The Wirsing equation**: if the prime mean is `β log n + O(1)`, then
`L(N) log N = (1 + β) M(N) + O(1 + log N)`. -/
theorem exists_abs_wirsing_equation_le (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b)
    (hbd : ∀ n, |ω n| ≤ 1) {β C : ℝ} (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |gaugeHarmonicSum ω N * Real.log N - (1 + β) * polarMoment ω N| ≤ K * (1 + Real.log N) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hA 1 le_rfl)
  set Cpp := 2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  refine ⟨2 * |β| + C * 2 + Cpp, fun N hN => ?_⟩
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  -- the Chebyshev identity, split into prime and non-prime terms
  have hcheb := logMoment_eq_vonMangoldt ω hmul N
  rw [logMoment_eq] at hcheb
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime
    (fun d => Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d))
  have hprime : ∑ d ∈ Icc 1 N with d.Prime, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d) =
      ∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) :=
    sum_congr rfl fun d hd => by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hd).2]; ring
  rw [hprime] at hsplit
  -- the non-prime terms
  have hnp : |∑ d ∈ Icc 1 N with ¬ d.Prime, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d)| ≤
      Cpp * (1 + Real.log N) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ (Icc 1 N).filter (fun d => ¬ d.Prime),
        |Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d)| ≤ Λ d / d * (1 + Real.log N) := by
      intro d hd
      have hd1 := (mem_Icc.mp (mem_filter.mp hd).1)
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1.1
      have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
      rw [abs_mul, abs_mul, abs_of_nonneg hΛ, abs_div, abs_of_pos hd0]
      have hL := abs_gaugeHarmonicSum_le ω hbd (N / d)
      have hL' : 1 + Real.log ((N / d : ℕ) : ℝ) ≤ 1 + Real.log N := by
        have h0 : (N / d : ℕ) ≤ N := Nat.div_le_self N d
        rcases Nat.eq_zero_or_pos (N / d) with h | h
        · rw [h, Nat.cast_zero, Real.log_zero]; linarith
        · have h0' : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast h0
          have hpos : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast h
          have := Real.log_le_log hpos h0'; linarith
      calc Λ d * (|ω d| / d) * |gaugeHarmonicSum ω (N / d)|
          ≤ Λ d * (1 / d) * (1 + Real.log N) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (hbd d) hd0.le) hΛ) (hL.trans hL') (abs_nonneg _)
              (by positivity)
        _ = Λ d / d * (1 + Real.log N) := by ring
    refine (sum_le_sum hterm).trans ?_
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_vonMangoldt_nonprime_le hN) (by linarith)
  have hab := abs_primePart_sub_le hbd hA hN
  have hpm := abs_polarMoment_sub_logWeightSum_le hbd hN
  have hh := hsum_le N
  -- assemble: `L log N − M = (prime part) + (non-prime part)`
  have heq : gaugeHarmonicSum ω N * Real.log N - (1 + β) * polarMoment ω N =
      (∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
          β * logWeightSum ω N) +
        ∑ d ∈ Icc 1 N with ¬ d.Prime, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d) -
        β * (polarMoment ω N - logWeightSum ω N) := by
    linarith [hcheb, hsplit]
  rw [heq]
  have hβ : |β * (polarMoment ω N - logWeightSum ω N)| ≤ 2 * |β| := by
    rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hpm (abs_nonneg _)
  calc _ ≤ |∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
          β * logWeightSum ω N| +
        |∑ d ∈ Icc 1 N with ¬ d.Prime, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d)| +
        |β * (polarMoment ω N - logWeightSum ω N)| := by
          refine (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C * (1 + hsum N) + Cpp * (1 + Real.log N) + 2 * |β| := add_le_add (add_le_add hab hnp) hβ
    _ ≤ (2 * |β| + C * 2 + Cpp) * (1 + Real.log N) := by
        have h1 : C * (1 + hsum N) ≤ C * 2 * (1 + Real.log N) := by
          nlinarith [mul_le_mul_of_nonneg_left hh hC]
        have h2 : 2 * |β| ≤ 2 * |β| * (1 + Real.log N) := by
          nlinarith [abs_nonneg β]
        nlinarith

end Equation

end GaloisForLFunctions.RenormalizedIntersectionTheory
