import GaloisForLFunctions.RenormalizedIntersectionTheory.TheAtomicHodgeIndexSeparatesExactlyTheSubmaximalMargins
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

If the primes carry the mean `Σ_{p ≤ N} ω(p) log p/p = β log N + O(1)`, Abel summation against
`β d log t` (the total variation of `k ↦ L(N/k)` is at most `H_N`) and the divisor swap turn the prime
terms into `β M(N) + O(log N)`; the prime powers cost `O(log N)`. So
`L(N) log N = (1 + β) M(N) + O(log N)` (`exists_abs_wirsing_equation_le`).

* **Bound** (`exists_abs_gaugeHarmonicSum_le_rpow`): `|L(N)| ≪ (log N)^{b − 1}` for every `b ≥ 1`,
  `b > |1 + β|`: the comparison sequence `A (log N)^b` absorbs the forcing by Bernoulli.
* **Asymptotic** (`exists_abs_gaugeHarmonicSum_sub_rpow_le`): for `0 < β ≤ 1`,
  `L(N) = C (log N)^β + O(1)`: `M/(log N)^{1+β} ± G (log N)^{−β}` are monotone envelopes, since the
  drift of `M/(log N)^{1+β}` is a second-order Bernoulli remainder.

For the flip of a set of primes of relative logarithmic density `κ`, `β = 1 − 2κ`: the harmonic sum is
`C (log N)^{1 − 2κ} + O(1)` for `κ < 1/2`, bounded for `κ > 1/2`, and `o(√log N)` for `κ > 1/4`, where
the atomic Hodge index separates the twin from `ζ`
(`hodgeSeparates_primeSetFlip_of_primeSetLogMass`).
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

/-- **Abel summation of the prime terms.** If the prime mean is `β log n + O(C)` up to `N`, the prime
terms of the Chebyshev identity are `β` times the log-weighted sum, up to `C(1 + H(N))`. -/
theorem abs_primePart_sub_le_of_le (hbd : ∀ n, |ω n| ≤ 1) {β C : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA : ∀ n, 1 ≤ n → n ≤ N → |primeMean ω n - β * Real.log n| ≤ C) :
    |∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
        β * logWeightSum ω N| ≤ C * (1 + hsum N) := by
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
  -- partial sums of `g` are the prime mean minus `β log`
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
  have htv := sum_abs_sub_gaugeHarmonicSum_div_le hbd N
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
    _ ≤ 1 * C + hsum N * C := by
        rw [← sum_mul]
        refine add_le_add (mul_le_mul_of_nonneg_right hf1 hC)
          (mul_le_mul_of_nonneg_right ?_ hC)
        simpa only [f, Nat.add_assoc] using htv
    _ = C * (1 + hsum N) := by ring

theorem abs_primePart_sub_le (hbd : ∀ n, |ω n| ≤ 1) {β C : ℝ}
    (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C) {N : ℕ} (hN : 1 ≤ N) :
    |∑ k ∈ Icc 1 N with k.Prime, ω k * Real.log k / k * gaugeHarmonicSum ω (N / k) -
        β * logWeightSum ω N| ≤ C * (1 + hsum N) :=
  abs_primePart_sub_le_of_le hbd hN fun n hn _ => hA n hn

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

/-- **The Wirsing equation with a power error**: if the prime mean is
`β log n + O((1 + log n)^α)`, `α ≥ 0`, then `L(N) log N = (1 + β) M(N) + O((1 + log N)^{1+α})`. -/
theorem exists_abs_wirsing_equation_le_rpow
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (hbd : ∀ n, |ω n| ≤ 1) {β C α : ℝ}
    (hα : 0 ≤ α)
    (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C * (1 + Real.log n) ^ α) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |gaugeHarmonicSum ω N * Real.log N - (1 + β) * polarMoment ω N| ≤
        K * (1 + Real.log N) ^ (1 + α) := by
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (hA 1 le_rfl)
  set Cpp := 2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  refine ⟨2 * |β| + C * 2 + Cpp, fun N hN => ?_⟩
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set Pα := (1 + Real.log N) ^ α
  have hPα : 1 ≤ Pα := Real.one_le_rpow (by linarith) hα
  have hP1 : (1 + Real.log N) ^ (1 + α) = (1 + Real.log N) * Pα := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
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
  have hab := abs_primePart_sub_le_of_le hbd hN (C := C * Pα) fun n hn hnN => (hA n hn).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (by have := Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
            (show (n : ℝ) ≤ N by exact_mod_cast hnN)
          linarith) hα) hC)
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
    _ ≤ C * Pα * (1 + hsum N) + Cpp * (1 + Real.log N) + 2 * |β| :=
        add_le_add (add_le_add hab hnp) hβ
    _ ≤ (2 * |β| + C * 2 + Cpp) * (1 + Real.log N) ^ (1 + α) := by
        rw [hP1]
        have hCpp : 0 ≤ Cpp := by
          have h := sum_vonMangoldt_nonprime_le (N := 1) le_rfl
          have h0 : (0 : ℝ) ≤ ∑ d ∈ Icc 1 1 with ¬ d.Prime, Λ d / d :=
            sum_nonneg fun d _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
          linarith
        have h1 : C * Pα * (1 + hsum N) ≤ C * 2 * ((1 + Real.log N) * Pα) := by
          have : 1 + hsum N ≤ 2 * (1 + Real.log N) := by linarith
          have := mul_le_mul_of_nonneg_left this (mul_nonneg hC (by linarith : (0 : ℝ) ≤ Pα))
          linarith
        have h2 : Cpp * (1 + Real.log N) ≤ Cpp * ((1 + Real.log N) * Pα) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith) hPα) hCpp
        have h3 : 2 * |β| ≤ 2 * |β| * ((1 + Real.log N) * Pα) := by
          have : 1 ≤ (1 + Real.log N) * Pα := one_le_mul_of_one_le_of_one_le (by linarith) hPα
          nlinarith [abs_nonneg β]
        nlinarith

/-- **The Wirsing equation**: if the prime mean is `β log n + O(1)`, then
`L(N) log N = (1 + β) M(N) + O(1 + log N)`. -/
theorem exists_abs_wirsing_equation_le (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b)
    (hbd : ∀ n, |ω n| ≤ 1) {β C : ℝ} (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |gaugeHarmonicSum ω N * Real.log N - (1 + β) * polarMoment ω N| ≤ K * (1 + Real.log N) := by
  obtain ⟨K, hK⟩ := exists_abs_wirsing_equation_le_rpow hmul hbd (α := 0) le_rfl
    fun n hn => by rw [Real.rpow_zero, mul_one]; exact hA n hn
  exact ⟨K, fun N hN => by simpa using hK N hN⟩

end Equation

section Gronwall

theorem one_le_log_of_three_le {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).le.trans h3

/-- Bernoulli's inequality in the form `ℓ^b + b δ ℓ^{b−1} ≤ (ℓ + δ)^b`. -/
theorem rpow_add_mul_le {ℓ δ b : ℝ} (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hb : 1 ≤ b) :
    ℓ ^ b + b * δ * ℓ ^ (b - 1) ≤ (ℓ + δ) ^ b := by
  have hs : -1 ≤ δ / ℓ := by have : 0 ≤ δ / ℓ := div_nonneg hδ hℓ.le; linarith
  have hB := one_add_mul_self_le_rpow_one_add hs hb
  have e1 : ℓ + δ = ℓ * (1 + δ / ℓ) := by field_simp
  rw [e1, Real.mul_rpow hℓ.le (by linarith), Real.rpow_sub_one hℓ.ne']
  calc ℓ ^ b + b * δ * (ℓ ^ b / ℓ) = ℓ ^ b * (1 + b * (δ / ℓ)) := by ring
    _ ≤ ℓ ^ b * (1 + δ / ℓ) ^ b := mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hℓ.le b)

/-- **Discrete Gronwall for the Wirsing equation.** If `M(N + 1) = M(N) + L(N) Δ log N` and
`L(N) log N = a M(N) + O(log N)`, then `M ≪ (log N)^b` and `L ≪ (log N)^{b − 1}` for every `b ≥ 1`
with `|a| < b`: the comparison sequence `A (log N)^b` absorbs the forcing because
`(log(N + 1))^b ≥ (log N)^b + b Δ log N (log N)^{b − 1}`. -/
theorem exists_abs_le_rpow_of_wirsing {M L : ℕ → ℝ} {a K b : ℝ} (hK : 0 ≤ K) (hb1 : 1 ≤ b)
    (hab : |a| < b)
    (hstep : ∀ N, 3 ≤ N → M (N + 1) = M N + L N * (Real.log ((N + 1 : ℕ) : ℝ) - Real.log N))
    (heq : ∀ N, 3 ≤ N → |L N * Real.log N - a * M N| ≤ K * Real.log N) :
    ∃ A, 0 ≤ A ∧ ∀ N, 3 ≤ N →
      |M N| ≤ A * Real.log N ^ b ∧ |L N| ≤ A * Real.log N ^ (b - 1) := by
  have hgap : 0 < b - |a| := by linarith
  set A₀ := max (|M 3| / Real.log ((3 : ℕ) : ℝ) ^ b) (K / (b - |a|)) with hA₀
  have hA₀0 : 0 ≤ A₀ := le_max_of_le_right (div_nonneg hK hgap.le)
  have hKA : K ≤ A₀ * (b - |a|) := by
    have := le_max_right (|M 3| / Real.log ((3 : ℕ) : ℝ) ^ b) (K / (b - |a|))
    rwa [div_le_iff₀ hgap] at this
  -- the equation turns a bound on `M` into a bound on `L`
  have hL : ∀ N, 3 ≤ N → |M N| ≤ A₀ * Real.log N ^ b →
      |L N| ≤ |a| * A₀ * Real.log N ^ (b - 1) + K := by
    intro N hN hM
    have hℓ0 : 0 < Real.log N := by linarith [one_le_log_of_three_le hN]
    have hpow : Real.log N ^ b = Real.log N * Real.log N ^ (b - 1) := by
      rw [Real.rpow_sub_one hℓ0.ne']; field_simp
    have h2 : |L N * Real.log N| ≤ |L N * Real.log N - a * M N| + |a * M N| := by
      simpa using abs_add_le (L N * Real.log N - a * M N) (a * M N)
    rw [abs_mul, abs_of_pos hℓ0, abs_mul] at h2
    have h3 : |L N| * Real.log N ≤ (|a| * A₀ * Real.log N ^ (b - 1) + K) * Real.log N := by
      calc |L N| * Real.log N ≤ |a| * |M N| + K * Real.log N := by linarith [heq N hN]
        _ ≤ |a| * (A₀ * (Real.log N * Real.log N ^ (b - 1))) + K * Real.log N := by
            rw [← hpow]; exact add_le_add (mul_le_mul_of_nonneg_left hM (abs_nonneg a)) le_rfl
        _ = (|a| * A₀ * Real.log N ^ (b - 1) + K) * Real.log N := by ring
    exact le_of_mul_le_mul_right h3 hℓ0
  have hM : ∀ N, 3 ≤ N → |M N| ≤ A₀ * Real.log N ^ b := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      have h3 : 0 < Real.log ((3 : ℕ) : ℝ) ^ b :=
        Real.rpow_pos_of_pos (by linarith [one_le_log_of_three_le (le_refl 3)]) b
      have := le_max_left (|M 3| / Real.log ((3 : ℕ) : ℝ) ^ b) (K / (b - |a|))
      rwa [div_le_iff₀ h3] at this
    | succ N hN ih =>
      have hℓ := one_le_log_of_three_le hN
      have hℓ0 : 0 < Real.log N := by linarith
      have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
      have hN0 : (0 : ℝ) < N := by linarith
      set δ := Real.log ((N + 1 : ℕ) : ℝ) - Real.log N with hδdef
      have hδ : 0 ≤ δ := sub_nonneg.mpr (Real.log_le_log hN0 (by push_cast; linarith))
      have hpow1 : 1 ≤ Real.log N ^ (b - 1) := Real.one_le_rpow hℓ (by linarith)
      have key := rpow_add_mul_le hℓ0 hδ hb1
      rw [show Real.log N + δ = Real.log ((N + 1 : ℕ) : ℝ) by rw [hδdef]; ring] at key
      have hK' : K ≤ A₀ * (b - |a|) * Real.log N ^ (b - 1) :=
        hKA.trans (le_mul_of_one_le_right (mul_nonneg hA₀0 hgap.le) hpow1)
      rw [hstep N hN]
      calc |M N + L N * δ| ≤ |M N| + |L N| * δ := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_nonneg hδ]
        _ ≤ A₀ * Real.log N ^ b + (|a| * A₀ * Real.log N ^ (b - 1) + K) * δ :=
            add_le_add ih (mul_le_mul_of_nonneg_right (hL N hN ih) hδ)
        _ ≤ A₀ * Real.log N ^ b +
              (|a| * A₀ * Real.log N ^ (b - 1) + A₀ * (b - |a|) * Real.log N ^ (b - 1)) * δ :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right (add_le_add le_rfl hK') hδ)
        _ = A₀ * (Real.log N ^ b + b * δ * Real.log N ^ (b - 1)) := by ring
        _ ≤ A₀ * Real.log ((N + 1 : ℕ) : ℝ) ^ b := mul_le_mul_of_nonneg_left key hA₀0
  have hAa : 0 ≤ |a| * A₀ := mul_nonneg (abs_nonneg a) hA₀0
  refine ⟨A₀ + |a| * A₀ + K, add_nonneg (add_nonneg hA₀0 hAa) hK, fun N hN => ⟨?_, ?_⟩⟩
  · exact (hM N hN).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (by linarith [one_le_log_of_three_le hN]) b))
  · have hpow1 : 1 ≤ Real.log N ^ (b - 1) :=
      Real.one_le_rpow (one_le_log_of_three_le hN) (by linarith)
    have := hL N hN (hM N hN)
    nlinarith

/-- **The Wirsing bound.** For a completely multiplicative `ω` with `|ω| ≤ 1` whose prime mean is
`β log n + O(1)`: `|M(N)| ≪ (log N)^b` and `|L(N)| ≪ (log N)^{b − 1}` for every `b ≥ 1`, `b > |1 + β|`. -/
theorem exists_abs_gaugeHarmonicSum_le_rpow {ω : ℕ → ℝ}
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (hbd : ∀ n, |ω n| ≤ 1) {β C : ℝ}
    (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C) {b : ℝ} (hb1 : 1 ≤ b)
    (hb : |1 + β| < b) :
    ∃ A, 0 ≤ A ∧ ∀ N, 3 ≤ N → |polarMoment ω N| ≤ A * Real.log N ^ b ∧
      |gaugeHarmonicSum ω N| ≤ A * Real.log N ^ (b - 1) := by
  obtain ⟨K, hK⟩ := exists_abs_wirsing_equation_le hmul hbd hA
  have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hK 1 le_rfl)
  refine exists_abs_le_rpow_of_wirsing (K := 2 * K) (by linarith) hb1 hb (fun N hN => ?_)
    (fun N hN => ?_)
  · have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    rw [polarMoment_succ ω (by omega : 1 ≤ N), Real.log_div (by positivity) hN0.ne']
    push_cast; ring
  · have hℓ := one_le_log_of_three_le hN
    refine (hK N (by omega)).trans ?_
    nlinarith

/-- A Wirsing bound with exponent `b − 1 < 1/2` makes `L(N)² = o(log N)`. -/
theorem tendsto_sq_div_log_of_rpow {L : ℕ → ℝ} {A b : ℝ} (hb : b < 3 / 2)
    (hL : ∀ N, 3 ≤ N → |L N| ≤ A * Real.log N ^ (b - 1)) :
    Tendsto (fun N : ℕ => L N ^ 2 / Real.log N) atTop (nhds 0) := by
  have hlim : Tendsto (fun N : ℕ => A ^ 2 * Real.log N ^ (-(3 - 2 * b))) atTop (nhds 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 3 - 2 * b)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul (A ^ 2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with N hN
    exact div_nonneg (sq_nonneg _) (by linarith [one_le_log_of_three_le hN])
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hℓ0 : 0 < Real.log N := by linarith [one_le_log_of_three_le hN]
    calc L N ^ 2 / Real.log N ≤ (A * Real.log N ^ (b - 1)) ^ 2 / Real.log N := by
          refine div_le_div_of_nonneg_right ?_ hℓ0.le
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hL N hN) 2
      _ = A ^ 2 * Real.log N ^ (-(3 - 2 * b)) := by
          have e : Real.log N ^ (-(3 - 2 * b)) * Real.log N =
              Real.log N ^ (b - 1) * Real.log N ^ (b - 1) := by
            rw [← Real.rpow_add_one hℓ0.ne', ← Real.rpow_add hℓ0]; congr 1; ring
          rw [div_eq_iff hℓ0.ne', mul_assoc, e]; ring

end Gronwall

section Asymptotic

/-- Second-order Bernoulli: `(1 + s)^a ≤ 1 + a s + s²` for `s ≥ 0`, `1 ≤ a ≤ 2`. -/
theorem one_add_rpow_le_second {s a : ℝ} (hs : 0 ≤ s) (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    (1 + s) ^ a ≤ 1 + a * s + s ^ 2 := by
  have h1 : (1 + s) ^ (a - 1) ≤ 1 + (a - 1) * s :=
    rpow_one_add_le_one_add_mul_self (by linarith) (by linarith) (by linarith)
  have e : (1 + s) ^ a = (1 + s) ^ (a - 1) * (1 + s) := by
    rw [← Real.rpow_add_one (by positivity), sub_add_cancel]
  rw [e]
  calc (1 + s) ^ (a - 1) * (1 + s) ≤ (1 + (a - 1) * s) * (1 + s) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ ≤ 1 + a * s + s ^ 2 := by nlinarith [sq_nonneg s]

/-- Telescoping bound for `ℓ^{1−a}`, `1 < a ≤ 2`: `(a − 1)(ℓ' − ℓ) ℓ'^{−a} ≤ ℓ^{1−a} − ℓ'^{1−a}`. -/
theorem sub_mul_rpow_neg_le {ℓ ℓ' a : ℝ} (hℓ : 0 < ℓ) (hle : ℓ ≤ ℓ') (ha1 : 1 < a) (ha2 : a ≤ 2) :
    (a - 1) * (ℓ' - ℓ) * (ℓ' ^ a)⁻¹ ≤ ℓ ^ (1 - a) - ℓ' ^ (1 - a) := by
  have hℓ' : 0 < ℓ' := hℓ.trans_le hle
  set X := ℓ ^ (a - 1)
  set Y := ℓ' ^ (a - 1)
  have hX : 0 < X := Real.rpow_pos_of_pos hℓ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hℓ' _
  have hXY : X ≤ Y := Real.rpow_le_rpow hℓ.le hle (by linarith)
  set D := (a - 1) * ((ℓ' - ℓ) / ℓ')
  have hD : 0 ≤ D := mul_nonneg (by linarith) (div_nonneg (by linarith) hℓ'.le)
  -- concave Bernoulli at `ℓ/ℓ' = 1 − (ℓ' − ℓ)/ℓ'`
  have hB : X ≤ Y * (1 - D) := by
    have h := rpow_one_add_le_one_add_mul_self (s := -((ℓ' - ℓ) / ℓ')) (p := a - 1)
      (by rw [neg_le_neg_iff, div_le_one hℓ']; linarith) (by linarith) (by linarith)
    rw [show 1 + -((ℓ' - ℓ) / ℓ') = ℓ / ℓ' by field_simp; ring,
      Real.div_rpow hℓ.le hℓ'.le, div_le_iff₀ hY] at h
    calc X ≤ (1 + (a - 1) * -((ℓ' - ℓ) / ℓ')) * Y := h
      _ = Y * (1 - D) := by ring
  have e1 : ℓ ^ (1 - a) = X⁻¹ := by
    rw [show 1 - a = -(a - 1) by ring, Real.rpow_neg hℓ.le]
  have e2 : ℓ' ^ (1 - a) = Y⁻¹ := by
    rw [show 1 - a = -(a - 1) by ring, Real.rpow_neg hℓ'.le]
  have hYℓ : Y * ℓ' = ℓ' ^ a := by rw [← Real.rpow_add_one hℓ'.ne', sub_add_cancel]
  have e3 : (ℓ' ^ a)⁻¹ = Y⁻¹ / ℓ' := by rw [← hYℓ, mul_inv, div_eq_mul_inv]
  rw [e1, e2, e3]
  have hlhs : (a - 1) * (ℓ' - ℓ) * (Y⁻¹ / ℓ') = D / Y := by
    simp only [D]; field_simp
  rw [hlhs, show X⁻¹ - Y⁻¹ = (Y - X) / (X * Y) by field_simp, div_le_div_iff₀ hY (by positivity)]
  have hDX : D * X ≤ Y - X := by nlinarith [mul_le_mul_of_nonneg_left hXY hD]
  nlinarith [mul_le_mul_of_nonneg_right hDX hY.le]

/-- The recursion of `U = M/ℓ^a` over one step `ℓ → ℓ' = ℓ(1 + σ)`:
`U' = U (1 + aσ)/q + Eσ/(ℓ^a q)` with `q = (1 + σ)^a`, `E = Lℓ − aM`. -/
theorem wirsing_step_rec {ℓ ℓ' a M L : ℝ} (hℓ : 0 < ℓ) (hle : ℓ ≤ ℓ') :
    (M + L * (ℓ' - ℓ)) / ℓ' ^ a =
      M / ℓ ^ a * ((1 + a * ((ℓ' - ℓ) / ℓ)) / (1 + (ℓ' - ℓ) / ℓ) ^ a) +
        (L * ℓ - a * M) * ((ℓ' - ℓ) / ℓ) / (ℓ ^ a * (1 + (ℓ' - ℓ) / ℓ) ^ a) := by
  have hσ0 : 0 ≤ (ℓ' - ℓ) / ℓ := div_nonneg (by linarith) hℓ.le
  have hq : 0 < (1 + (ℓ' - ℓ) / ℓ) ^ a := Real.rpow_pos_of_pos (by linarith) a
  have hℓa : 0 < ℓ ^ a := Real.rpow_pos_of_pos hℓ a
  have hℓ' : ℓ' = ℓ * (1 + (ℓ' - ℓ) / ℓ) := by field_simp; ring
  have hℓ'a : ℓ' ^ a = ℓ ^ a * (1 + (ℓ' - ℓ) / ℓ) ^ a := by
    conv_lhs => rw [hℓ']
    exact Real.mul_rpow hℓ.le (by linarith)
  rw [hℓ'a]
  field_simp
  ring

/-- The forcing of one step telescopes against `ℓ^{1−a'}`, `a = a' + α`:
`|Eσ/(ℓ^a q)| ≤ K (a' − 1)⁻¹ (ℓ^{1−a'} − ℓ'^{1−a'})` when `|E| ≤ K ℓ^{1+α}`. -/
theorem wirsing_step_force {ℓ ℓ' a a' K α E : ℝ} (hℓ : 0 < ℓ) (hle : ℓ ≤ ℓ')
    (ha'1 : 1 < a') (ha'2 : a' ≤ 2) (haa' : a = a' + α) (hα : 0 ≤ α) (hK : 0 ≤ K)
    (hE : |E| ≤ K * ℓ ^ (1 + α)) :
    |E * ((ℓ' - ℓ) / ℓ) / (ℓ ^ a * (1 + (ℓ' - ℓ) / ℓ) ^ a)| ≤
      K * (a' - 1)⁻¹ * (ℓ ^ (1 - a') - ℓ' ^ (1 - a')) := by
  have hℓ'0 : 0 < ℓ' := hℓ.trans_le hle
  set δ := ℓ' - ℓ
  have hδ0 : 0 ≤ δ := by simp only [δ]; linarith
  have hσ0 : 0 ≤ δ / ℓ := div_nonneg hδ0 hℓ.le
  have hσℓ : δ / ℓ * ℓ = δ := div_mul_cancel₀ δ hℓ.ne'
  have htel := sub_mul_rpow_neg_le hℓ hle ha'1 ha'2
  have hℓ'a : ℓ' ^ a = ℓ ^ a * (1 + δ / ℓ) ^ a := by
    have hℓ' : ℓ' = ℓ * (1 + δ / ℓ) := by simp only [δ]; field_simp; ring
    conv_lhs => rw [hℓ']
    exact Real.mul_rpow hℓ.le (by linarith)
  have hℓ'a0 : 0 < ℓ' ^ a := Real.rpow_pos_of_pos hℓ'0 a
  have hℓ'a'0 : 0 < ℓ' ^ a' := Real.rpow_pos_of_pos hℓ'0 a'
  have hℓα : ℓ ^ α ≤ ℓ' ^ α := Real.rpow_le_rpow hℓ.le hle hα
  have hsplit : ℓ' ^ a = ℓ' ^ α * ℓ' ^ a' := by
    rw [← Real.rpow_add hℓ'0, haa', add_comm]
  have hpow1 : ℓ ^ (1 + α) = ℓ * ℓ ^ α := by rw [Real.rpow_add hℓ, Real.rpow_one]
  have h1 : |E * (δ / ℓ) / (ℓ ^ a * (1 + δ / ℓ) ^ a)| ≤ K * δ * (ℓ' ^ a')⁻¹ := by
    rw [abs_div, abs_mul, abs_of_nonneg hσ0, ← hℓ'a, abs_of_pos hℓ'a0, div_le_iff₀ hℓ'a0]
    calc |E| * (δ / ℓ) ≤ K * ℓ ^ (1 + α) * (δ / ℓ) := mul_le_mul_of_nonneg_right hE hσ0
      _ = K * δ * ℓ ^ α := by rw [hpow1, ← hσℓ]; field_simp
      _ ≤ K * δ * ℓ' ^ α := mul_le_mul_of_nonneg_left hℓα (mul_nonneg hK hδ0)
      _ = K * δ * (ℓ' ^ a')⁻¹ * ℓ' ^ a := by rw [hsplit]; field_simp
  refine h1.trans ?_
  have ha0 : 0 < a' - 1 := by linarith
  calc K * δ * (ℓ' ^ a')⁻¹ = K * (a' - 1)⁻¹ * ((a' - 1) * δ * (ℓ' ^ a')⁻¹) := by
        field_simp
    _ ≤ K * (a' - 1)⁻¹ * (ℓ ^ (1 - a') - ℓ' ^ (1 - a')) :=
        mul_le_mul_of_nonneg_left htel (mul_nonneg hK (inv_nonneg.mpr ha0.le))

/-- The drift factor of one step: `0 ≤ ρ ≤ 1` and `1 − ρ ≤ 4 (a − 1)⁻¹ (ℓ^{1−a} − ℓ'^{1−a})` for
`ρ = (1 + aσ)/(1 + σ)^a`, `σ = (ℓ' − ℓ)/ℓ`, `1 ≤ ℓ ≤ ℓ' ≤ ℓ + 1`, `1 < a ≤ 2`. -/
theorem wirsing_step_drift {ℓ ℓ' a : ℝ} (hℓ1 : 1 ≤ ℓ) (hle : ℓ ≤ ℓ') (hδ1 : ℓ' - ℓ ≤ 1)
    (ha1 : 1 < a) (ha2 : a ≤ 2) :
    0 ≤ (1 + a * ((ℓ' - ℓ) / ℓ)) / (1 + (ℓ' - ℓ) / ℓ) ^ a ∧
      (1 + a * ((ℓ' - ℓ) / ℓ)) / (1 + (ℓ' - ℓ) / ℓ) ^ a ≤ 1 ∧
      1 - (1 + a * ((ℓ' - ℓ) / ℓ)) / (1 + (ℓ' - ℓ) / ℓ) ^ a ≤
        4 * (a - 1)⁻¹ * (ℓ ^ (1 - a) - ℓ' ^ (1 - a)) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ'0 : 0 < ℓ' := hℓ0.trans_le hle
  set δ := ℓ' - ℓ
  set σ := δ / ℓ
  have hδ0 : 0 ≤ δ := by simp only [δ]; linarith
  have hσ0 : 0 ≤ σ := div_nonneg hδ0 hℓ0.le
  have hσℓ : σ * ℓ = δ := div_mul_cancel₀ δ hℓ0.ne'
  have htel := sub_mul_rpow_neg_le hℓ0 hle ha1 ha2
  set q := (1 + σ) ^ a
  have hq1 : 1 + a * σ ≤ q := one_add_mul_self_le_rpow_one_add (by linarith) ha1.le
  have hq2 : q ≤ 1 + a * σ + σ ^ 2 := one_add_rpow_le_second hσ0 ha1.le ha2
  have haσ0 : 0 ≤ a * σ := mul_nonneg (by linarith) hσ0
  have hqpos : 0 < q := by linarith
  have hℓ'a0 : 0 < ℓ' ^ a := Real.rpow_pos_of_pos hℓ'0 a
  have hρ2 : 1 - (1 + a * σ) / q ≤ σ ^ 2 := by
    rw [sub_le_comm, le_div_iff₀ hqpos]
    calc (1 - σ ^ 2) * q ≤ (1 - σ ^ 2) * (1 + a * σ + σ ^ 2) := by
          have hσ1 : σ ≤ 1 := (div_le_self hδ0 hℓ1).trans hδ1
          exact mul_le_mul_of_nonneg_left hq2 (by nlinarith)
      _ ≤ 1 + a * σ := by
          have h4 : 0 ≤ a * σ * σ ^ 2 := mul_nonneg haσ0 (sq_nonneg σ)
          have h5 : 0 ≤ σ ^ 4 := pow_nonneg hσ0 4
          nlinarith [h4, h5]
  have hσ4 : σ ^ 2 ≤ 4 * (a - 1)⁻¹ * (ℓ ^ (1 - a) - ℓ' ^ (1 - a)) := by
    have hℓ'2 : ℓ' ^ a ≤ 4 * ℓ ^ 2 := by
      have hℓ'1 : 1 ≤ ℓ' := by linarith
      calc ℓ' ^ a ≤ ℓ' ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hℓ'1 ha2
        _ = ℓ' ^ 2 := Real.rpow_two ℓ'
        _ ≤ (2 * ℓ) ^ 2 := pow_le_pow_left₀ hℓ'0.le (by simp only [δ] at hδ1; linarith) 2
        _ = 4 * ℓ ^ 2 := by ring
    have h1 : σ ^ 2 ≤ 4 * δ * (ℓ' ^ a)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hℓ'a0]
      calc σ ^ 2 * ℓ' ^ a ≤ σ ^ 2 * (4 * ℓ ^ 2) := mul_le_mul_of_nonneg_left hℓ'2 (sq_nonneg σ)
        _ = 4 * δ * δ := by rw [← hσℓ]; ring
        _ ≤ 4 * δ := by nlinarith
    refine h1.trans ?_
    have ha0 : 0 < a - 1 := by linarith
    calc 4 * δ * (ℓ' ^ a)⁻¹ = 4 * (a - 1)⁻¹ * ((a - 1) * δ * (ℓ' ^ a)⁻¹) := by field_simp
      _ ≤ 4 * (a - 1)⁻¹ * (ℓ ^ (1 - a) - ℓ' ^ (1 - a)) :=
          mul_le_mul_of_nonneg_left htel (by positivity)
  exact ⟨div_nonneg (by linarith) hqpos.le, (div_le_one hqpos).mpr hq1, hρ2.trans hσ4⟩

/-- **Envelopes.** If `|U| ≤ B` and `|U(N + 1) − U(N)| ≤ G₁ ΔT + G₂ ΔT_α` with nonnegative
nonincreasing `T ≤ T_α` from `N = 3` on, then `U → c` with `|U(N) − c| ≤ (G₁ + G₂) T_α(N)`: the
sequences `U ± (G₁ T + G₂ T_α)` are monotone and pinch `c`. -/
theorem exists_abs_sub_le_of_drift {U T Tα : ℕ → ℝ} {G₁ G₂ B : ℝ} (hG₁ : 0 ≤ G₁) (hG₂ : 0 ≤ G₂)
    (hT0 : ∀ N, 3 ≤ N → 0 ≤ T N) (hTα0 : ∀ N, 3 ≤ N → 0 ≤ Tα N)
    (hTTα : ∀ N, 3 ≤ N → T N ≤ Tα N) (hUB : ∀ N, 3 ≤ N → |U N| ≤ B)
    (hdrift : ∀ N, 3 ≤ N →
      |U (N + 1) - U N| ≤ G₁ * (T N - T (N + 1)) + G₂ * (Tα N - Tα (N + 1))) :
    ∃ c : ℝ, ∀ N, 3 ≤ N → |U N - c| ≤ (G₁ + G₂) * Tα N := by
  set V : ℕ → ℝ := fun N => G₁ * T N + G₂ * Tα N
  have hV0 : ∀ N, 3 ≤ N → 0 ≤ V N := fun N hN =>
    add_nonneg (mul_nonneg hG₁ (hT0 N hN)) (mul_nonneg hG₂ (hTα0 N hN))
  have hVd : ∀ N, 3 ≤ N → ∀ m, N ≤ m → U m + V m ≤ U N + V N := by
    intro N hN m hm
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih =>
      have := (abs_le.mp (hdrift m (hN.trans hm))).2
      simp only [V] at ih ⊢
      linarith
  have hWi : ∀ N, 3 ≤ N → ∀ m, N ≤ m → U N - V N ≤ U m - V m := by
    intro N hN m hm
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih =>
      have := (abs_le.mp (hdrift m (hN.trans hm))).1
      simp only [V] at ih ⊢
      linarith
  have hbdd : BddBelow (Set.range fun n : ℕ => U (n + 3) + V (n + 3)) := by
    refine ⟨-B, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 := (abs_le.mp (hUB (n + 3) (by omega))).1
    have h2 := hV0 (n + 3) (by omega)
    linarith
  set c := ⨅ n : ℕ, (U (n + 3) + V (n + 3))
  have hcV : ∀ N, 3 ≤ N → c ≤ U N + V N := fun N hN => by
    have := ciInf_le hbdd (N - 3)
    simpa only [Nat.sub_add_cancel hN] using this
  have hWc : ∀ N, 3 ≤ N → U N - V N ≤ c := fun N hN => by
    refine le_ciInf fun n => ?_
    rcases le_total N (n + 3) with h | h
    · have := hWi N hN (n + 3) h
      have := hV0 (n + 3) (by omega)
      linarith
    · have := hVd (n + 3) (by omega) N h
      have := hV0 N hN
      linarith
  refine ⟨c, fun N hN => ?_⟩
  have hVG : V N ≤ (G₁ + G₂) * Tα N := by
    have := mul_le_mul_of_nonneg_left (hTTα N hN) hG₁
    simp only [V]; linarith
  rw [abs_le]; constructor <;> linarith [hcV N hN, hWc N hN]

/-- **The Wirsing asymptotic with a power error.** If `M(N + 1) = M(N) + L(N) Δ log N` and
`|L(N) log N − a M(N)| ≤ K (log N)^{1+α}` with `0 ≤ α`, `1 + α < a ≤ 2`, then `M(N)/(log N)^a → c` at
rate `(log N)^{1+α−a}` and `L(N) = a c (log N)^{a − 1} + O((log N)^α)`. The drift of `M/(log N)^a` is a
second-order Bernoulli remainder telescoping against `(log N)^{1−a}`, the forcing telescopes against
`(log N)^{1+α−a}` (`wirsing_step_drift`, `wirsing_step_force`, `exists_abs_sub_le_of_drift`). -/
theorem exists_abs_sub_rpow_le_of_wirsing_rpow {M L : ℕ → ℝ} {a K α : ℝ} (hK : 0 ≤ K)
    (hα : 0 ≤ α) (haα : 1 + α < a) (ha2 : a ≤ 2)
    (hstep : ∀ N, 3 ≤ N → M (N + 1) = M N + L N * (Real.log ((N + 1 : ℕ) : ℝ) - Real.log N))
    (heq : ∀ N, 3 ≤ N → |L N * Real.log N - a * M N| ≤ K * Real.log N ^ (1 + α)) :
    ∃ c G : ℝ, ∀ N, 3 ≤ N →
      |M N / Real.log N ^ a - c| ≤ G * Real.log N ^ (1 + α - a) ∧
        |L N - a * c * Real.log N ^ (a - 1)| ≤ (a * G + K) * Real.log N ^ α := by
  have ha1 : 1 < a := by linarith
  set a' := a - α with ha'
  have ha'1 : 1 < a' := by simp only [a']; linarith
  have ha'2 : a' ≤ 2 := by simp only [a']; linarith
  have haa' : a = a' + α := by simp only [a']; ring
  have h1a' : 1 - a' = 1 + α - a := by simp only [a']; ring
  set U : ℕ → ℝ := fun N => M N / Real.log N ^ a with hU
  set T : ℕ → ℝ := fun N => Real.log N ^ (1 - a) with hT
  set Tα : ℕ → ℝ := fun N => Real.log N ^ (1 - a') with hTα
  have hlogs : ∀ N : ℕ, 3 ≤ N → 1 ≤ Real.log N ∧ Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) ∧
      Real.log ((N + 1 : ℕ) : ℝ) - Real.log N ≤ 1 := by
    intro N hN
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    refine ⟨one_le_log_of_three_le hN, Real.log_le_log hN0 (by push_cast; linarith), ?_⟩
    rw [← Real.log_div (by positivity) hN0.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hN0.ne', div_le_one hN0]; push_cast; linarith
  -- one step of the recursion
  have hstepU : ∀ N, 3 ≤ N →
      (|U (N + 1)| ≤ |U N| + K * (a' - 1)⁻¹ * (Tα N - Tα (N + 1))) ∧
      |U (N + 1) - U N| ≤ 4 * |U N| * (a - 1)⁻¹ * (T N - T (N + 1)) +
        K * (a' - 1)⁻¹ * (Tα N - Tα (N + 1)) := by
    intro N hN
    obtain ⟨hℓ1, hle, hδ1⟩ := hlogs N hN
    have hrec := wirsing_step_rec (M := M N) (L := L N) (a := a) (by linarith) hle
    have hforce := wirsing_step_force (E := L N * Real.log N - a * M N) (by linarith) hle
      ha'1 ha'2 haa' hα hK (heq N hN)
    obtain ⟨hρ0, hρ1, hρ2⟩ := wirsing_step_drift hℓ1 hle hδ1 ha1 ha2
    have hUN1 : U (N + 1) = M (N + 1) / Real.log ((N + 1 : ℕ) : ℝ) ^ a := rfl
    rw [hUN1, hstep N hN, hrec]
    set ρ := (1 + a * ((Real.log ((N + 1 : ℕ) : ℝ) - Real.log N) / Real.log N)) /
      (1 + (Real.log ((N + 1 : ℕ) : ℝ) - Real.log N) / Real.log N) ^ a
    set F := (L N * Real.log N - a * M N) *
      ((Real.log ((N + 1 : ℕ) : ℝ) - Real.log N) / Real.log N) /
        (Real.log N ^ a * (1 + (Real.log ((N + 1 : ℕ) : ℝ) - Real.log N) / Real.log N) ^ a)
    have hUN : M N / Real.log N ^ a = U N := rfl
    rw [hUN]
    constructor
    · refine (abs_add_le _ _).trans (add_le_add ?_ hforce)
      rw [abs_mul, abs_of_nonneg hρ0]
      exact mul_le_of_le_one_right (abs_nonneg _) hρ1
    · rw [show U N * ρ + F - U N = -(U N * (1 - ρ)) + F by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_mul, abs_of_nonneg (sub_nonneg.mpr hρ1)]
      have := mul_le_mul_of_nonneg_left hρ2 (abs_nonneg (U N))
      calc |U N| * (1 - ρ) + |F| ≤ |U N| * (4 * (a - 1)⁻¹ * (T N - T (N + 1))) +
            K * (a' - 1)⁻¹ * (Tα N - Tα (N + 1)) := add_le_add this hforce
        _ = _ := by ring
  have ha0 : 0 < (a - 1)⁻¹ := inv_pos.mpr (by linarith)
  have ha0α : 0 < (a' - 1)⁻¹ := inv_pos.mpr (by linarith)
  have hTα0 : ∀ N, 3 ≤ N → 0 ≤ Tα N := fun N hN =>
    Real.rpow_nonneg (by linarith [one_le_log_of_three_le hN]) _
  have hdT : ∀ N, 3 ≤ N → 0 ≤ T N - T (N + 1) := fun N hN => by
    obtain ⟨hℓ1, hle, -⟩ := hlogs N hN
    have := sub_mul_rpow_neg_le (by linarith) hle ha1 ha2
    have h0 : 0 ≤ (a - 1) * (Real.log ((N + 1 : ℕ) : ℝ) - Real.log N) *
        (Real.log ((N + 1 : ℕ) : ℝ) ^ a)⁻¹ :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith))
        (inv_nonneg.mpr (Real.rpow_nonneg (by linarith) _))
    exact h0.trans this
  -- `U` is bounded
  set B := |U 3| + K * (a' - 1)⁻¹ * Tα 3
  have hB : ∀ N, 3 ≤ N → |U N| + K * (a' - 1)⁻¹ * Tα N ≤ B := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact le_rfl
    | succ N hN ih => linarith [(hstepU N hN).1]
  have hUB : ∀ N, 3 ≤ N → |U N| ≤ B := fun N hN => by
    have := hB N hN
    have := mul_nonneg (mul_nonneg hK ha0α.le) (hTα0 N hN)
    linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hUB 3 le_rfl)
  obtain ⟨c, hc⟩ := exists_abs_sub_le_of_drift (U := U) (T := T) (Tα := Tα)
    (G₁ := 4 * B * (a - 1)⁻¹) (G₂ := K * (a' - 1)⁻¹) (B := B) (by positivity)
    (mul_nonneg hK ha0α.le)
    (fun N hN => Real.rpow_nonneg (by linarith [one_le_log_of_three_le hN]) _) hTα0
    (fun N hN => Real.rpow_le_rpow_of_exponent_le (one_le_log_of_three_le hN)
      (by simp only [a']; linarith)) hUB
    (fun N hN => by
      have h2 := (hstepU N hN).2
      have h4 : 4 * |U N| * (a - 1)⁻¹ * (T N - T (N + 1)) ≤
          4 * B * (a - 1)⁻¹ * (T N - T (N + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (by linarith [hUB N hN]) ha0.le) (hdT N hN)
      linarith)
  set G := 4 * B * (a - 1)⁻¹ + K * (a' - 1)⁻¹
  refine ⟨c, G, fun N hN => ?_⟩
  have hUc := hc N hN
  refine ⟨by rw [← h1a']; exact hUc, ?_⟩
  -- `L = (a M + E)/ℓ` with `M = U ℓ^a`
  have hℓ0 : 0 < Real.log N := by linarith [one_le_log_of_three_le hN]
  have hℓa : 0 < Real.log N ^ a := Real.rpow_pos_of_pos hℓ0 a
  have hMU : M N = U N * Real.log N ^ a := by simp only [hU]; field_simp
  have hTa : Tα N * Real.log N ^ a = Real.log N ^ (1 + α) := by
    simp only [hTα]; rw [← Real.rpow_add hℓ0, h1a']; congr 1; ring
  have hpa : Real.log N ^ a = Real.log N * Real.log N ^ (a - 1) := by
    rw [Real.rpow_sub_one hℓ0.ne']; field_simp
  have hp1α : Real.log N ^ (1 + α) = Real.log N * Real.log N ^ α := by
    rw [Real.rpow_add hℓ0, Real.rpow_one]
  have hkey : (L N - a * c * Real.log N ^ (a - 1)) * Real.log N =
      (L N * Real.log N - a * M N) + a * ((U N - c) * Real.log N ^ a) := by
    rw [hMU, hpa]; ring
  have h2 : a * (|U N - c| * Real.log N ^ a) ≤ a * (G * Real.log N ^ (1 + α)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc |U N - c| * Real.log N ^ a ≤ G * Tα N * Real.log N ^ a :=
          mul_le_mul_of_nonneg_right hUc hℓa.le
      _ = G * Real.log N ^ (1 + α) := by rw [mul_assoc, hTa]
  have hbound : |L N - a * c * Real.log N ^ (a - 1)| * Real.log N ≤
      ((a * G + K) * Real.log N ^ α) * Real.log N := by
    calc |L N - a * c * Real.log N ^ (a - 1)| * Real.log N
        = |(L N * Real.log N - a * M N) + a * ((U N - c) * Real.log N ^ a)| := by
          rw [← hkey, abs_mul, abs_of_pos hℓ0]
      _ ≤ |L N * Real.log N - a * M N| + a * (|U N - c| * Real.log N ^ a) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))
          rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < a), abs_mul, abs_of_pos hℓa]
      _ ≤ K * Real.log N ^ (1 + α) + a * (G * Real.log N ^ (1 + α)) := add_le_add (heq N hN) h2
      _ = ((a * G + K) * Real.log N ^ α) * Real.log N := by rw [hp1α]; ring
  exact le_of_mul_le_mul_right hbound hℓ0

/-- **The Wirsing asymptotic.** If `M(N + 1) = M(N) + L(N) Δ log N` and
`|L(N) log N − a M(N)| ≤ K log N` with `1 < a ≤ 2`, then `M(N)/(log N)^a → c` at rate
`(log N)^{1 − a}` and `L(N) = a c (log N)^{a − 1} + O(1)`. -/
theorem exists_abs_sub_rpow_le_of_wirsing {M L : ℕ → ℝ} {a K : ℝ} (hK : 0 ≤ K) (ha1 : 1 < a)
    (ha2 : a ≤ 2)
    (hstep : ∀ N, 3 ≤ N → M (N + 1) = M N + L N * (Real.log ((N + 1 : ℕ) : ℝ) - Real.log N))
    (heq : ∀ N, 3 ≤ N → |L N * Real.log N - a * M N| ≤ K * Real.log N) :
    ∃ c G : ℝ, ∀ N, 3 ≤ N →
      |M N / Real.log N ^ a - c| ≤ G * Real.log N ^ (1 - a) ∧
        |L N - a * c * Real.log N ^ (a - 1)| ≤ a * G + K := by
  obtain ⟨c, G, h⟩ := exists_abs_sub_rpow_le_of_wirsing_rpow (α := 0) hK le_rfl (by linarith) ha2
    hstep fun N hN => by rw [add_zero, Real.rpow_one]; exact heq N hN
  exact ⟨c, G, fun N hN => by simpa using h N hN⟩

/-- **The Wirsing asymptotic with a power error.** If the prime mean of a completely multiplicative
`|ω| ≤ 1` is `β log n + O((1 + log n)^α)` with `0 ≤ α < β ≤ 1`, then
`Σ_{n ≤ N} ω(n)/n = c (log N)^β + O((log N)^α)`. -/
theorem exists_abs_gaugeHarmonicSum_sub_rpow_le_rpow {ω : ℕ → ℝ}
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (hbd : ∀ n, |ω n| ≤ 1) {β C α : ℝ}
    (hα : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C * (1 + Real.log n) ^ α) :
    ∃ c G : ℝ, ∀ N, 3 ≤ N → |gaugeHarmonicSum ω N - c * Real.log N ^ β| ≤ G * Real.log N ^ α := by
  obtain ⟨K, hK⟩ := exists_abs_wirsing_equation_le_rpow hmul hbd hα hA
  have hK0 : 0 ≤ K := by
    have h := (abs_nonneg _).trans (hK 1 le_rfl)
    simp only [Nat.cast_one, Real.log_one, add_zero, Real.one_rpow, mul_one] at h
    exact h
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨c, G, hcG⟩ := exists_abs_sub_rpow_le_of_wirsing_rpow (M := polarMoment ω)
    (L := gaugeHarmonicSum ω) (a := 1 + β) (K := 4 * K) (α := α) (by linarith) hα (by linarith)
    (by linarith)
    (fun N hN => by
      have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
      have hN0 : (0 : ℝ) < N := by linarith
      rw [polarMoment_succ ω (by omega : 1 ≤ N), Real.log_div (by positivity) hN0.ne']
      push_cast; ring)
    (fun N hN => by
      have hℓ := one_le_log_of_three_le hN
      refine (hK N (by omega)).trans ?_
      have h1 : (1 + Real.log N) ^ (1 + α) ≤ (2 * Real.log N) ^ (1 + α) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      have h2 : (2 * Real.log N) ^ (1 + α) = 2 ^ (1 + α) * Real.log N ^ (1 + α) :=
        Real.mul_rpow (by norm_num) (by linarith)
      have h3 : (2 : ℝ) ^ (1 + α) ≤ 4 := by
        calc (2 : ℝ) ^ (1 + α) ≤ 2 ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by norm_num
      have h4 : 0 ≤ Real.log N ^ (1 + α) := Real.rpow_nonneg (by linarith) _
      calc K * (1 + Real.log N) ^ (1 + α) ≤ K * (2 ^ (1 + α) * Real.log N ^ (1 + α)) := by
            rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hK0
        _ ≤ K * (4 * Real.log N ^ (1 + α)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h4) hK0
        _ = 4 * K * Real.log N ^ (1 + α) := by ring)
  refine ⟨(1 + β) * c, (1 + β) * G + 4 * K, fun N hN => ?_⟩
  have h := (hcG N hN).2
  rwa [show 1 + β - 1 = β by ring] at h

/-- **The Wirsing asymptotic for completely multiplicative `ω`.** If the prime mean is
`β log n + O(1)` with `0 < β ≤ 1`, then `Σ_{n ≤ N} ω(n)/n = C (log N)^β + O(1)`. -/
theorem exists_abs_gaugeHarmonicSum_sub_rpow_le {ω : ℕ → ℝ}
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (hbd : ∀ n, |ω n| ≤ 1) {β C : ℝ}
    (hA : ∀ n, 1 ≤ n → |primeMean ω n - β * Real.log n| ≤ C) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ c G : ℝ, ∀ N, 3 ≤ N → |gaugeHarmonicSum ω N - c * Real.log N ^ β| ≤ G := by
  obtain ⟨c, G, h⟩ := exists_abs_gaugeHarmonicSum_sub_rpow_le_rpow hmul hbd le_rfl hβ0 hβ1
    (C := C) fun n hn => by rw [Real.rpow_zero, mul_one]; exact hA n hn
  exact ⟨c, G, fun N hN => by simpa using h N hN⟩

end Asymptotic

section FlipTwins

open ArithmeticCountingPositivity (primeSetFlip primeSetCutoff primeSetFlip_eq_finiteFlip_of_le)
open RenormalizedArithmeticPotentialTheory (primeSignGauge_isSignGauge primeSignGauge_prime)

/-- The **logarithmic prime mass** `Σ_{p ∈ P, p ≤ n} log p / p` of a set of primes. -/
def primeSetLogMass (P : Set ℕ) (n : ℕ) : ℝ := ∑ p ∈ primeSetCutoff P n, Real.log p / p

theorem primeSetFlip_isSignGauge (P : Set ℕ) :
    RenormalizedArithmeticPotentialTheory.IsSignGauge (primeSetFlip P) := by
  classical
  apply primeSignGauge_isSignGauge
  intro p
  split_ifs <;> norm_num

theorem primeSetFlip_mul_self (P : Set ℕ) (n : ℕ) : primeSetFlip P n * primeSetFlip P n = 1 := by
  rw [primeSetFlip_eq_finiteFlip_of_le P le_rfl]
  exact finiteFlip_mul_self _ n

theorem abs_primeSetFlip_le (P : Set ℕ) (n : ℕ) : |primeSetFlip P n| ≤ 1 := by
  have h := primeSetFlip_mul_self P n
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (primeSetFlip P n - 1), sq_nonneg (primeSetFlip P n + 1)]

theorem primeSetFlip_prime_of_mem (P : Set ℕ) {p : ℕ} (hp : p.Prime) (h : p ∈ P) :
    primeSetFlip P p = -1 := by
  unfold primeSetFlip
  rw [primeSignGauge_prime hp]
  simp [h]

theorem primeSetFlip_prime_of_notMem (P : Set ℕ) {p : ℕ} (hp : p.Prime) (h : p ∉ P) :
    primeSetFlip P p = 1 := by
  unfold primeSetFlip
  rw [primeSignGauge_prime hp]
  simp [h]

open Classical in
theorem primeSetCutoff_eq_filter (P : Set ℕ) (n : ℕ) :
    primeSetCutoff P n = ((Icc 1 n).filter Nat.Prime).filter (· ∈ P) := by
  ext k
  simp only [primeSetCutoff, mem_filter, Nat.mem_primesLE, mem_Icc]
  constructor
  · rintro ⟨⟨hkn, hk⟩, hP⟩; exact ⟨⟨⟨hk.one_lt.le, hkn⟩, hk⟩, hP⟩
  · rintro ⟨⟨⟨_, hkn⟩, hk⟩, hP⟩; exact ⟨⟨hkn, hk⟩, hP⟩

/-- The prime mean of a flip twin is the full Mertens sum minus twice the flipped mass. -/
theorem primeMean_primeSetFlip (P : Set ℕ) (n : ℕ) :
    primeMean (primeSetFlip P) n =
      ∑ k ∈ Icc 1 n with k.Prime, Real.log k / k - 2 * primeSetLogMass P n := by
  classical
  unfold primeMean primeSetLogMass
  rw [primeSetCutoff_eq_filter, sum_filter (s := (Icc 1 n).filter Nat.Prime), mul_sum,
    ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hp := (mem_filter.mp hk).2
  by_cases h : k ∈ P
  · rw [if_pos h, primeSetFlip_prime_of_mem P hp h]; ring
  · rw [if_neg h, primeSetFlip_prime_of_notMem P hp h]; ring

/-- A relative logarithmic density of the flipped primes gives the prime mean `(1 − 2κ) log n`. -/
theorem abs_primeMean_primeSetFlip_sub_le (P : Set ℕ) {κ C : ℝ}
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) {n : ℕ} (hn : 1 ≤ n) :
    |primeMean (primeSetFlip P) n - (1 - 2 * κ) * Real.log n| ≤
      (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) + 2 * C := by
  rw [primeMean_primeSetFlip]
  have h1 := RHTower.Mertens.mertens_first_prime n hn
  have h2 := hP n hn
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- A relative logarithmic density with a power error gives the prime mean `(1 − 2κ) log n` with the
same error. -/
theorem abs_primeMean_primeSetFlip_sub_le_rpow (P : Set ℕ) {κ C α : ℝ} (hα : 0 ≤ α)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C * (1 + Real.log n) ^ α)
    {n : ℕ} (hn : 1 ≤ n) :
    |primeMean (primeSetFlip P) n - (1 - 2 * κ) * Real.log n| ≤
      (|(Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)| + 2 * C) * (1 + Real.log n) ^ α := by
  rw [primeMean_primeSetFlip]
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (hP 1 le_rfl)
  have hP1 : 1 ≤ (1 + Real.log n) ^ α := Real.one_le_rpow (by linarith [Real.log_natCast_nonneg n]) hα
  have h1 := RHTower.Mertens.mertens_first_prime n hn
  have h2 := hP n hn
  set C₀ := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  have hC₀ : C₀ ≤ |C₀| * (1 + Real.log n) ^ α :=
    (le_abs_self C₀).trans (le_mul_of_one_le_right (abs_nonneg _) hP1)
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **The Wirsing asymptotic for flip twins with a power error.** If
`Σ_{p ∈ P, p ≤ n} log p/p = κ log n + O((1 + log n)^α)` with `0 ≤ κ`, `0 ≤ α < 1 − 2κ`, then
`Σ_{n ≤ N} ω_P(n)/n = c (log N)^{1 − 2κ} + O((log N)^α)`. -/
theorem exists_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le_rpow (P : Set ℕ) {κ C α : ℝ}
    (hκ0 : 0 ≤ κ) (hα : 0 ≤ α) (hακ : α < 1 - 2 * κ)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C * (1 + Real.log n) ^ α) :
    ∃ c G : ℝ, ∀ N, 3 ≤ N →
      |gaugeHarmonicSum (primeSetFlip P) N - c * Real.log N ^ (1 - 2 * κ)| ≤ G * Real.log N ^ α :=
  exists_abs_gaugeHarmonicSum_sub_rpow_le_rpow
    (fun a b ha hb => (primeSetFlip_isSignGauge P).mul ha hb) (abs_primeSetFlip_le P) hα hακ
    (by linarith) (fun n hn => abs_primeMean_primeSetFlip_sub_le_rpow P hα hP hn)

/-- A relative logarithmic density is at most `1`. -/
theorem le_one_of_primeSetLogMass (P : Set ℕ) {κ C : ℝ}
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) : κ ≤ 1 := by
  classical
  by_contra hκ
  rw [not_le] at hκ
  set C₀ := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  obtain ⟨n, hn1, hnX⟩ := ((eventually_ge_atTop 1).and
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      ((C + C₀) / (κ - 1)))).exists
  rw [Function.comp_apply, div_lt_iff₀ (by linarith)] at hnX
  have hmass : primeSetLogMass P n ≤ ∑ k ∈ Icc 1 n with k.Prime, Real.log k / k := by
    rw [primeSetLogMass, primeSetCutoff_eq_filter]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun k _ _ => div_nonneg (Real.log_natCast_nonneg k) (Nat.cast_nonneg k)
  have h1 := RHTower.Mertens.mertens_first_prime n hn1
  have h2 := hP n hn1
  rw [abs_le] at h1 h2
  nlinarith [h1.2, h2.1]

/-- **The Wirsing bound for flip twins.** If the flipped primes have relative logarithmic density
`κ`, then `|Σ_{n ≤ N} ω_P(n)/n| ≪ (log N)^{b − 1}` for every `b ≥ 1` with `b > |2 − 2κ|`. -/
theorem exists_abs_gaugeHarmonicSum_primeSetFlip_le (P : Set ℕ) {κ C : ℝ}
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) {b : ℝ} (hb1 : 1 ≤ b)
    (hb : |2 - 2 * κ| < b) :
    ∃ A, 0 ≤ A ∧ ∀ N, 3 ≤ N →
      |gaugeHarmonicSum (primeSetFlip P) N| ≤ A * Real.log N ^ (b - 1) := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_gaugeHarmonicSum_le_rpow (β := 1 - 2 * κ)
    (fun a b ha hb => (primeSetFlip_isSignGauge P).mul ha hb) (abs_primeSetFlip_le P)
    (fun n hn => abs_primeMean_primeSetFlip_sub_le P hP hn) hb1
    (by rwa [show 1 + (1 - 2 * κ) = 2 - 2 * κ by ring])
  exact ⟨A, hA0, fun N hN => (hA N hN).2⟩

/-- **Flips of relative density above `1/2` have bounded harmonic sums.** -/
theorem exists_abs_gaugeHarmonicSum_primeSetFlip_le_const (P : Set ℕ) {κ C : ℝ} (hκ : 1 / 2 < κ)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) :
    ∃ A, ∀ N, 3 ≤ N → |gaugeHarmonicSum (primeSetFlip P) N| ≤ A := by
  have hκ1 := le_one_of_primeSetLogMass P hP
  obtain ⟨A, -, hA⟩ := exists_abs_gaugeHarmonicSum_primeSetFlip_le P hP le_rfl
    (by rw [abs_lt]; constructor <;> linarith)
  exact ⟨A, fun N hN => by simpa using hA N hN⟩

/-- A relative logarithmic density is nonnegative. -/
theorem nonneg_of_primeSetLogMass (P : Set ℕ) {κ C : ℝ}
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) : 0 ≤ κ := by
  by_contra hκ
  rw [not_le] at hκ
  obtain ⟨n, hn1, hnX⟩ := ((eventually_ge_atTop 1).and
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      (C / -κ))).exists
  rw [Function.comp_apply, div_lt_iff₀ (by linarith)] at hnX
  have hmass : 0 ≤ primeSetLogMass P n :=
    sum_nonneg fun k _ => div_nonneg (Real.log_natCast_nonneg k) (Nat.cast_nonneg k)
  have h2 := (abs_le.mp (hP n hn1)).2
  nlinarith

/-- **The Wirsing asymptotic for flip twins.** If the flipped primes have relative logarithmic
density `κ < 1/2`, then `Σ_{n ≤ N} ω_P(n)/n = C (log N)^{1 − 2κ} + O(1)`. -/
theorem exists_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le (P : Set ℕ) {κ C : ℝ}
    (hκ : κ < 1 / 2) (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) :
    ∃ c G : ℝ, ∀ N, 3 ≤ N →
      |gaugeHarmonicSum (primeSetFlip P) N - c * Real.log N ^ (1 - 2 * κ)| ≤ G := by
  have hκ0 := nonneg_of_primeSetLogMass P hP
  exact exists_abs_gaugeHarmonicSum_sub_rpow_le
    (fun a b ha hb => (primeSetFlip_isSignGauge P).mul ha hb) (abs_primeSetFlip_le P)
    (fun n hn => abs_primeMean_primeSetFlip_sub_le P hP hn) (by linarith) (by linarith)

/-- **The atomic Hodge index separates every flip twin of relative density `κ > 1/4`.** The Wirsing
bound gives `L(N)² = o(log N)`, so the twin has margin `0`. -/
theorem hodgeSeparates_primeSetFlip_of_primeSetLogMass (P : Set ℕ) {κ C : ℝ} (hκ : 1 / 4 < κ)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) :
    HodgeSeparates (primeSetFlip P) := by
  have hκ1 := le_one_of_primeSetLogMass P hP
  have habs : |2 - 2 * κ| = 2 - 2 * κ := abs_of_nonneg (by linarith)
  obtain ⟨A, -, hA⟩ := exists_abs_gaugeHarmonicSum_primeSetFlip_le P hP
    (b := max 1 ((2 - 2 * κ) / 2 + 3 / 4)) (le_max_left _ _)
    (by rw [habs]; exact lt_max_of_lt_right (by linarith))
  exact hodgeSeparates_of_harmonicSum_small (primeSetFlip_mul_self P)
    (tendsto_sq_div_log_of_rpow (max_lt (by norm_num) (by linarith)) hA)

end FlipTwins

end GaloisForLFunctions.RenormalizedIntersectionTheory
