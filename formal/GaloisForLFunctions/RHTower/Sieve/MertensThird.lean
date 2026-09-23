import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount

/-!
# Mertens' third theorem

The reciprocal Euler product of the primes below `N` is comparable to `1/log N`:

```text
e^{-(K+1)}/log N ≤ ∏_{p ≤ N} (1 - 1/p) ≤ e^{E - M}/log N,
```

with the constants of the sharp second Mertens theorem.  The upper bound is `1 - x ≤ e^{-x}`
against the Mertens lower bound; the lower bound is `e^{-1/(p-1)} ≤ 1 - 1/p`, whose exponents sum
to `∑ 1/p + ∑ 1/(p(p-1)) ≤ mertensS N + 1` by telescoping.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-! ## The telescoping tail -/

theorem sum_inv_mul_pred_eq_mertensThird : ∀ N : ℕ, 1 ≤ N →
    ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) = 1 - 1 / (N : ℝ) := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.lt_or_ge n 1 with hn | hn
    · have hn0 : n = 0 := by omega
      subst hn0
      norm_num
    · have hins : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : (n + 1) ∉ Finset.Icc 2 n := by
        simp only [Finset.mem_Icc]
        omega
      rw [hins, Finset.sum_insert hnot, ih hn]
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hnne : ((n : ℝ)) ≠ 0 := ne_of_gt hn0
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      simp only [add_sub_cancel_right]
      field_simp
      ring

theorem sum_inv_mul_pred_le_one {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) ≤ 1 := by
  rw [sum_inv_mul_pred_eq_mertensThird N hN]
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  linarith

/-! ## The shifted reciprocal prime sum -/

theorem sum_inv_pred_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1) ≤ mertensS N + 1 := by
  have hsplit : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1)
      = mertensS N + ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [mertensS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    field_simp
    ring
  have hsub : Nat.primesLE N ⊆ Finset.Icc 2 N := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.two_le, hp.1⟩
  have htail : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => ?_
    rw [Finset.mem_Icc] at hk
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    positivity
  have hone := sum_inv_mul_pred_le_one (N := N) (by omega)
  linarith [hsplit, htail, hone]

/-! ## Mertens' third theorem -/

/-- The constant of the lower reciprocal Euler product. -/
noncomputable def mertensThirdLowerConst : ℝ := Real.exp (-(mertensUpperConst + 1))

/-- The constant of the upper reciprocal Euler product. -/
noncomputable def mertensThirdUpperConst : ℝ :=
  Real.exp ((2 * mertensFirstConst + 1 / 2) / Real.log 2 - meisselMertensConst)

theorem mertensThirdLowerConst_pos : 0 < mertensThirdLowerConst := Real.exp_pos _

theorem mertensThirdUpperConst_pos : 0 < mertensThirdUpperConst := Real.exp_pos _

/-- **Mertens' third theorem, lower bound.** -/
theorem mertensThirdLowerConst_div_log_le {N : ℕ} (hN : 2 ≤ N) :
    mertensThirdLowerConst / Real.log N ≤ ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos hN1
  have hterm : ∀ p ∈ Nat.primesLE N,
      Real.exp (-((1 : ℝ) / ((p : ℝ) - 1))) ≤ 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hp1ne : ((p : ℝ) - 1) ≠ 0 := ne_of_gt hp1
    have hp0ne : ((p : ℝ)) ≠ 0 := ne_of_gt hp0
    have hval : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / (p : ℝ) := by
      field_simp
    have hid : (1 : ℝ) / ((p : ℝ) - 1) + 1 = (p : ℝ) / ((p : ℝ) - 1) := by
      field_simp
      ring
    have hexp : (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp ((1 : ℝ) / ((p : ℝ) - 1)) := by
      rw [← hid]
      exact Real.add_one_le_exp _
    have hpos : (0 : ℝ) < Real.exp ((1 : ℝ) / ((p : ℝ) - 1)) := Real.exp_pos _
    have hkey : (p : ℝ) ≤ ((p : ℝ) - 1) * Real.exp ((1 : ℝ) / ((p : ℝ) - 1)) := by
      rw [div_le_iff₀ hp1] at hexp
      linarith
    rw [Real.exp_neg, hval, inv_eq_one_div, div_le_div_iff₀ hpos hp0]
    linarith
  have hprod : Real.exp (-∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1))
      ≤ ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹) := by
    calc Real.exp (-∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1))
        = ∏ p ∈ Nat.primesLE N, Real.exp (-((1 : ℝ) / ((p : ℝ) - 1))) := by
          rw [← Real.exp_sum]
          congr 1
          rw [← Finset.sum_neg_distrib]
      _ ≤ ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹) :=
          Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) hterm
  have hsum := sum_inv_pred_le hN
  have hmert := mertensS_le_logLog_add hN
  have hle : -∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1)
      ≥ -(logLog N + mertensUpperConst + 1) := by linarith
  have hexpmono : Real.exp (-(logLog N + mertensUpperConst + 1))
      ≤ Real.exp (-∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlogexp : Real.exp (logLog N) = Real.log N := by
    rw [logLog]
    exact Real.exp_log hlogN
  have hval : Real.exp (-(logLog N + mertensUpperConst + 1))
      = mertensThirdLowerConst / Real.log N := by
    rw [mertensThirdLowerConst, ← hlogexp, ← Real.exp_sub]
    congr 1
    ring
  rw [hval] at hexpmono
  linarith [hexpmono, hprod]

/-- **Mertens' third theorem, upper bound.** -/
theorem prod_one_sub_inv_le {N : ℕ} (hN : 2 ≤ N) :
    ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹) ≤ mertensThirdUpperConst / Real.log N := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos hN1
  have hterm : ∀ p ∈ Nat.primesLE N, (1 : ℝ) - (p : ℝ)⁻¹ ≤ Real.exp (-(p : ℝ)⁻¹) := by
    intro p hp
    have h := Real.add_one_le_exp (-(p : ℝ)⁻¹)
    linarith
  have hnonneg : ∀ p ∈ Nat.primesLE N, (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    linarith
  have hprod : ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹) ≤ Real.exp (-mertensS N) := by
    calc ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)
        ≤ ∏ p ∈ Nat.primesLE N, Real.exp (-(p : ℝ)⁻¹) :=
          Finset.prod_le_prod hnonneg hterm
      _ = Real.exp (-mertensS N) := by
          rw [← Real.exp_sum, mertensS, ← Finset.sum_neg_distrib]
          congr 1
          exact Finset.sum_congr rfl fun p _ => by rw [one_div]
  have hmert : logLog N + meisselMertensConst
      - (2 * mertensFirstConst + 1 / 2) / Real.log 2 ≤ mertensS N := by
    have h := abs_mertensS_sub_logLog_sub_const_le hN
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogN2 : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have hnum : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
      have hpos : (0 : ℝ) < mertensFirstConst :=
        lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 4)) (le_max_left _ _)
      linarith
    have hquot : (2 * mertensFirstConst + 1 / 2) / Real.log N ≤
        (2 * mertensFirstConst + 1 / 2) / Real.log 2 :=
      div_le_div_of_nonneg_left hnum hlog2 hlogN2
    have habs := (abs_le.mp h).1
    linarith
  have hexpmono : Real.exp (-mertensS N)
      ≤ Real.exp (-(logLog N + meisselMertensConst
        - (2 * mertensFirstConst + 1 / 2) / Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
  have hlogexp : Real.exp (logLog N) = Real.log N := by
    rw [logLog]
    exact Real.exp_log hlogN
  have hval : Real.exp (-(logLog N + meisselMertensConst
      - (2 * mertensFirstConst + 1 / 2) / Real.log 2))
      = mertensThirdUpperConst / Real.log N := by
    rw [mertensThirdUpperConst, ← hlogexp, ← Real.exp_sub]
    congr 1
    ring
  rw [hval] at hexpmono
  linarith [hprod, hexpmono]

end

end RHTower.Sieve
