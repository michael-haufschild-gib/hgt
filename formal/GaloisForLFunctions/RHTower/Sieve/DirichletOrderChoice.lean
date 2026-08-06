import GaloisForLFunctions.RHTower.Sieve.DirichletLittleOh

/-!
# Choosing the order from `t`

The threshold form gives, for every order `K`, an estimate valid once `t` clears
`2π · exp (orderThreshold K)`.  Taking the *largest* order whose threshold `t` has already cleared
turns that family into a single function of `t`:

```text
littlewoodOrder t = greatest K with orderThreshold K ≤ log (t / 2π).
```

The search is legitimate because an order never exceeds its own threshold — `balanceBound K` already
dominates `2·2^K` — so the admissible orders lie below `⌈log (t/2π)⌉`, a genuine bound for the
search.

With this choice the estimate becomes `1 + log 2 + 2 log(t/2π)/(littlewoodOrder t - 4/3)`, and since
every fixed order is eventually admissible, one function realises every accuracy at once.
-/

namespace RHTower.Sieve

open Finset

/-- The threshold quantity of an order: past `2π · exp (orderThreshold K)` the order-`K` estimate
applies. -/
noncomputable def orderThreshold (K : ℕ) : ℝ :=
  max (largenessBound K) (balanceBound K) + 1

/-- The logarithm inside the balance quantity is at least `1`. -/
theorem one_le_balance_log {K : ℕ} (hK : 2 ≤ K) :
    (1 : ℝ) ≤ Real.log (7680 * ((K : ℝ) - 4 / 3) / Real.log 2) := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have harg : (3 : ℝ) ≤ 7680 * ((K : ℝ) - 4 / 3) / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    linarith
  have hpos : (0 : ℝ) < 7680 * ((K : ℝ) - 4 / 3) / Real.log 2 := by linarith
  have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  rw [Real.le_log_iff_exp_le hpos]
  linarith

/-- The balance quantity dominates `2·2^K`. -/
theorem two_mul_two_pow_le_balanceBound {K : ℕ} (hK : 2 ≤ K) :
    2 * (2 : ℝ) ^ K ≤ balanceBound K := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL := one_le_balance_log hK
  have hApos : (0 : ℝ) < 3 * (2 : ℝ) ^ K := by positivity
  have hx : (2 : ℝ) / 3 ≤ (K : ℝ) - 4 / 3 := by linarith
  have hstep1 : 3 * (2 : ℝ) ^ K * (2 / 3) ≤ 3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3) :=
    mul_le_mul_of_nonneg_left hx hApos.le
  have hc : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3) := by nlinarith
  have hstep2 : 3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3) * 1
      ≤ 3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3)
        * Real.log (7680 * ((K : ℝ) - 4 / 3) / Real.log 2) :=
    mul_le_mul_of_nonneg_left hL hc
  have hKlog : 0 ≤ (K : ℝ) * Real.log 2 := by positivity
  rw [balanceBound]
  nlinarith [hstep1, hstep2, hKlog]

/-- An order never exceeds its own threshold, so the search for the greatest admissible order is
bounded. -/
theorem cast_le_orderThreshold {K : ℕ} (hK : 2 ≤ K) : (K : ℝ) ≤ orderThreshold K := by
  have hb := two_mul_two_pow_le_balanceBound hK
  have hpow : (K : ℝ) ≤ (2 : ℝ) ^ K := by
    have h : K < 2 ^ K := Nat.lt_two_pow_self
    have hc : ((K : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast h.le
    have hcast : ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K := by push_cast; ring
    rwa [hcast] at hc
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
  have hmax : balanceBound K ≤ max (largenessBound K) (balanceBound K) := le_max_right _ _
  rw [orderThreshold]
  linarith

theorem nine_le_orderThreshold_two : (9 : ℝ) ≤ orderThreshold 2 := by
  have hb := two_mul_two_pow_le_balanceBound (K := 2) le_rfl
  have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
  rw [h4] at hb
  have hmax : balanceBound 2 ≤ max (largenessBound 2) (balanceBound 2) := le_max_right _ _
  rw [orderThreshold]
  linarith

/-- The greatest order whose threshold `t` has already cleared. -/
noncomputable def littlewoodOrder (t : ℝ) : ℕ :=
  Nat.findGreatest (fun K => orderThreshold K ≤ Real.log (t / (2 * Real.pi)))
    ⌈Real.log (t / (2 * Real.pi))⌉₊

/-- Clearing an order's threshold puts it below the chosen order. -/
theorem le_littlewoodOrder {t : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (h : orderThreshold K ≤ Real.log (t / (2 * Real.pi))) :
    K ≤ littlewoodOrder t := by
  refine Nat.le_findGreatest ?_ h
  have h1 : (K : ℝ) ≤ Real.log (t / (2 * Real.pi)) := le_trans (cast_le_orderThreshold hK) h
  have h2 : (K : ℝ) ≤ ((⌈Real.log (t / (2 * Real.pi))⌉₊ : ℕ) : ℝ) :=
    le_trans h1 (Nat.le_ceil _)
  exact_mod_cast h2

theorem two_le_littlewoodOrder {t : ℝ}
    (ht : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi))) : 2 ≤ littlewoodOrder t :=
  le_littlewoodOrder le_rfl ht

/-- The chosen order is itself admissible. -/
theorem orderThreshold_littlewoodOrder_le {t : ℝ}
    (ht : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi))) :
    orderThreshold (littlewoodOrder t) ≤ Real.log (t / (2 * Real.pi)) := by
  have h1 : ((2 : ℕ) : ℝ) ≤ Real.log (t / (2 * Real.pi)) :=
    le_trans (cast_le_orderThreshold (K := 2) le_rfl) ht
  have h2 : ((2 : ℕ) : ℝ) ≤ ((⌈Real.log (t / (2 * Real.pi))⌉₊ : ℕ) : ℝ) :=
    le_trans h1 (Nat.le_ceil _)
  have hb : (2 : ℕ) ≤ ⌈Real.log (t / (2 * Real.pi))⌉₊ := by exact_mod_cast h2
  exact Nat.findGreatest_spec (P := fun K => orderThreshold K ≤ Real.log (t / (2 * Real.pi)))
    hb ht

/-- Clearing `2π · exp (orderThreshold K)` is clearing the order's threshold. -/
theorem orderThreshold_le_log_of_le {t : ℝ} {K : ℕ}
    (hexp : 2 * Real.pi * Real.exp (orderThreshold K) ≤ t) :
    orderThreshold K ≤ Real.log (t / (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hq : Real.exp (orderThreshold K) ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀' h2π]
    exact hexp
  have h := Real.log_le_log (Real.exp_pos _) hq
  rwa [Real.log_exp] at h

theorem le_littlewoodOrder_of_exp {t : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (hexp : 2 * Real.pi * Real.exp (orderThreshold K) ≤ t) : K ≤ littlewoodOrder t :=
  le_littlewoodOrder hK (orderThreshold_le_log_of_le hexp)

/-- **The estimate at the order chosen from `t`.**  A single explicit function of `t` replaces the
family of fixed-order bounds. -/
theorem norm_dirichlet_partial_littlewood_order {t : ℝ} (ht16 : 16 * Real.pi ≤ t)
    (ht : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi))) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log 2
        + 2 * Real.log (t / (2 * Real.pi)) / ((littlewoodOrder t : ℝ) - 4 / 3) := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have ht0 : 0 < t := by linarith
  have hK := two_le_littlewoodOrder ht
  have hthr := orderThreshold_littlewoodOrder_le ht
  refine littlewood_threshold (littlewoodOrder t) hK t (max_le ht16 ?_)
  have hrw : max (largenessBound (littlewoodOrder t)) (balanceBound (littlewoodOrder t)) + 1
      = orderThreshold (littlewoodOrder t) := rfl
  rw [hrw, ← le_div_iff₀' h2π]
  have h := Real.exp_le_exp.mpr hthr
  rwa [Real.exp_log (by positivity)] at h

/-- **`o (log t)` with a single order function.**  The order is chosen from `t`, not from the
accuracy. -/
theorem littlewood_littleOh_explicit_order {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
          (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
        ≤ 1 + Real.log 2 + ε * Real.log (t / (2 * Real.pi)) := by
  set K : ℕ := orderForAccuracy ε with hKdef
  have hK : 2 ≤ K := two_le_orderForAccuracy ε
  have hKeps : 2 / ((K : ℝ) - 4 / 3) ≤ ε := orderForAccuracy_spec hε
  refine ⟨max (max (16 * Real.pi) (2 * Real.pi * Real.exp (orderThreshold 2)))
      (2 * Real.pi * Real.exp (orderThreshold K)), fun t hT => ?_⟩
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hA : max (16 * Real.pi) (2 * Real.pi * Real.exp (orderThreshold 2)) ≤ t :=
    le_trans (le_max_left _ _) hT
  have hB : 2 * Real.pi * Real.exp (orderThreshold K) ≤ t := le_trans (le_max_right _ _) hT
  have ht16 : 16 * Real.pi ≤ t := le_trans (le_max_left _ _) hA
  have ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi)) :=
    orderThreshold_le_log_of_le (le_trans (le_max_right _ _) hA)
  have hKle : K ≤ littlewoodOrder t := le_littlewoodOrder_of_exp hK hB
  refine le_trans (norm_dirichlet_partial_littlewood_order ht16 ht2) ?_
  have hLnn : 0 ≤ Real.log (t / (2 * Real.pi)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ h2π]
    linarith
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hOrdR : (K : ℝ) ≤ ((littlewoodOrder t : ℕ) : ℝ) := by exact_mod_cast hKle
  have hden : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
  have hden' : (0 : ℝ) < ((littlewoodOrder t : ℕ) : ℝ) - 4 / 3 := by linarith
  have hstep : 2 / (((littlewoodOrder t : ℕ) : ℝ) - 4 / 3) ≤ 2 / ((K : ℝ) - 4 / 3) := by
    rw [div_le_div_iff₀ hden' hden]
    linarith
  have hfin : 2 / (((littlewoodOrder t : ℕ) : ℝ) - 4 / 3) ≤ ε := le_trans hstep hKeps
  have hrw : 2 * Real.log (t / (2 * Real.pi)) / (((littlewoodOrder t : ℕ) : ℝ) - 4 / 3)
      = Real.log (t / (2 * Real.pi)) * (2 / (((littlewoodOrder t : ℕ) : ℝ) - 4 / 3)) := by
    field_simp
  rw [hrw]
  nlinarith [mul_le_mul_of_nonneg_left hfin hLnn]

end RHTower.Sieve
