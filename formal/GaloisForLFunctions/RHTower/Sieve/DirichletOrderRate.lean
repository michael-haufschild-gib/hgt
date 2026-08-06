import GaloisForLFunctions.RHTower.Sieve.DirichletOrderChoice

/-!
# The rate

The order chosen from `t` is the greatest admissible one, so the *next* order already fails:
`log (t/2π) < orderThreshold (littlewoodOrder t + 1)`.  A crude envelope

```text
orderThreshold M  ≤  34561 · M² · 2^M      (M ≥ 2)
```

turns that failure into a lower bound on the order.  Since an order is below `2^` of itself, the
square in the envelope is absorbed and the failure reads

```text
log (t/2π)  <  69122 · 2^(3·littlewoodOrder t),
```

so `littlewoodOrder t > log (log(t/2π)/69122) / (3 log 2)`: the order is `log₂ log t` up to an
additive constant times a factor `3`.  The estimate therefore has the shape

```text
‖∑_{n < 2^(R+1)} n^(-1-it)‖  ≤  1 + log 2 + O(log t / log log t),
```

which is Littlewood's exponent.
-/

namespace RHTower.Sieve

open Finset

/-- A crude envelope for the threshold quantity. -/
theorem orderThreshold_le_envelope {M : ℕ} (hM : 2 ≤ M) :
    orderThreshold M ≤ 34561 * (M : ℝ) ^ 2 * (2 : ℝ) ^ M := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lb : (2 : ℝ) / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hpow : (M : ℝ) ≤ (2 : ℝ) ^ M := by
    have h : M < 2 ^ M := Nat.lt_two_pow_self
    have hc : ((M : ℕ) : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast h.le
    have hcast : ((2 ^ M : ℕ) : ℝ) = (2 : ℝ) ^ M := by push_cast; ring
    rwa [hcast] at hc
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  -- the largeness quantity
  have hlargelog : Real.log ((M : ℝ) - 1) ≤ (M : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (M : ℝ) - 1 by linarith)
    linarith
  have hlognn : (0 : ℝ) ≤ Real.log ((M : ℝ) - 1) := Real.log_nonneg (by linarith)
  have hp1nn : (0 : ℝ) ≤ ((M : ℝ) - 1) * ((M : ℝ) - 4 / 3) := by nlinarith
  have hp2 : ((M : ℝ) - 1) * ((M : ℝ) - 4 / 3) * Real.log ((M : ℝ) - 1)
      ≤ (M : ℝ) * (M : ℝ) * (M : ℝ) := by
    calc ((M : ℝ) - 1) * ((M : ℝ) - 4 / 3) * Real.log ((M : ℝ) - 1)
        ≤ ((M : ℝ) - 1) * ((M : ℝ) - 4 / 3) * (M : ℝ) :=
          mul_le_mul_of_nonneg_left hlargelog hp1nn
      _ ≤ (M : ℝ) * (M : ℝ) * (M : ℝ) := by nlinarith
  have hlarge : largenessBound M ≤ (M : ℝ) ^ 3 + (M : ℝ) := by
    rw [largenessBound]
    nlinarith [hp2, hlog2le]
  have hcube : (M : ℝ) ^ 3 ≤ (M : ℝ) ^ 2 * (2 : ℝ) ^ M := by
    nlinarith [hpow, sq_nonneg (M : ℝ)]
  have hlarge' : largenessBound M ≤ (M : ℝ) ^ 2 * (2 : ℝ) ^ M + (M : ℝ) := by linarith
  -- the balance quantity
  have hargpos : (0 : ℝ) < 7680 * ((M : ℝ) - 4 / 3) / Real.log 2 := by
    have hnum : (0 : ℝ) < 7680 * ((M : ℝ) - 4 / 3) := by linarith
    exact div_pos hnum hlog2pos
  have hlogb : Real.log (7680 * ((M : ℝ) - 4 / 3) / Real.log 2) ≤ 11520 * (M : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hargpos
    have hdiv : 7680 * ((M : ℝ) - 4 / 3) / Real.log 2 ≤ 11520 * (M : ℝ) := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith
    linarith
  have hbalnn : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ M * ((M : ℝ) - 4 / 3) := by nlinarith
  have hb1 : 3 * (2 : ℝ) ^ M * ((M : ℝ) - 4 / 3)
        * Real.log (7680 * ((M : ℝ) - 4 / 3) / Real.log 2)
      ≤ 3 * (2 : ℝ) ^ M * ((M : ℝ) - 4 / 3) * (11520 * (M : ℝ)) :=
    mul_le_mul_of_nonneg_left hlogb hbalnn
  have hb2 : 3 * (2 : ℝ) ^ M * ((M : ℝ) - 4 / 3) * (11520 * (M : ℝ))
      ≤ 34560 * (M : ℝ) ^ 2 * (2 : ℝ) ^ M := by
    have hstep : ((M : ℝ) - 4 / 3) * (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left hstep hpowpos.le
    nlinarith [h3]
  have hbal : balanceBound M ≤ 34560 * (M : ℝ) ^ 2 * (2 : ℝ) ^ M + (M : ℝ) := by
    rw [balanceBound]
    nlinarith [hb1, hb2, hlog2le]
  -- assembling
  have hsq : (0 : ℝ) ≤ (M : ℝ) ^ 2 * (2 : ℝ) ^ M := by positivity
  have hmax : max (largenessBound M) (balanceBound M)
      ≤ 34560 * (M : ℝ) ^ 2 * (2 : ℝ) ^ M + (M : ℝ) := by
    refine max_le (le_trans hlarge' ?_) hbal
    linarith
  have hM2 : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have s1 : (4 : ℝ) * (2 : ℝ) ^ M ≤ (M : ℝ) ^ 2 * (2 : ℝ) ^ M :=
    mul_le_mul_of_nonneg_right hM2 hpowpos.le
  have hfin : (M : ℝ) + 1 ≤ (M : ℝ) ^ 2 * (2 : ℝ) ^ M := by linarith
  rw [orderThreshold]
  linarith

/-- The chosen order is below the logarithm of the target. -/
theorem two_pow_littlewoodOrder_lt {t : ℝ}
    (ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi))) :
    (2 : ℝ) ^ (littlewoodOrder t) < Real.log (t / (2 * Real.pi)) := by
  have hK := two_le_littlewoodOrder ht2
  have hb := two_mul_two_pow_le_balanceBound hK
  have hmax : balanceBound (littlewoodOrder t)
      ≤ max (largenessBound (littlewoodOrder t)) (balanceBound (littlewoodOrder t)) :=
    le_max_right _ _
  have hthr := orderThreshold_littlewoodOrder_le ht2
  rw [orderThreshold] at hthr
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (littlewoodOrder t) := by positivity
  linarith

theorem succ_le_two_pow_littlewoodOrder (t : ℝ) :
    ((littlewoodOrder t : ℝ) + 1) ≤ (2 : ℝ) ^ (littlewoodOrder t) := by
  have hnat : littlewoodOrder t + 1 ≤ 2 ^ littlewoodOrder t := Nat.lt_two_pow_self
  have hc : ((littlewoodOrder t + 1 : ℕ) : ℝ) ≤ ((2 ^ littlewoodOrder t : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hcast : ((2 ^ littlewoodOrder t : ℕ) : ℝ) = (2 : ℝ) ^ (littlewoodOrder t) := by
    push_cast; ring
  rw [hcast] at hc
  push_cast at hc
  exact hc

/-- **Maximality.**  The next order already fails. -/
theorem log_lt_orderThreshold_succ {t : ℝ}
    (ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi))) :
    Real.log (t / (2 * Real.pi)) < orderThreshold (littlewoodOrder t + 1) := by
  rcases lt_or_ge (Real.log (t / (2 * Real.pi))) (orderThreshold (littlewoodOrder t + 1)) with
    h | hcon
  · exact h
  exfalso
  have hlt := two_pow_littlewoodOrder_lt ht2
  have hsucc := succ_le_two_pow_littlewoodOrder t
  have hcap : littlewoodOrder t + 1 ≤ ⌈Real.log (t / (2 * Real.pi))⌉₊ := by
    have h1 : ((littlewoodOrder t + 1 : ℕ) : ℝ) ≤ Real.log (t / (2 * Real.pi)) := by
      push_cast
      linarith
    have h2 : ((littlewoodOrder t + 1 : ℕ) : ℝ)
        ≤ ((⌈Real.log (t / (2 * Real.pi))⌉₊ : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h2
  exact Nat.findGreatest_is_greatest
    (P := fun K => orderThreshold K ≤ Real.log (t / (2 * Real.pi)))
    (n := ⌈Real.log (t / (2 * Real.pi))⌉₊)
    (Nat.lt_succ_self (littlewoodOrder t)) hcap hcon

/-- **The failure, in closed form.** -/
theorem log_lt_two_pow_three_mul {t : ℝ}
    (ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi))) :
    Real.log (t / (2 * Real.pi)) < 69122 * (2 : ℝ) ^ (3 * littlewoodOrder t) := by
  set K : ℕ := littlewoodOrder t with hKdef
  have hK : 2 ≤ K := two_le_littlewoodOrder ht2
  have henv := orderThreshold_le_envelope (M := K + 1) (by omega)
  have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  rw [hcast] at henv
  have hstep := log_lt_orderThreshold_succ ht2
  have hsucc := succ_le_two_pow_littlewoodOrder t
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hsq : ((K : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ K) ^ 2 := by nlinarith [hsucc]
  have hs1 : (2 : ℝ) ^ (K + 1) = 2 * (2 : ℝ) ^ K := by rw [pow_succ]; ring
  have h3 : (2 : ℝ) ^ (3 * K) = ((2 : ℝ) ^ K) ^ 2 * (2 : ℝ) ^ K := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  calc Real.log (t / (2 * Real.pi)) < orderThreshold (K + 1) := hstep
    _ ≤ 34561 * ((K : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (K + 1) := henv
    _ = 34561 * ((K : ℝ) + 1) ^ 2 * (2 * (2 : ℝ) ^ K) := by rw [hs1]
    _ ≤ 34561 * ((2 : ℝ) ^ K) ^ 2 * (2 * (2 : ℝ) ^ K) := by nlinarith [hsq, hpowpos]
    _ = 69122 * (((2 : ℝ) ^ K) ^ 2 * (2 : ℝ) ^ K) := by ring
    _ = 69122 * (2 : ℝ) ^ (3 * K) := by rw [h3]

/-- The explicit lower bound the maximality yields: `log₂` of the target, up to a constant factor
`3` and an additive constant. -/
noncomputable def orderLowerBound (L : ℝ) : ℝ := Real.log (L / 69122) / (3 * Real.log 2)

/-- **The order is at least `orderLowerBound` of the target.** -/
theorem orderLowerBound_lt {t : ℝ}
    (ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi))) :
    orderLowerBound (Real.log (t / (2 * Real.pi))) < ((littlewoodOrder t : ℕ) : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hden : (0 : ℝ) < 3 * Real.log 2 := by linarith
  have hlt := two_pow_littlewoodOrder_lt ht2
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (littlewoodOrder t) := by positivity
  have hL0 : 0 < Real.log (t / (2 * Real.pi)) := lt_trans hpos hlt
  have hmain := log_lt_two_pow_three_mul ht2
  have hquot : Real.log (t / (2 * Real.pi)) / 69122
      < (2 : ℝ) ^ (3 * littlewoodOrder t) := by
    rw [div_lt_iff₀ (by norm_num)]
    linarith
  have hlog := Real.log_lt_log (by positivity) hquot
  rw [Real.log_pow] at hlog
  rw [orderLowerBound, div_lt_iff₀ hden]
  push_cast at hlog
  linarith

/-- **Littlewood's exponent.**  The estimate at the order chosen from `t`, with the order replaced
by its explicit lower bound: the error term is `O(log t / log log t)`. -/
theorem norm_dirichlet_partial_littlewood_rate {t : ℝ} (ht16 : 16 * Real.pi ≤ t)
    (ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi)))
    (hden : 4 / 3 < orderLowerBound (Real.log (t / (2 * Real.pi)))) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log 2
        + 2 * Real.log (t / (2 * Real.pi))
            / (orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3) := by
  refine le_trans (norm_dirichlet_partial_littlewood_order ht16 ht2) ?_
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlow := orderLowerBound_lt ht2
  have hLnn : 0 ≤ Real.log (t / (2 * Real.pi)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ h2π]
    linarith
  have hd1 : (0 : ℝ) < orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3 := by linarith
  have hd2 : (0 : ℝ) < ((littlewoodOrder t : ℕ) : ℝ) - 4 / 3 := by linarith
  have hstep : 2 * Real.log (t / (2 * Real.pi)) / (((littlewoodOrder t : ℕ) : ℝ) - 4 / 3)
      ≤ 2 * Real.log (t / (2 * Real.pi))
          / (orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3) := by
    rw [div_le_div_iff₀ hd2 hd1]
    nlinarith [hLnn, hlow]
  linarith

end RHTower.Sieve
