import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries

/-!
# Eigenvalue growth from a heat-trace bound

Lemma 3.3 and the counting steps inside Theorems 3.9 and 3.10 of Dai–Yoshikawa,
*Degeneration of Riemann surfaces and small eigenvalues of the Laplacian* (arXiv:2509.06151v2),
all run the same Cheng–Li argument.  A pointwise heat-kernel bound gives a heat-trace bound

```text
Σ_{i ≤ k} e^{−t λᵢ} ≤ C t^{−n}      (0 < t ≤ 1),
```

and, the spectrum being bounded below by `λ₀ > 0`, one may substitute the admissible time
`t = λ₀ / λ_k`.  Every summand is then at least `e^{−λ₀}`, so

```text
#{i ≤ k} · e^{−λ₀}  ≤  C (λ_k / λ₀)^n ,
```

which is a lower bound on `λ_k` growing like `k^{1/n}`.  For `n = 1` this is Lemma 3.3
(`λ_k ≥ C' k`); for `n = 2` it is the bound `λ_k ≥ B √k` used to dominate the tail of the heat
trace in Theorems 3.9 and 3.10.

The last section proves the domination itself: `Σ_k e^{−c√k}` converges for every `c > 0`, so the
tail sums appearing in those two theorems are dominated by a summable family.
-/

open Real Finset Filter

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-! ## The substitution step -/

/-- **The Cheng–Li substitution.**

If a finite family of eigenvalues is bounded above by `M`, with `0 < λ₀ ≤ M`, and the heat trace
over that family obeys `Σ e^{−tλᵢ} ≤ C t^{−n}` for every admissible time `t ∈ (0,1]`, then
substituting `t = λ₀/M` gives

```text
#s · e^{−λ₀} ≤ C (M/λ₀)^n .
```
-/
theorem card_mul_exp_neg_le_of_heatTrace_bound
    {ι : Type*} {lam : ι → ℝ} {C lam0 M : ℝ} {n : ℕ} {s : Finset ι}
    (hlam0 : 0 < lam0) (hlam0M : lam0 ≤ M)
    (hle : ∀ i ∈ s, lam i ≤ M)
    (htrace : ∀ t : ℝ, 0 < t → t ≤ 1 → ∑ i ∈ s, exp (-(t * lam i)) ≤ C / t ^ n) :
    (s.card : ℝ) * exp (-lam0) ≤ C * (M / lam0) ^ n := by
  have hM : 0 < M := lt_of_lt_of_le hlam0 hlam0M
  set t : ℝ := lam0 / M with ht
  have htpos : 0 < t := div_pos hlam0 hM
  have htle : t ≤ 1 := (div_le_one hM).mpr hlam0M
  have hlower : ∀ i ∈ s, exp (-lam0) ≤ exp (-(t * lam i)) := by
    intro i hi
    refine Real.exp_le_exp.mpr ?_
    have hmul : t * lam i ≤ t * M := mul_le_mul_of_nonneg_left (hle i hi) htpos.le
    have hM' : t * M = lam0 := by rw [ht]; field_simp
    rw [hM'] at hmul
    linarith
  have hsum : (s.card : ℝ) * exp (-lam0) ≤ ∑ i ∈ s, exp (-(t * lam i)) := by
    calc (s.card : ℝ) * exp (-lam0) = ∑ _i ∈ s, exp (-lam0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, exp (-(t * lam i)) := Finset.sum_le_sum hlower
  refine hsum.trans ((htrace t htpos htle).trans (le_of_eq ?_))
  rw [ht, div_pow, div_pow]
  field_simp

/-! ## The eigenvalue lower bound -/

/-- **Lemma 3.3 of Dai–Yoshikawa, polynomial form.**

For a nondecreasing spectrum bounded below by `λ₀ > 0` obeying the heat-trace bound
`Σ_{i ≤ k} e^{−tλᵢ} ≤ C t^{−n}` on `(0,1]`,

```text
(k+1) e^{−λ₀} ≤ C (λ_k / λ₀)^n .
```
-/
theorem heatTrace_eigenvalue_pow_bound
    {lam : ℕ → ℝ} {C lam0 : ℝ} {n k : ℕ}
    (hlam0 : 0 < lam0) (hmono : Monotone lam) (hge : ∀ i, lam0 ≤ lam i)
    (htrace : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∑ i ∈ Finset.range (k + 1), exp (-(t * lam i)) ≤ C / t ^ n) :
    ((k : ℝ) + 1) * exp (-lam0) ≤ C * (lam k / lam0) ^ n := by
  have h := card_mul_exp_neg_le_of_heatTrace_bound (lam := lam) (C := C) (lam0 := lam0)
    (M := lam k) (n := n) (s := Finset.range (k + 1)) hlam0 (hge k)
    (fun i hi => hmono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) htrace
  rw [Finset.card_range] at h
  push_cast at h
  exact h

/-- **Lemma 3.3 of Dai–Yoshikawa.**  The case `n = 1`: the eigenvalues grow at least linearly,
`λ_k ≥ (λ₀ e^{−λ₀}/C)(k+1)`. -/
theorem heatTrace_eigenvalue_linear_bound
    {lam : ℕ → ℝ} {C lam0 : ℝ} {k : ℕ}
    (hC : 0 < C) (hlam0 : 0 < lam0) (hmono : Monotone lam) (hge : ∀ i, lam0 ≤ lam i)
    (htrace : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∑ i ∈ Finset.range (k + 1), exp (-(t * lam i)) ≤ C / t ^ 1) :
    lam0 * exp (-lam0) / C * ((k : ℝ) + 1) ≤ lam k := by
  have h := heatTrace_eigenvalue_pow_bound hlam0 hmono hge htrace
  rw [pow_one] at h
  have h2 : ((k : ℝ) + 1) * exp (-lam0) * lam0 ≤ C * lam k := by
    have hmul := mul_le_mul_of_nonneg_right h hlam0.le
    have hr : C * (lam k / lam0) * lam0 = C * lam k := by field_simp
    rw [hr] at hmul
    linarith [hmul]
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  have hcomm : lam0 * exp (-lam0) * ((k : ℝ) + 1) = ((k : ℝ) + 1) * exp (-lam0) * lam0 := by ring
  rw [hcomm]
  linarith [h2]

/-- **The `√k` growth used in Theorems 3.9 and 3.10.**  The case `n = 2`:
`λ_k ≥ λ₀ √((k+1) e^{−λ₀}/C)`. -/
theorem heatTrace_eigenvalue_sqrt_bound
    {lam : ℕ → ℝ} {C lam0 : ℝ} {k : ℕ}
    (hC : 0 < C) (hlam0 : 0 < lam0) (hmono : Monotone lam) (hge : ∀ i, lam0 ≤ lam i)
    (htrace : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∑ i ∈ Finset.range (k + 1), exp (-(t * lam i)) ≤ C / t ^ 2) :
    lam0 * Real.sqrt (((k : ℝ) + 1) * exp (-lam0) / C) ≤ lam k := by
  have h := heatTrace_eigenvalue_pow_bound hlam0 hmono hge htrace
  have hratio : ((k : ℝ) + 1) * exp (-lam0) / C ≤ (lam k / lam0) ^ 2 := by
    rw [div_le_iff₀ hC]
    linarith [h]
  have hlamk : 0 < lam k := lt_of_lt_of_le hlam0 (hge k)
  have hq : 0 < lam k / lam0 := div_pos hlamk hlam0
  have hsq := Real.sqrt_le_sqrt hratio
  rw [Real.sqrt_sq hq.le] at hsq
  calc lam0 * Real.sqrt (((k : ℝ) + 1) * exp (-lam0) / C)
      ≤ lam0 * (lam k / lam0) := mul_le_mul_of_nonneg_left hsq hlam0.le
    _ = lam k := by field_simp

/-! ## The dominating series

Theorems 3.9 and 3.10 pass to the limit inside `∫₁^∞ Σ_m e^{−tλ_m(s)} dt/t` by dominating the tail
uniformly in the deformation parameter by `Σ_m e^{−tB√m}`.  That series converges. -/

/-- `(y/5)^5 ≤ e^y` for `y ≥ 0`: the tangent-line bound `1 + y/5 ≤ e^{y/5}`, raised to the fifth
power. -/
theorem pow_five_div_le_exp {y : ℝ} (hy : 0 ≤ y) : (y / 5) ^ 5 ≤ exp y := by
  have h1 : y / 5 ≤ exp (y / 5) := by
    have := Real.add_one_le_exp (y / 5)
    linarith
  have h2 : (y / 5) ^ 5 ≤ (exp (y / 5)) ^ 5 := pow_le_pow_left₀ (by positivity) h1 5
  have h3 : (exp (y / 5)) ^ 5 = exp y := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3] at h2
  exact h2

/-- **The dominating series converges.**  For `c > 0` the family `k ↦ e^{−c√k}` is summable:
beyond `k ≥ (5/c)^{10}` one has `k² ≤ e^{c√k}`, and `Σ k^{−2}` converges. -/
theorem summable_exp_neg_mul_sqrt {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℕ => exp (-(c * Real.sqrt k)) := by
  have hkey : ∀ᶠ k : ℕ in atTop, ‖exp (-(c * Real.sqrt k))‖ ≤ 1 / ((k : ℝ) ^ 2) := by
    have hthr : ∀ᶠ k : ℕ in atTop, ((5 : ℝ) / c) ^ 10 ≤ (k : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (((5 : ℝ) / c) ^ 10)
    filter_upwards [hthr, eventually_gt_atTop 0] with k hk hk0
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
    -- `√k ≥ (5/c)^5`
    have hsqrt : ((5 : ℝ) / c) ^ 5 ≤ Real.sqrt (k : ℝ) := by
      have h := Real.sqrt_le_sqrt hk
      rwa [show ((5 : ℝ) / c) ^ 10 = (((5 : ℝ) / c) ^ 5) ^ 2 by ring,
        Real.sqrt_sq (by positivity)] at h
    have hfactor : (1 : ℝ) ≤ (c / 5) ^ 5 * Real.sqrt (k : ℝ) := by
      have h1 : (c / 5) ^ 5 * ((5 : ℝ) / c) ^ 5 = 1 := by field_simp
      calc (1 : ℝ) = (c / 5) ^ 5 * ((5 : ℝ) / c) ^ 5 := h1.symm
        _ ≤ (c / 5) ^ 5 * Real.sqrt (k : ℝ) :=
            mul_le_mul_of_nonneg_left hsqrt (by positivity)
    have hsqk : Real.sqrt (k : ℝ) ^ 4 = (k : ℝ) ^ 2 := by
      have h2 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hkpos.le
      calc Real.sqrt (k : ℝ) ^ 4 = (Real.sqrt (k : ℝ) ^ 2) ^ 2 := by ring
        _ = (k : ℝ) ^ 2 := by rw [h2]
    have hid : ((c * Real.sqrt (k : ℝ)) / 5) ^ 5
        = ((c / 5) ^ 5 * Real.sqrt (k : ℝ)) * (k : ℝ) ^ 2 := by
      rw [← hsqk]; ring
    have hexp : ((c * Real.sqrt (k : ℝ)) / 5) ^ 5 ≤ exp (c * Real.sqrt (k : ℝ)) :=
      pow_five_div_le_exp (by positivity)
    have hlow : (k : ℝ) ^ 2 ≤ exp (c * Real.sqrt (k : ℝ)) := by
      refine le_trans ?_ hexp
      rw [hid]
      nlinarith [hfactor, sq_nonneg ((k : ℝ))]
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) hlow
  refine Summable.of_norm_bounded_eventually_nat ?_ hkey
  exact Real.summable_one_div_nat_pow.mpr (by norm_num)

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
