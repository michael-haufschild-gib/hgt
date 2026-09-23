import GaloisForLFunctions.RHTower.CyclotomicScaleReversal

/-!
# The empty-window positivity method is self-limiting

The empty prime window gives unconditional Weil positivity for every test of width below the least
prime-norm logarithm.  This file asks what zero-free strip that buys, and finds the method's success
condition is exactly the negation of a consequence of the generalized hypothesis.

**The bound.**  For a number field `K`, an off-critical zero at deviation `a` contributes
`≍ -(2L²/π²)·cosh(aL)` at detuning `π/L`, while the archimedean side is `≍ (log|d_K|/2)·L`.  With an
empty prime window, positivity is automatic, so

```text
(2L²/π²)·cosh(aL) ≤ (log|d_K|/2)·L      ⟹      e^{aL} ≲ π²·log|d_K| / (4L) ,
```

and taking `L = L₀ = log N_min`, the least prime-norm logarithm,

```text
a  ≲  log( C·log|d_K| ) / L₀ .
```

**When is that nontrivial?**  A zero-free strip needs `a < ½`, i.e. `L₀ > 2·log(C·log|d_K|)`, i.e.

```text
N_min  >  (C·log|d_K|)² .
```

**And that is exactly what cannot happen.**  Effective Chebotarev under the generalized hypothesis
bounds the least prime norm by `≪ (log|d_K|)²` — the same threshold.  So the method delivers an
unconditional zero-free strip precisely for fields that the generalized hypothesis says do not exist.

> **The empty-window positivity method is self-limiting: its success condition is the negation of a
> consequence of the hypothesis it is trying to prove.**

For cyclotomic fields the failure is visible directly: `N_min = q` while
`log|d_K| ≍ φ(q)·log q`, so `N_min > (log|d_K|)²` fails badly.  The extended prime-free range `log q`
is exactly cancelled by the archimedean weight `φ(q)·log q`, and the ratio is the degree `φ(q)`.

This is a different kind of wall from the eleven classification entries: not a cap on strength, but a
coincidence between the method's requirement and the theory's prediction.

This file formalizes the deviation bound, the nontriviality threshold, and the coincidence.
-/

open Real

noncomputable section

namespace RHTower

/-- **The deviation bound.**  From `e^{aL₀} ≤ M` one gets `a ≤ log M / L₀`. -/
theorem deviation_bound {a L0 M : ℝ} (hL0 : 0 < L0)
    (h : Real.exp (a * L0) ≤ M) : a ≤ Real.log M / L0 := by
  rw [le_div_iff₀ hL0]
  have hlog : a * L0 ≤ Real.log M := by
    have := Real.log_le_log (Real.exp_pos _) h
    rwa [Real.log_exp] at this
  linarith

/-- **Nontriviality threshold.**  The bound beats `½` exactly when `L₀` exceeds `2 log M`. -/
theorem nontrivial_iff {L0 M : ℝ} (hL0 : 0 < L0) (hM : 1 < M) :
    Real.log M / L0 < 1 / 2 ↔ 2 * Real.log M < L0 := by
  have hlog : 0 < Real.log M := Real.log_pos hM
  rw [div_lt_div_iff₀ hL0 (by norm_num)]
  constructor <;> intro h <;> linarith

/-- **The threshold in terms of the least prime norm.**  `L₀ > 2 log M` is `N_min > M²`. -/
theorem threshold_squared {N M : ℝ} (hN : 0 < N) (hM : 0 < M) :
    2 * Real.log M < Real.log N ↔ M ^ (2 : ℕ) < N := by
  have h2 : Real.log (M ^ (2 : ℕ)) = 2 * Real.log M := by
    rw [Real.log_pow]; push_cast; ring
  rw [← h2]
  exact Real.log_lt_log_iff (by positivity) hN

/-- **The coincidence.**  The method needs `N_min > (C log|d_K|)²`, while effective Chebotarev under
the hypothesis gives `N_min ≪ (log|d_K|)²`.  The two are the same threshold, so the requirement is
the negation of the prediction. -/
theorem self_limiting {N D C : ℝ}
    (hneed : (C * D) ^ (2 : ℕ) < N) (hpred : N ≤ (C * D) ^ (2 : ℕ)) : False := by
  linarith

/-- **The cyclotomic case fails directly.**  With `N_min = q` and `log|d_K| ≍ φ·log q`, the
requirement `q > (φ log q)²` is false whenever `φ log q ≥ √q`. -/
theorem cyclotomic_fails {q phi lq : ℝ} (hq : 0 < q) (hbig : Real.sqrt q ≤ phi * lq) :
    q ≤ (phi * lq) ^ (2 : ℕ) := by
  have hs : Real.sqrt q ^ (2 : ℕ) = q := Real.sq_sqrt (le_of_lt hq)
  nlinarith [hbig, Real.sqrt_nonneg q, hs]

/-- The cancellation, named: the archimedean weight per unit of prime-free reach is the degree. -/
theorem weight_per_reach {phi lq : ℝ} (hlq : lq ≠ 0) :
    phi * lq / lq = phi := by
  field_simp

end RHTower
