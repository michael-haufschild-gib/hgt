import Mathlib

/-!
# No uniform radial floor for a factorially decaying amplitude

The source-lock transfer consumes its growth hypothesis only through `ccm_struct`, whose substantive
output is a **floor**: past index two, every radial scale is at least the second one,

```text
∀ j,  d₂ ≤ d_{j+2} ,       d_j = A_j · lam^{8j+1} · e^{−4π lam²} ,
```

which after cancelling the common factor is `A₂ ≤ A_{j+2}·lam^{8j}`, uniformly in `j`.

For the Fuchs amplitudes this fails.  The leakage asymptotic carries a factorial denominator, so
`A_{j+2}·K^j → 0` as `j → ∞` for **every** fixed `K` — the factorial beats any geometric factor — and
a sequence tending to zero eventually drops below the positive constant `A₂`.

Hence the floor is not merely unproved but false, and so is any weakening of the growth hypothesis
that still yields it.  A replacement route must avoid the radial floor entirely rather than derive
it from a weaker growth assumption.
-/

open Filter

namespace RHTower

/-- **No uniform floor under geometric-beating decay.**  If the shifted amplitudes times any fixed
geometric factor tend to zero, they eventually fall below the fixed positive value `A 2`, so the
uniform floor fails. -/
theorem exists_index_below_floor {A : ℕ → ℝ} (hA2 : 0 < A 2) {K : ℝ}
    (hdecay : Tendsto (fun j : ℕ => A (j + 2) * K ^ j) atTop (nhds 0)) :
    ∃ j : ℕ, A (j + 2) * K ^ j < A 2 :=
  (hdecay.eventually (gt_mem_nhds hA2)).exists

/-- **Factorial decay beats every geometric factor.**  For `A j = c^j / j!` with `c > 0`, and any
fixed `K`, the products `A (j+2)·K^j` tend to zero. -/
theorem factorial_amplitude_decay (c K : ℝ) :
    Tendsto (fun j : ℕ => (c ^ (j + 2) / (Nat.factorial (j + 2) : ℝ)) * K ^ j) atTop (nhds 0) := by
  have hbase : Tendsto (fun j : ℕ => |c * K| ^ j / (Nat.factorial j : ℝ)) atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop |c * K|
  have hb2 : Tendsto (fun j : ℕ => |c| ^ 2 * (|c * K| ^ j / (Nat.factorial j : ℝ)))
      atTop (nhds 0) := by
    have h := hbase.const_mul (|c| ^ 2)
    rwa [mul_zero] at h
  refine squeeze_zero_norm ?_ hb2
  intro j
  have hfacpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac2pos : (0 : ℝ) < (Nat.factorial (j + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 2)
  have hfac : (Nat.factorial j : ℝ) ≤ (Nat.factorial (j + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have heq : (c ^ (j + 2) / (Nat.factorial (j + 2) : ℝ)) * K ^ j
      = c ^ 2 * ((c * K) ^ j / (Nat.factorial (j + 2) : ℝ)) := by
    rw [pow_add, mul_pow]
    ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_pow, abs_of_pos hfac2pos]
  gcongr

/-- **The radial floor fails for factorially decaying amplitudes.**  Combining: with
`A j = c^j / j!` and `c > 0`, for every geometric factor `K` there is an index at which the uniform
floor `A 2 ≤ A (j+2)·K^j` is violated.  So the structural output of the growth hypothesis is false
for such amplitudes, not merely unavailable. -/
theorem factorial_amplitude_no_uniform_floor {c : ℝ} (hc : 0 < c) (K : ℝ) :
    ∃ j : ℕ, (c ^ (j + 2) / (Nat.factorial (j + 2) : ℝ)) * K ^ j
      < c ^ 2 / (Nat.factorial 2 : ℝ) := by
  have hA2 : (0 : ℝ) < c ^ 2 / (Nat.factorial 2 : ℝ) := by
    have : (0 : ℝ) < (Nat.factorial 2 : ℝ) := by norm_num
    positivity
  exact exists_index_below_floor (A := fun j => c ^ j / (Nat.factorial j : ℝ))
    (by simpa using hA2) (factorial_amplitude_decay c K)

end RHTower
