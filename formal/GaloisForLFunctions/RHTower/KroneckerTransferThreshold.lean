import GaloisForLFunctions.RHTower.PrimeAmplitudeUniformBound

/-!
# The transfer threshold: when the Bohr torus model becomes valid along the Kronecker line

The prime symbol of the Weil functional is a function on the Bohr torus, sampled along the Kronecker
line `ξ ↦ (ξ log p)_{p ≤ N}`.  Concentration estimates — the previous module supplies the exact
constants — hold on the torus with full measure, but the Weil condition is only needed along the
line, a set of measure zero.  Transferring requires the line to be equidistributed at the resolution
of the estimate, and that costs height.

The cost is bounded below by an elementary count, with no arithmetic input at all.  Partition the
torus `ℝ^r/ℤ^r` into `M^r` boxes of side `1/M`.  Parameterize a curve by arclength: each time it
enters a new box some coordinate has crossed a grid hyperplane, and the number of crossings of the
hyperplanes orthogonal to coordinate `i` is at most `1 + M·(total variation of coordinate i)`, which
is at most `1 + M·L`.  So a curve of length `L` meets at most `1 + r + r·M·L` boxes.  If its
`1/M`-neighbourhood is to cover the torus it must meet all `M^r` of them, whence

```text
M^r ≤ 1 + r + r·M·L        and therefore        L ≥ M^{r-1}/(2r)   for r ≥ 3.
```

For the Kronecker line the curve traced by `ξ ∈ [0,T]` has length `T·‖λ‖₂` with `λ_p = log p`, so

```text
log T ≥ (r-1)·log M - log(2r) - log‖λ‖₂ ,      r = π(N),  ‖λ‖₂ = (Σ_{p≤N} log²p)^{1/2}.
```

Resolving the torus at scale `1/M` therefore demands `log T ≳ π(N)·log M`, growing like `N/log N`.
The prime symbol itself only lives at scale `√N`.  So the heights at which the torus model becomes
applicable are exponentially beyond the heights at which the prime symbol is already of full size:
**no probabilistic argument on the Bohr torus can establish Weil positivity, because the Weil
condition is required precisely at the heights where the line provably has not equidistributed.**

This is the third ceiling of the programme, after the linear one and its quadratic counterpart.  The
count below is unconditional and elementary; the only inputs are the covering hypothesis and `r ≥ 3`.
-/

open Real

noncomputable section

namespace RHTower

/-- `2(1+r) ≤ 2^r` for `r ≥ 3`. -/
theorem two_mul_one_add_le_two_pow {r : ℕ} (hr : 3 ≤ r) : (2 : ℝ) * (1 + (r : ℝ)) ≤ 2 ^ r := by
  induction r with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · have hn2 : n = 2 := by omega
      subst hn2; norm_num
    · have h := ih hn
      have h8 : (8 : ℝ) ≤ 2 ^ n := by
        have : (2 : ℝ) ^ 3 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
        norm_num at this; linarith
      rw [pow_succ]
      push_cast
      linarith

/-- **Covering lower bound.**  A curve of length `L` in the `r`-torus meets at most `1 + r + r M L`
boxes of side `1/M`; if its `1/M`-neighbourhood covers the torus it must meet all `M^r`, and for
`r ≥ 3` that forces `L ≥ M^{r-1}/(2r)`. -/
theorem length_ge_of_cover {r M : ℕ} {L : ℝ} (hr : 3 ≤ r) (hM : 2 ≤ M) (_hL : 0 ≤ L)
    (hcover : (M : ℝ) ^ r ≤ 1 + r + r * M * L) :
    (M : ℝ) ^ r / (2 * r * M) ≤ L := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  -- `2(1 + r) ≤ 2^r ≤ M^r`, so `1 + r ≤ M^r/2`
  have hpow : (2 : ℝ) * (1 + (r : ℝ)) ≤ (M : ℝ) ^ r := by
    have h2r := two_mul_one_add_le_two_pow hr
    have hmono : (2 : ℝ) ^ r ≤ (M : ℝ) ^ r := pow_le_pow_left₀ (by norm_num) hMR r
    linarith
  have hhalf : (1 : ℝ) + (r : ℝ) ≤ (M : ℝ) ^ r / 2 := by linarith
  have hstep : (M : ℝ) ^ r / 2 ≤ (r : ℝ) * (M : ℝ) * L := by linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Logarithmic form: resolving the `r`-torus at scale `1/M` along a curve of length `L` forces
`log L ≥ (r-1) log M - log(2r)`. -/
theorem log_length_ge_of_cover {r M : ℕ} {L : ℝ} (hr : 3 ≤ r) (hM : 2 ≤ M) (hL : 0 < L)
    (hcover : (M : ℝ) ^ r ≤ 1 + r + r * M * L) :
    ((r : ℝ) - 1) * Real.log M - Real.log (2 * r) ≤ Real.log L := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hbase := length_ge_of_cover hr hM hL.le hcover
  have hposq : (0 : ℝ) < (M : ℝ) ^ r / (2 * r * M) := by positivity
  have hlog : Real.log ((M : ℝ) ^ r / (2 * r * M)) ≤ Real.log L :=
    Real.log_le_log hposq hbase
  have hexpand : Real.log ((M : ℝ) ^ r / (2 * r * M))
      = (r : ℝ) * Real.log M - (Real.log (2 * r) + Real.log M) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
      show (2 : ℝ) * (r : ℝ) * (M : ℝ) = (2 * (r : ℝ)) * (M : ℝ) from by ring,
      Real.log_mul (by positivity) (by positivity)]
  rw [hexpand] at hlog
  linarith

/-- **Transfer threshold for the Kronecker line.**  The curve traced by `ξ ∈ [0,T]` has length
`T·Λ` with `Λ = ‖(log p)_{p≤N}‖₂`, so resolving the `π(N)`-torus at scale `1/M` forces
`log T ≥ (π(N) - 1)·log M - log(2π(N)) - log Λ`.  The threshold grows like `π(N)·log M`, whereas the
prime symbol is already of size `√N`. -/
theorem log_height_ge_of_cover {r M : ℕ} {T Λ : ℝ} (hr : 3 ≤ r) (hM : 2 ≤ M)
    (hT : 0 < T) (hΛ : 0 < Λ)
    (hcover : (M : ℝ) ^ r ≤ 1 + r + r * M * (T * Λ)) :
    ((r : ℝ) - 1) * Real.log M - Real.log (2 * r) - Real.log Λ ≤ Real.log T := by
  have hprod : (0 : ℝ) < T * Λ := mul_pos hT hΛ
  have h := log_length_ge_of_cover hr hM hprod hcover
  rw [Real.log_mul (ne_of_gt hT) (ne_of_gt hΛ)] at h
  linarith

end RHTower
