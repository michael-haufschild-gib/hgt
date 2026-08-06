# π and θ carry the exponent-1/2 error term

`RHTower/Sieve/ChebyshevThetaBigO.lean`, `RHTower/Sieve/PrimeCountingBigO.lean`,
`RHTower/Sieve/SqrtLogDecayIntegral.lean` — all unconditional
(`[propext, Classical.choice, Quot.sound]`).

```
chebyshevTheta_sub_id_isBigO :
  ∃ c > 0, (Chebyshev.theta - id) =O[atTop] fun x => x * exp (-c * √(log x))

primeCounting_sub_logIntegral_isBigO :
  ∃ c > 0, (fun x => π(⌊x⌋) - ∫ t in Icc 2 x, (log t)⁻¹)
             =O[atTop] fun x => x * exp (-c * √(log x))
```

Both refine PNTPlus: `chebyshev_asymptotic` (θ ~ id) and `pi_asymp`/`pi_alt`/`pi_alt'`
(all `c =o[atTop] 1`) are qualitative; these give the rate.

## Do not rebuild — PNTPlus owns the passage

- `pi_asymp_aux : π(⌊x⌋) = θ x / log x + ∫_{Icc 2 x} θ t * (t * log²t)⁻¹` — partial summation.
- `integral_log_inv'' : 2/log 2 + ∫_{Icc 2 x}(log t)⁻¹ = x/log x + ∫_{Icc 2 x}(log t²)⁻¹` — the
  main term reassembling into the logarithmic integral.
- `chebyshev_asymptotic''` gives `f` with `θ x = x + x·f x` **and** `IntegrableOn f (Icc 2 x)` for
  every `x ≥ 2`.  That integrability is the expensive ingredient: θ is a step function, so the
  integral split is only legitimate because PNTPlus already banked it.
- `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log : 1 ≤ x → |ψ x − θ x| ≤ 2√x·log x`.
- `Chebyshev.psi_eq_sum_range` — the bridge from the corpus's `∑_{n ≤ N} Λ n` form.

## The reusable brick

```
exists_bound_setIntegral_sqrt_log_decay (hc : 0 < c) (hK : 0 ≤ K)
  (hint : ∀ x ≥ 2, IntegrableOn g (Icc 2 x))
  (hbd : ∀ᶠ t, |g t| ≤ K * exp (-c * √(log t))) :
  ∃ C ≥ 0, ∀ᶠ x, |∫ t in Icc 2 x, g t| ≤ C * (x * exp (-(c/2) * √(log x)))
```

Stated for an arbitrary integrand.  **The halving of `c` is intrinsic**, not slack: split at `√x`
and the top piece only gets `exp(−c√(log √x)) = exp(−(c/√2)√(log x))`.  A pure-power majorant
`exp(−c'√(log x))·(t/x)^α` cannot replace the split — at `t ≈ 2` the weight is `≈ 1` while any such
majorant is `≈ 0`.  The bottom piece contributes only `√x`, so the split is cheap.

Companion: `sqrt_log_sqrt_le` (`√(log x)/2 ≤ √(log t)` when `√x ≤ t`) — spending `√2` down to `2`
keeps every later constant rational.

## Lean names that cost time

- `isLittleO_log_rpow_atTop` is at the **root**, not `Real.isLittleO_log_rpow_atTop`.
- `Real.sqrt_le_self` does **not** exist; use `Real.sqrt_le_sqrt (x ≤ x^2)` + `Real.sqrt_sq`.
- `abs_add` is gone; the triangle inequality is `abs_add_le a b`.
- `∫ t in s, g t + h` parses with the integral binder swallowing `+ h`.  Every integral in a sum
  needs its own parentheses, or the `calc` LHS silently fails to match.
- `norm_setIntegral_le_of_norm_le_const` returns `C * μ.real s`; pair with
  `Real.volume_real_Ioc : volume.real (Ioc a b) = max (b - a) 0`.
