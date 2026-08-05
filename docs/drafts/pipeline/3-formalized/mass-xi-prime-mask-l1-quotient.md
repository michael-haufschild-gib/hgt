# Mass–Xi critical `ℓ¹` prime-mask quotient

## Status

- Lane: `3-formalized`
- Conjecture: `C35-A/B` proved
- Parent: C34 universal Euler-valuation quotient
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core

## Higher principle

C34 proves vertical Euler depth is a one-dimensional quotient.  The surviving obstruction is
horizontal across valuation-one primes.  Test the next canonical ideal: prime-diagonal masks whose
difference from a scalar is absolutely summable at the exact critical atom weight
`(log p)/sqrt(p)`.

## Conjecture loop

### C35-A — critical `ℓ¹` residual ideal

For `w : Nat.Primes → ℂ` and `c : ℂ`, assume

```text
Summable (fun p => ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0).
```

Prove the residual source

```text
R_(w,c)(a,τ) = ∑' p, (w p - c) * xiMassCenteredPrimeAtom a τ p
```

is uniformly bounded on every positive vertical line.

### C35-B — exact scalar quotient

Prove

```text
maskedLayer w = c * S₁ + R_(w,c).
```

Deduce:

```text
c = 0  → maskedLayer w is uniformly vertically bounded;
c ≠ 0  → (maskedLayer w bounded ↔ S₁ bounded ↔ RH).
```

### C35-C — fail criterion

If exact decomposition needs stronger assumptions than critical-weight `ℓ¹`, identify the sharp
summability boundary and formalize it.  Do not import any source or zero bound equivalent to RH.

## Novelty test

This must strictly extend C34.  C34 varies valuation depth uniformly over primes; C35 permits an
arbitrary prime-dependent mask and classifies every perturbation in the maximal obvious absolute
ideal.  Result matters only if the capstone proves the line-bound equivalence unconditionally.

## Result `[LEAN-PROVED]`

All conjectured statements hold at the exact critical atom weight.  Lean proves:

```text
maskedLayer(w) = c * S₁ + residual(w-c),
```

where the equality is between actual convergent `tsum`s, and

```text
sup_u ‖residual(w-c)(σ+iu)‖
  ≤ (∑' p, ‖w(p)-c‖ criticalWeight(p)) * ∫ exp(-σ|x|) dx.
```

Therefore:

```text
c = 0  → maskedLayer(w) is uniformly vertically bounded;
c ≠ 0  → (maskedLayer(w) bounded ↔ S₁ bounded ↔ RH).
```

This is strictly stronger than C34: `w` may vary arbitrarily with the prime and need not be
bounded.  Only its deviation from one scalar class must lie in the exact critical-weight `ℓ¹`
ideal.  Hence any source-changing mask capable of weakening the open core must have a genuinely
cofinal, non-`ℓ¹` horizontal deformation across primes.

## Lean declarations

- `RHTower.summable_norm_xiMassPrimeMaskResidualAtom`
- `RHTower.norm_xiMassPrimeMaskResidual_vertical_le`
- `RHTower.xiMassPrimeMaskedLayer_eq_scalar_add_residual`
- `RHTower.xiMassPrimeMaskedLineBound_of_scalar_eq_zero`
- `RHTower.xiMassPrimeMaskedLineBound_iff_valuationOne`
- `RHTower.riemannHypothesis_iff_xiMassPrimeMaskedLineBound`

Source:
`formal/GaloisForLFunctions/RHTower/XiMassPrimeMaskL1Quotient.lean`.

## Verification

- Numerical pre-certification separated a convergent example
  `∑_p log(p)/p^(3/2)` from the divergent non-ideal scale `∑_p 1/sqrt(p)`.
- `lake env lean GaloisForLFunctions/RHTower/XiMassPrimeMaskL1Quotient.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.XiMassPrimeMaskL1Quotient`: pass (`9477/9477`).
- Capstone axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, project axiom, `opaque`, or `unsafe` declaration.

## Log

- 2026-08-05 — opened after C34 proved every bounded valuation-only filter is detected by `b(1)`.
- 2026-08-05 — C35-A/B compiled without a mathematical repair; promoted to `3-formalized`.
