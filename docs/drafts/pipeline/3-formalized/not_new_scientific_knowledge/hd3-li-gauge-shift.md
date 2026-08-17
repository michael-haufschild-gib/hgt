# HD3 Zero-Free Gauge Shifts Log-Defined Li Coefficients

- **ID:** hd3-li-gauge-shift
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), proof-route atlas normalization
- **Source:** random formula-graph node 91/100, `HD3` in `docs/consolidated/revision01/formulas-graph.md`
- **Statement:** The HD3 zero-free FE-symmetric gauge

```text
F_c(s) = exp(c(s-1/2)^2) xi(s)
```

has exactly the same zero divisor as `xi`, but it shifts the log-defined Li coefficients by

```text
delta lambda_n = c n^2.
```

Therefore Li coefficients computed from `log F` are not invariant under the HD3 gauge. The Li chart is a zero-divisor chart only after the zero-free Hadamard gauge has been canonically fixed or subtracted.

## Goal

Close a false atlas shortcut. The corpus already says the HD3 multiplier does not move zeros, source measure, or the divisor-based detectors. But log-defined coefficient charts can still move, because `log F = log xi + Q`. This card isolates the exact gauge term for the first nontrivial FE-symmetric zero-free multiplier.

## Gates

- [x] 0 -> 1 in-progress: random formula selected and checked against HD3/surrogate prior work
- [x] 1 -> 2 fully-proven: derivative formula complete
- [x] 2 -> 3 formalized: **DONE (2026-08-16)** — `GaloisForLFunctions.liLogCoeff_hd3Gauge`,
  `liLogCoeff_add_hd3Gauge`, `hd3_zero_iff`, `hd3Gauge_reflect` in
  `formal/GaloisForLFunctions/RHTower/HD3LiGaugeShift.lean`; `lake build` green; axiom footprint
  `[propext, Classical.choice, Quot.sound]`
- [ ] 3 -> 4 publication-ready: fold into the Li/Jensen/Hadamard atlas notes

## Proof

[PROVED HERE]

Use the standard log-defined Li coefficient functional

```text
lambda_n(f)
  = 1/(n-1)! * d^n/ds^n [s^(n-1) log f(s)] at s=1.
```

If

```text
F_c(s) = exp(Q_c(s)) xi(s),
qquad Q_c(s)=c(s-1/2)^2,
```

then additivity of `log` gives

```text
lambda_n(F_c) = lambda_n(xi) + delta_n(Q_c),
```

where

```text
delta_n(Q_c)
  = 1/(n-1)! * d^n/ds^n [s^(n-1)c(s-1/2)^2] at s=1.
```

Now

```text
s^(n-1)(s-1/2)^2 = s^(n+1) - s^n + (1/4)s^(n-1).
```

The `n`-th derivative of the last term is zero, while

```text
d^n/ds^n s^(n+1) at s=1 = (n+1)!,
d^n/ds^n s^n     at s=1 = n!.
```

Thus

```text
delta_n(Q_c)
  = c ((n+1)! - n!) / (n-1)!
  = c n^2.
```

The zero divisor is unchanged because `exp(Q_c)` is zero-free. The functional equation symmetry is also preserved because `Q_c` is even in `s-1/2`.

## Route Consequence

This does not weaken Li's criterion for the canonical completed `xi`; it explains why the canonical normalization is not optional. A Li/Jensen/Hadamard atlas edge must specify whether it is using:

```text
1. divisor Li coefficients, depending only on zeros, or
2. log-defined coefficients of a chosen entire representative.
```

Under HD3 these differ by an explicit polynomial gauge term. With `c < 0`, the shifted coefficients can be driven negative for large `n` without moving a single zero. With `c > 0`, they can be inflated. Hence unnormalized log-defined Li positivity is not a zero-divisor invariant.

The proof-route bridge should only use the canonical `xi` normalization, or explicitly subtract the HD3 zero-free gauge before comparing the Li chart to reciprocal-seam `T_k` positivity.

## Computation

The symbolic derivative check is archived in:

- `computations/2026-06-21-conway-hd3-li-gauge-shift.py`
- `computations/2026-06-21-conway-hd3-li-gauge-shift.txt`

## Log

- 2026-06-21 -- Conway: created from random formula-graph node 91/100 (`HD3`). Prior HD3 work established surrogate vacuity and detector invariance; this card adds the Li-chart normalization obstruction.

## Lean formalization — 2026-08-16

**Module:** `formal/GaloisForLFunctions/RHTower/HD3LiGaugeShift.lean` (wired into `RHTower.lean`).
**Axioms:** `[propext, Classical.choice, Quot.sound]` on every headline theorem — no `sorry`, no
added axiom.

| Paper step (§) | Lean name | Statement |
|-|-|-|
| the log-defined Li functional | `liLogCoeff` | `λ_n(g) = 1/(n−1)! · dⁿ/dsⁿ[s^{n−1} g(s)]|_{s=1}` |
| the HD3 gauge `Q_c(s) = c(s−1/2)²` | `hd3Gauge` | |
| "the FE symmetry is preserved because `Q_c` is even in `s − 1/2`" | `hd3Gauge_reflect` | `Q_c(1−s) = Q_c(s)` |
| "the zero divisor is unchanged because `exp(Q_c)` is zero-free" | `exp_hd3Gauge_ne_zero`, **`hd3_zero_iff`** | `exp(Q_c(s))·f(s) = 0 ↔ f(s) = 0` |
| `s^{n−1}(s−1/2)² = s^{n+1} − s^n + s^{n−1}/4`; the `n`-th derivative kills the last term | inside `liLogCoeff_hd3Gauge` (via mathlib's `iteratedDeriv_pow` and `Nat.descFactorial_eq_zero_iff_lt`) | |
| `dⁿ/dsⁿ s^{n+1}|_1 = (n+1)!`, `dⁿ/dsⁿ s^n|_1 = n!` | `Nat.descFactorial_eq_div`, `Nat.descFactorial_self` | |
| `((n+1)! − n!)/(n−1)! = n²` | `factorial_succ_eq` | `(n+1)! = n! + n²(n−1)!` |
| **`δλ_n = c n²`** | **`liLogCoeff_hd3Gauge`** | the gauge contributes exactly `c n²` |
| **`λ_n(F_c) = λ_n(ξ) + c n²`** | **`liLogCoeff_add_hd3Gauge`** | the log-defined Li chart is *not* gauge invariant |

The additivity theorem carries the differentiability hypothesis on the "log" that the card's
`log F = log ξ + Q` presupposes (`ContDiffAt` of `s ↦ s^{n−1}·g(s)` at `1`); the gauge computation
itself (`liLogCoeff_hd3Gauge`) is unconditional.

## Log (cont.)

- 2026-08-16 (Leaner) — **→ 3-formalized.**  The exact gauge term `c n²`, the zero-freeness and the
  FE symmetry of the HD3 multiplier are unconditional Lean theorems, so the card's atlas warning —
  unnormalised log-defined Li positivity is not a zero-divisor invariant — is now certified.
