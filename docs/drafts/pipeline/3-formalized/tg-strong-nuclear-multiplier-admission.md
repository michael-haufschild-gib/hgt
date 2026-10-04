# TG C9.22b: strong multiplier limits in the genuine trace ideal

- **Stage:** 3-formalized
- **Route:** TG, source-to-Hardy operator-ideal admission
- **Parent:** tg-gamma-clock-nuclear-phase-admission.md
- **Production:** formal/GaloisForLFunctions/RHTower/StrongTraceNormMultiplierLimit.lean

## Exact analytic mechanism

For a uniformly bounded strongly convergent net A_i→A and any fixed nuclear
T, ||(A_i-A)T||_1→0. Strong convergence of the adjoints gives the right-action
version ||T(A_i-A)||_1→0. Neither operator-norm convergence nor separability
is assumed. This strengthens the inspected corpus's scalar trace limit to
convergence in the genuine nuclear norm.

Factor T=S V using the actual Hilbert–Schmidt factors from trace class.
For a Hilbert basis e_j, dominated convergence gives

 sum_j ||(A_i-A)S e_j||^2 → 0,

with summable majorant (C+||A||)^2 sum_j ||S e_j||^2. Its square root is the
actual Hilbert–Schmidt norm. Schatten Holder now bounds the nuclear error
by ||V||_2 ||(A_i-A)S||_2. Taking adjoints proves the right-action result.

## Audit and exact scope

2026-10-04: final foreground `lake --old env lean
GaloisForLFunctions/RHTower/StrongTraceNormMultiplierLimit.lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/StrongTraceNormMultiplierLimit.olean`
exits 0, empty diagnostics. All three public theorems pass separate /tmp
axiom audit: exactly propext, Classical.choice, Quot.sound. Wired in RHTower;
no umbrella/full build. Index0 records all three. Latest lint1 reports twelve
unrelated unreachable modules, no finding in this leaf. Default heartbeats.
Logs: `/tmp/tg-c922-strong-{final,axioms,index,lint}.log`.

This discharges the fixed-factor product mechanism for C9.22. It is not the
application to its varying clock symbols: their Schwartz convergence remains
open in Lean. Full relative prime–Gamma cubic compatibility, native arithmetic
energy and strict sub-unit control remain open; no RH conclusion follows.
