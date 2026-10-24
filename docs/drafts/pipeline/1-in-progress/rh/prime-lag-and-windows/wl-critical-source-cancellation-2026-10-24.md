# WL — critical cancellation in the actual prime source

- **ID:** wl-critical-source-cancellation-2026-10-24
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md`, WL; literal Lean source.
- **Statement:** For every ε > 0, the actual logarithmic Chebyshev deficit
  `D(T) = ∫₀ᵀ (exp(t) − ψ(exp(t))) dt` admits a one-sided bound
  `D(T) ≤ Cε exp((1/2 + ε)T)` for all sufficiently large T.

## Goal

Derive the bound from actual prime arithmetic and discharge the existing WL
receiver. The full task ends only with an unconditional Lean proof of RH.
Another receiver, a numerical improvement, a model obstruction, or an exact
identity with an unpaid remainder does not complete this task.

## Constraints

No web searches, external novelty checks, or numerical experiments. No new
analytic assumptions, axioms, placeholders, or raised Lean resource limits.
Preserve unrelated work. Compile only individual required files with
`lake --old env lean` from `formal/`, one owned foreground process at a time.

## Established inputs inspected

- `RHTower.ccmLogChebyshevDeficitPrimitive_eq_prime_log_tents`
  (`CCMPrimeDeficitPrimeWork.lean`):
  `D(T) = exp(T) − 1 − Σ(n ≤ exp(T)) Λ(n)(T − log(n))`.
- `RHTower.ccmPrimeDeficitCriticalEnergy_prime_work_balance`
  (`CCMPrimeDeficitPrimeWork.lean`):
  the full signed prime-entry work equals half the terminal critical energy
  plus half its accumulated integral. Its nonnegativity gives the opposite
  direction from the upper energy payment still required.
- `RHTower.ccmLogChebyshevDeficitPrimitive_scale_descent`
  (`CCMPrimeDeficitScaleDescent.lean`):
  the higher-power sector is a half-radius copy plus an explicitly bounded
  positive cubic-root remainder. The prime-only same-scale deficit remains.
- `PrimeWindowCeilingVinogradovKorobovRemainder`:
  the unconditional envelope is `C exp(T − κ T^a)`, `0 < a < 3/5`.
  Its leading exponent remains 1.

The five declarations listed in the verification section received a fresh
dependency audit. Other observations here remain source inspections.

## Direct attack

Keep the complete signed arithmetic source together. Investigate the exact
Selberg convolution and the Möbius inversion of factorial/logarithmic tents
before applying absolute values. Seek cancellation of the full same-scale
remainder, including the moving hyperbola boundary. The first unproved step
must remain explicit; it must not become a premise of a claimed solution.

**[OPEN CORE]** Obtain an unconditional critical-scale upper estimate for the
signed remainder of the actual prime source. Existing prime-power descent
does not estimate the prime-only same-scale term.

## Gates

- [x] Exact source and missing estimate identified.
- [ ] Dependency-closed paper proof of the source estimate.
- [ ] Lean formalization, direct final compilation, and transitive axiom audit.
- [ ] Existing WL receiver discharged and unconditional RH conclusion audited.

## Research status

Active. No claimed source estimate or RH proof. External and novelty audits
are deliberately omitted under the user's instruction.

## Direct-attack findings

The existing finite identity `ccmLogChebyshevDeficitPrimitive_dilation_conservation`
already gives, with `x = exp(T)` and `N = floor(x)`,

```
Σ(n ≤ x) D(log(x/n))
  = x H_N − N − Σ(k ≤ x) log(k) log(x/k) =: S(T).
```

`ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation` is its exact inverse.
`abs_ccmLogChebyshevDeficitPrimitive_sub_moebius_tail_le` already proves

```
|D(T) − (explicitWork(T) + L M(floor(exp(T))) + transientTail(T))|
  ≤ (T + 14)/4.
```

Thus eliminating the small-divisor transient is not new work. The signed
combination inside the parentheses still needs the critical-scale estimate;
estimating its terms separately has not supplied it.

For clarity, the ordinary Laplace transforms for real `s > 1` can be derived
directly from the absolutely convergent prime series:

```
Laplace(D)(s) = 1/(s(s−1)) + ζ'(s)/(s² ζ(s)),
Laplace(S)(s) = ζ(s)/(s(s−1)) + ζ'(s)/s².
```

Indeed, integration of `exp(T) − 1` gives `1/(s(s−1))`, integration of each
tent `(T−log n)_+` gives `n^(−s)/s²`, and
`Σ Λ(n)n^(−s) = −ζ'(s)/ζ(s)`. Multiplicative delays multiply the transform
by `ζ(s)`. Absolute convergence for `s > 1` justifies these interchanges.
This calculation is an explanatory paper observation, not a new Lean theorem.
It supplies no justification for moving the inverse transform into the
critical half-plane. Such a move needs the unresolved source estimate or an
independently proved continuation, not division by `ζ` across possible zeros.

The inspected Selberg formula has a remainder bounded by `410N`, not by
square-root scale. The Euler half-logarithmic balance retains the deleted-prime
work and the lower-order surviving-prime work with opposite signs. Neither
their nonnegativity nor the half-logarithmic force estimate bounds the complete
signed difference. No term has been dropped from the requested estimate.

**Outcome:** no significant obstacle closed in this pass. These observations
are a record of the exact unfinished argument, not an additional criterion or
a claimed new no-go. The next proof step must estimate the complete long-tail
combination from the actual Möbius/prime arithmetic. Repeating the established
inversion, diagonal bound, or small-divisor estimate would not advance it.

## Verification

From `formal/`, the focused command
`lake --old env lean /tmp/wl-critical-source-audit-2026-10-24.lean`
exited 0. It checked the full types and printed transitive axioms of:

- `RHTower.ccmPrimeDeficitCriticalEnergy_prime_work_balance`
- `RHTower.ccmLogChebyshevDeficitPrimitive_scale_descent`
- `RHTower.abs_ccmLogChebyshevDeficitPrimitive_sub_moebius_tail_le`
- `RHTower.ccmLogChebyshevDeficitPrimitive_sub_eulerAction_halfLog_balance`
- `RHTower.selberg_symmetry_formula`

Each reported exactly `{propext, Classical.choice, Quot.sound}`. These certify
the existing identities and bounds only; they do not certify the missing
critical cancellation or RH. No repository Lean source or umbrella was added
or edited by this pass.

Final direct source audit:
`lake --old env lean GaloisForLFunctions/RHTower/CCM/CCMPrimeDeficitMobiusTailLocalization.lean`
exited 0 with empty output. The five inspected source files and both route
reports remain unchanged. The owned temporary audit file was removed.
