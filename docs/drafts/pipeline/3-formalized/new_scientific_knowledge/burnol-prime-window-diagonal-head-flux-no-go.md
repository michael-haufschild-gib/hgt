# Burnol ordinary-prime diagonal head-flux no-go

- **ID:** `burnol-prime-window-diagonal-head-flux-no-go`
- **Stage:** 3 — formalized
- **Type:** THEOREM (Lean) / POSITIVE-SIGN NO-GO
- **Route:** R
- **Scientific status:** `[LEAN-PROVED] [NO-GO CLOSED] [NOT RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/BurnolPrimeWindowDiagonalHeadFluxNoGo.lean`

## Statement

For an ordinary prime `p` and the source window `[1/p,1]`, define

```text
J_p(rho) = (p-1)^2 |1-rho|^-2 - (log p)^2 |rho|^-2.
```

If `1/2 < Re rho < 1`, then `J_p(rho)>0` for every prime `p`. Every nonempty finite sum

```text
sum_p w_p J_p(rho),        w_p>0,
```

is therefore strictly positive. This remains true when `rho` is a hypothetical right-half Xi
divisor.

Principal Lean theorems:

```text
burnolPrimeWindowDiagonalHeadFlux_pos
burnolPrimeWindowDiagonalHeadFlux_finset_sum_pos
xiDivisor_burnolPrimeWindowDiagonalHeadFlux_pos
```

## Dependency-closed paper proof `[PROVED HERE]`

In the open right half-strip, `|1-rho|<|rho|`, hence
`|rho|^-1<|1-rho|^-1`. For every prime, `1<p` and strict logarithmic convexity gives
`0<log p<p-1`. Therefore

```text
(log p)|rho|^-1 < (p-1)|1-rho|^-1.
```

Both sides are nonnegative, so squaring yields `J_p(rho)>0`. Strict positivity is preserved by
every nonempty finite combination with positive weights.

## No-go closure

- **Exact killing mechanism:** every ordinary-prime diagonal channel already has the same strict
  positive orientation as the dyadic obstruction.
- **Strongest positive survivor:** prime-uniform strict sign and finite positive-cone stability.
- **New insight:** adding primes with positive diagonal weights cannot create the required
  nonpositive pre-polar current.
- **Exact frontier:** surviving producers must contain signed off-diagonal coupling or a singular
  domain-admission law. No annihilation theorem is asserted.

## Gates and verification

- [x] complete paper proof
- [x] unconditional Lean sign theorem and finite-sum corollary
- [x] wired into `RHTower.lean`
- [x] direct `lake env lean` check
- [ ] final targeted `lake build` and axiom audit (recorded at session close)

## Log

- 2026-08-11 — paper proof extracted from Route-R heavy-loop conjecture C3.
- 2026-08-11 — formalized and promoted to stage 3.
