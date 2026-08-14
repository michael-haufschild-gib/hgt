# Selberg analytic-continuation uniqueness

- **ID:** `selberg-analytic-continuation-uniqueness`
- **Status:** Stage 3 — formalized in Lean 4
- **Novelty:** `[LITERATURE]` analytic infrastructure; not new scientific knowledge
- **Lean module:** `GaloisForLFunctions.RHTower.SelbergClass.AnalyticUniqueness`

## Exact theorem

If two pole-safe Selberg analytic continuations agree for every `s` with `Re(s)>1`, their represented
meromorphic values agree on the codiscrete filter.  Consequently, two exact `S♯` data with identical
arithmetic coefficients represent the same meromorphic function.

## Proof

For continuations `H₁(s)/(s-1)^m` and `H₂(s)/(s-1)^n`, agreement on the right half-plane gives

`H₁(s)(s-1)^n = H₂(s)(s-1)^m`.

Both sides are entire.  The analytic identity principle makes this equality global.  Cancelling the
powers away from `s=1` gives codiscrete equality, with no assertion about a totalized pole value.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/SelbergClass/AnalyticUniqueness.lean`: passed
- named module olean build: passed
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only
- umbrella import added; umbrella build deliberately not run
