# Mass–Xi universal Euler-valuation quotient

## Status

- Lane: `3-formalized`
- Conjecture: `C34-D` proved; `C34-A` and `C34-C` retired
- Parent: C33 valuation-one prime quotient
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core

## Hard core

For

```text
S₁(a,τ) = ∑' p, xiMassCenteredPrimeAtom a τ p,
```

prove a uniform vertical bound at one `a>1/2`, `σ>0` without importing any equivalent trace,
zero-displacement, or RH hypothesis.

## Conjecture loop

### C34-A — primitive Euler Möbius inversion

For `Re s>1`, prove the exact identity

```text
PrimeLog(s) = ∑' k≥1, μ(k) infinitePrimeFlux(k s).
```

Then transport it through the analytic mass integral. Audit whether all `k≥2` terms form a
bounded ideal/residue family, leaving a new regularized `k=1` object with better structure than the
original prime sum.

### C34-B — fail criterion

If the `k=1` term is exactly the full zeta logarithmic derivative on the critical half-plane and
its required bound is equivalent to C33/RH, retire the route. Extract the strongest positive
survivor: exact valuation Möbius decomposition, classification of all `k≥2` terms, and the precise
singular support that prevents bounded continuation.

### C34-C — universal reinterpretation

Test whether corpus QEC/quantum/Hilbert structures turn the Möbius coefficients into an orthogonal
or unitary primitive projector. The required theorem must transfer to `S₁`; finite-dimensional
or algorithmic cancellation without a dependency-closed analytic bridge is failure/theatre.

### C34-D — one-dimensional valuation quotient

For every bounded complex valuation mask `b(r)`, define the filtered centered source by weighting
every prime-power atom `p^r` by `b(r)`. Prove:

```text
b(1)=0  → filtered source is uniformly vertically bounded;
b(1)≠0  → (filtered fixed-line boundedness ↔ RH).
```

This is the positive survivor forced by C34-A's failure. It would classify every bounded
valuation-only Möbius, parity, finite-difference, or dilation projector at once: non-primitive
Euler manipulation cannot weaken the hard core unless it deletes the primitive prime channel.

## Research rules

- Search formal corpus and failed cards before proving any reusable identity.
- Every conjecture must end in a Lean theorem or an explicit retired no-go with positive survivor.
- No absolute envelope already ruled out by C28.
- No zero-side equivalent bound may be used as source input.

## Result `[LEAN-PROVED]`

Let `b : ℕ → ℂ` be any bounded valuation mask, with `‖b r‖ ≤ L`, and put

```text
F_b(a,τ)
  = b(1) S₁(a,τ) + b(2) S₂(a,τ)
    + ∑' (p,k), b(k+3) A_{p^(k+3)}(a,τ).
```

Lean proves the exact dichotomy on every fixed positive vertical line:

```text
b(1) = 0  → F_b is uniformly vertically bounded;
b(1) ≠ 0  → (F_b is uniformly vertically bounded ↔ S₁ is uniformly vertically bounded).
```

Consequently, for every legal mass parameter and every `b(1) ≠ 0`,

```text
RiemannHypothesis ↔ XiMassValuationFilteredLineBound b a σ.
```

Thus bounded valuation filters modulo uniformly vertically bounded sources form a
one-dimensional quotient, with quotient coordinate `b(1)`.  Every non-primitive valuation is in
the bounded ideal.  No bounded Möbius, parity, finite-difference, or dilation mask can weaken the
open core while retaining valuation one.

## Conjecture audit

- `C34-A` failed as a closure mechanism.  Möbius inversion reconstructs the primitive prime
  channel, but its `k=1` term is the same critical logarithmic-derivative wall already equivalent
  to C33/RH.  Existing failed-route cards independently record this obstruction.
- `C34-C` failed as an analytic bridge.  QEC/Quantum finite purity supplies finite-dimensional
  unitary cancellation but no dependency-closed theorem controlling the infinite critical prime
  source.  Importing such cancellation would merely rename the open bound.
- `C34-D` is the positive survivor and strictly strengthens C33: it classifies all bounded
  valuation-only projectors, not only the literal von-Mangoldt mask.

## Lean declarations

- `RHTower.norm_xiMassValuationFilteredHighTail_vertical_le`
- `RHTower.exists_norm_xiMassValuationFilteredNonPrimitive_vertical_bound`
- `RHTower.xiMassValuationFilteredLineBound_of_depthOne_eq_zero`
- `RHTower.xiMassValuationFilteredLineBound_iff_valuationOne`
- `RHTower.riemannHypothesis_iff_xiMassValuationFilteredLineBound`

Source:
`formal/GaloisForLFunctions/RHTower/XiMassValuationFilterQuotient.lean`.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/XiMassValuationFilterQuotient.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.XiMassValuationFilterQuotient`: pass (`9476/9476`).
- Capstone axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, project axiom, `opaque`, or `unsafe` declaration.

## Log

- 2026-08-05 — opened after exact C33 reduction.
- 2026-08-05 — raw Möbius/log-derivative and finite QEC-purity closures failed the dependency audit.
- 2026-08-05 — extracted and formalized universal one-dimensional valuation quotient; promoted to
  `3-formalized`.
