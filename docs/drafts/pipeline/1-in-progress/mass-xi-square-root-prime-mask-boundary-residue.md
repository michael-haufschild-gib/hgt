# Mass–Xi square-root prime-mask boundary residue

## Status

- Lane: `1-in-progress`
- Conjecture: `C36`
- Parent: C35 critical `ℓ¹` prime-mask quotient
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core

## Hard conjecture

Define the cofinal horizontal mask layer

```text
T(a,τ) = ∑' p, (p : ℝ)^(-1/2) * xiMassCenteredPrimeAtom a τ p.
```

Its coefficient is `log(p)/p`, so its absolute critical-prime envelope diverges and C35 does not
apply.  Unlike the valuation-two layer, its Fourier frequency remains `log p`.

### C36-A — natural boundary reassembly

For every `0<d<a`, prove

```text
T(a,τ) = ∫ x, xiMassBottomTest a d τ x * xiPrimeLogDirichlet (1+d+ix).
```

### C36-B — adaptive boundary residue

Use

```text
Q(s) = (s-1)⁻¹ + zetaLogDerivReg(s) - xiPrimeLogHigherValuation(s)
```

on the adaptive depth `d(u)=min(a/2,1/(1+|u|))`.  Prove the pole identity

```text
∫ x, g(x-id) * (d+ix)⁻¹ = π * g(0)
```

and absorb the regular polynomial response by mass decay.  Conclude `T(a,σ+iu)` is uniformly
bounded for every `a,σ>0`.

### C36-C — enlarged horizontal quotient

Combine C35 with C36.  If

```text
w(p) = c + d / sqrt(p) + r(p),
∑ p ‖r(p)‖ log(p)/sqrt(p) < ∞,
```

then the `c=0` source is bounded and every `c≠0` masked source is RH-equivalent.

## Fail criteria

- If the natural-line series cannot be reassembled unconditionally, identify exact missing
  summability theorem.
- If the regular response picks up an uncancelled `d(u)⁻¹` loss, retire and extract exact pole law.
- No use of any bound equivalent to C33/RH.

## Novelty audit

Corpus has the valuation-two boundary residue at frequency `2 log p`, but no theorem for the
horizontal square-root prime mask at frequency `log p`.  C36 would prove first explicit cofinal,
non-critical-`ℓ¹` prime-mask direction belongs to the bounded ideal.

## Log

- 2026-08-05 — opened after C35 isolated the critical `ℓ¹` horizontal ideal.
