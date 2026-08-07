# Mass–Xi balanced adjacent-prime difference ideal

## Status

- Lane: `3-formalized`
- Conjecture: `C38`
- Result: `[LEAN-PROVED] [BOUNDED-IDEAL ENLARGED] [SCALAR CLASS SURVIVES] [NOT RH]`
- Parent: C37 integer-dilation prime-mask ideal
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core

## Exact conjecture

Write `p_n` for the increasing prime enumeration,

```text
t_n = LSeries.term(vonMangoldt, 1/2, p_n),
F_{a,τ}(λ) = stripFourier(xiMassAnalyticTest(a,τ), λ),
A_n(a,τ) = t_n F_{a,τ}(log p_n).
```

Define the balanced adjacent-pair atom

```text
B_n(a,τ) = (t_{2n+1}/t_{2n}) A_{2n}(a,τ) - A_{2n+1}(a,τ).
```

Since every prime critical coefficient is nonzero, the coefficient balance is exact:

```text
B_n(a,τ)
  = t_{2n+1}
      (F_{a,τ}(log p_{2n}) - F_{a,τ}(log p_{2n+1})).
```

**C38.** For every `a>0` and positive vertical time line `Re τ=σ>0`, the sequence
`B_n(a,τ)` is absolutely summable and its sum is uniformly bounded in `Im τ`.

## Attack

### A. Uniform frequency Lipschitz law

For real frequencies `v,w`, prove unconditionally

```text
‖F_{a,σ+iu}(v) - F_{a,σ+iu}(w)‖
  ≤ |v-w| ∫_ℝ |x| exp(-σ|x|) dx.
```

This follows inside the actual Fourier integral from

```text
‖exp(-ivx)-exp(-iwx)‖ ≤ |v-w| |x|
```

and `‖xiMassAnalyticTest(a,σ+iu,x)‖ ≤ exp(-σ|x|)`.  No derivative exchange or
frequency asymptotic is needed.

### B. Exponential-potential coboundary

Put `λ_n=log p_n` and `E_n=exp(-λ_n/4)`.  For `x≤y`, prove

```text
y exp(-y/2) (y-x)
  ≤ 16 (exp(-x/4)-exp(-y/4)).
```

The first factor obeys `y exp(-y/2) ≤ 4 exp(-y/4)` by `y/4≤exp(y/4)`;
the remaining inequality is `exp((y-x)/4)-1≥(y-x)/4`.  Strict prime
monotonicity then gives

```text
‖B_n(a,σ+iu)‖
  ≤ 16 J₁(σ) (E_{2n}-E_{2n+1})
  ≤ 16 J₁(σ) (E_{2n}-E_{2n+2}),
J₁(σ)=∫_ℝ |x| exp(-σ|x|) dx.
```

The last majorant telescopes exactly.  Hence its partial sums are at most `E_0`, proving
absolute summability without PNT, Bertrand, or any prime-gap estimate.

### C. Quotient target

Reverse-normalize the pair sequence and package it as an actual bounded prime mask

```text
v_adj(p_{2n})   = 1,
v_adj(p_{2n+1}) = -t_{2n}/t_{2n+1}.
```

Prove its masked layer equals `∑' n, B_n`, is uniformly bounded, and classify

```text
w = c + b w_adj + critical-ℓ¹ residual
```

by an exact decomposition.  The `c=0` class must be unconditionally bounded; every `c≠0`
class must be equivalent to the valuation-one bound and hence RH.

## Falsification gates

1. Exact algebraic identity and telescoping majorant must be proved symbolically; no numerical
   evidence is accepted.
2. Lean must prove Fourier Lipschitz with the actual integral definition and no new assumptions.
3. Lean must prove absolute summability from the ordered-prime enumeration without importing PNT.
4. The adjacent mask must be structurally outside finite Euler-power dilation: it couples two
   distinct prime-log frequencies rather than transporting one prime to one power.
5. If the quotient merely rephrases critical `ℓ¹`, prove that collapse and retire C38; do not keep
   a renamed bounded source.

## Higher-principle conjecture

C31–C37 show vertical Euler valuations form a bounded dilation ideal, leaving one primitive
scalar class.  C38 tests whether the next invisible directions are **frequency coboundaries**:
cofinal masks whose coefficient balance converts atoms into discrete differences of a uniformly
regular Fourier profile.  The apparent prime-gap obstacle may be a shadow of a universal rule:

```text
ordered spectral differences × decaying critical mass
  = summable coboundary of a slower exponential potential.
```

If true, open-core quotient is controlled not only by coefficient decay but by a first discrete
cohomology: dilation boundaries and ordered-frequency coboundaries vanish, while primitive scalar
mass survives.

## Novelty audit

- Existing C35–C37 modules treat critical `ℓ¹` deviations and finite Euler-power dilation orbits;
  neither couples distinct primes.
- `sonin-two-particle-prime-coherence.md` uses adjacent prime pairs in a different Sonin/Calkin
  operator construction.  It contains neither the balanced Xi atom identity nor the exponential
  potential telescope above.
- Corpus search found no strip-Fourier frequency-Lipschitz theorem for the mass test and no actual
  ordered-prime masked-layer theorem of this form.
- Novelty remains provisional until exact Lean theorem and broader internal-source audit pass.

## Lean targets

- `XiMassStripFourierLipschitz.lean` — proved: actual integral frequency-Lipschitz law, uniform in
  vertical height
- `XiMassAdjacentPrimeDifference.lean`
- `XiMassAdjacentPrimeMask.lean`
- `XiMassAdjacentPrimeQuotient.lean`

All proofs must be unconditional; final capstones must expose only standard quotient/classical
axioms under `#print axioms`.

## Log

- 2026-08-06 — opened from C37 phase-transition survivor; exact conjecture and fail gates fixed.
- 2026-08-06 — C38-A formalized as
  `norm_stripFourier_xiMassAnalyticTest_sub_le`; proof acts directly on the integral.
- 2026-08-07 — C38-B formalized: balanced adjacent atoms are absolutely summable with an exact
  quarter-exponential telescope and a vertical-height-independent bound.
- 2026-08-07 — C38-C formalized. Bertrand bounds the reverse-normalized actual mask by `2`; Lean
  proves exact flattening of paired atoms back to the prime layer and the `32 J_sigma E_0` bound.
- 2026-08-07 — Exact quotient classification formalized: adjoining the adjacent-prime direction
  preserves fixed-line boundedness and leaves the scalar valuation-one class, hence the RH open
  core, unchanged. C38 closes as a positive bounded-ideal survivor plus a sharp no-go.
