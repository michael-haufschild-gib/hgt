# CCM first-clock asymptotic Bohr Torelli law

- **ID:** `ccm-first-clock-asymptotic-bohr-torelli`
- **Stage:** `3-formalized/needs-audit`
- **Type:** THEOREM / source-side multiplicity-exact spectral reconstruction
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [AXIOM-AUDITED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `ccm-first-clock-asymptotic-bohr-completeness.md`
- **HT reservoir used:** `BohrMeanInvariance`, `BohrDerivativeSpectrum`,
  `SummableSpectrumScrewAlmostPeriodic`, and the `AP ∩ C₀ = {0}` rigidity mechanism

## Exact theorem

Put

```text
F(L) = L * ccmPublishedSourceSineCoefficient(L/2, 2*pi/L).
```

Suppose `P : R -> R` is continuous, Bohr almost periodic, and

```text
F(L) - P(L) -> 0  as L -> +infinity.                       (ABP)
```

Then:

1. `P` is the unique continuous Bohr almost-periodic asymptote of `F`;
2. `(ABP)` forces RH;
3. `P(L)=2*sum_q (1-cos(gamma_q L))/gamma_q^2`, with
   `gamma_q=Re(xiSpectralPoint(q))`;
4. for every nonzero real `lambda`,

```text
a_P(lambda) = -N(|lambda|)/lambda^2,                       (T)
```

   where `a_P(lambda)` is the complex Bohr coefficient and `N(|lambda|)` is the exact number of
   Xi divisor copies satisfying `|gamma_q|=|lambda|`;
5. equivalently,

```text
-lambda^2 * a_P(lambda) = N(|lambda|).                     (R)
```

Thus the literal source asymptote recovers the multiplicity-bearing absolute Xi spectrum. Since
the centered Xi divisor is reflection invariant, this determines its full real divisor under RH.
No simplicity or rational-independence assumption occurs.

## Paper proof

### Uniqueness

If `P` and `Q` are two asymptotes, then `P-Q -> 0` at positive infinity. Their difference is Bohr
almost periodic. A nonzero Bohr almost-periodic function has relatively dense approximate return
times, contradicting decay at positive infinity. Hence `P=Q`.

### Identification

Existence of `P` is the source-only asymptotic-Bohr property already proved equivalent to RH.
Under RH the explicit critical screw series `2*S` is an asymptote. Uniqueness gives `P=2*S`.

### Coefficient extraction

One atom has the character decomposition

```text
a(1-cos(omega*t))
  = a - (a/2) exp(i*omega*t) - (a/2) exp(-i*omega*t).
```

Therefore its coefficient at `lambda` is

```text
[lambda=0]a - [omega=lambda]a/2 - [-omega=lambda]a/2.
```

Finite partial sums obey this formula exactly. Nonnegative summability bounds the uniform tail by
`2*sum_tail a`, while the Bohr coefficient functional is 1-Lipschitz in uniform norm. Passing to
the finite-subset limit proves termwise extraction for the complete screw series without any
frequency-separation premise.

For `lambda != 0`, the zero-frequency term vanishes. Each divisor copy with
`gamma_q=lambda` or `-gamma_q=lambda` contributes exactly `-1/lambda^2`; all other copies
contribute zero. RH makes this fibre finite because it is contained in the union of the two finite
complex Xi spectral fibres at `lambda` and `-lambda`. Summation gives `(T)` and `(R)`.

## Hostile audit

1. **Is `AP + C₀` uniqueness new?** No. It is classical and already latent in HTGeometry. It is
   infrastructure, not novelty claim.
2. **Do ordinate collisions destroy recovery?** No. Colliding copies add, and `XiZeroCopy`
   preserves analytic multiplicity exactly.
3. **Does cosine lose the sign?** Yes, deliberately: it recovers the absolute fibre. Xi's centered
   divisor is even, so this loses no divisor information on RH.
4. **Can `lambda=0` corrupt quantization?** Excluded in `(T)`; under RH every Xi spectral ordinate
   is nonzero anyway.
5. **Does this prove RH?** No. Existence of the asymptote is already equivalent to RH. This theorem
   reconstructs the divisor from that source-side object; it does not produce the object
   unconditionally.
6. **Prior-art collision:** generic termwise Fourier/Bohr extraction is classical. Primary Suzuki
   and Matsumoto--Suzuki screw-function papers audited so far do not state the literal CCM-source
   asymptote uniqueness plus multiplicity-quantized Torelli law. Keep novelty unverified pending
   expert review.

## Lean certificate

Generic module:

```text
formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewBohrCoefficients.lean
```

Capstones:

```text
bohrCoefficient_complex_screwSeries
eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
asymptoticBohrModel_unique
```

Xi/source module:

```text
formal/GaloisForLFunctions/RHTower/CCMFirstClockAsymptoticBohrTorelli.lean
```

Capstones:

```text
ccmFirstClockAsymptoticBohrModel_eq_explicitScrew
bohrCoefficient_ccmFirstClockAsymptoticBohrModel_eq_multiplicity
ccmFirstClockAsymptoticBohrModel_recovers_absoluteMultiplicity
```

Both theorem-area umbrellas import the modules. Green audit:

```text
lake env lean GaloisForLFunctions/HTGeometry/SummableSpectrumScrewBohrCoefficients.lean
lake env lean GaloisForLFunctions/RHTower/CCMFirstClockAsymptoticBohrTorelli.lean
lake build GaloisForLFunctions.RHTower.CCMFirstClockAsymptoticBohrTorelli
lake env lean /tmp/ccm_abt_axioms.lean
```

Final build: `9334/9334`, success. All six audited generic/source capstones depend exactly on

```text
[propext, Classical.choice, Quot.sound]
```

`scripts/formal_tools.py lint` reports no forbidden declarations. It remains red only on six
unrelated pre-existing HTGeometry umbrella-reachability failures; both new modules are reachable.

## Frontier consequence

The asymptote is no longer merely an RH-equivalent bounded object: it is a canonical spectral
coordinate system for the full Xi divisor. Remaining RH-producing problem is sharply source-side:
construct this asymptote, or enough of its quantized coefficient law, directly from the published
prime/Gamma source without assuming a zero-location theorem.

## Log

- 2026-08-01 — Whole-corpus HT audit isolated uniform Bohr coefficient continuity and
  `AP ∩ C₀` rigidity as previously unapplied source-side tools.
- 2026-08-01 — Paper proof closed after collision, zero-frequency, and prior-art hostile tests.
- 2026-08-01 — Generic coefficient theorem and multiplicity-exact CCM specialization formalized.
