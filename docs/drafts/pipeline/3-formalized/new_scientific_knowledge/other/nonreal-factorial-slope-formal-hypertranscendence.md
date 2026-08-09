# Nonreal factorial slope forces formal hypertranscendence — formalization certificate

- **ID:** `nonreal-factorial-slope-formal-hypertranscendence`
- **Stage:** 3-formalized
- **Paper proof:**
  `../../../2-fully-proven/new_scientific_knowledge/other/nonreal-factorial-slope-formal-hypertranscendence.md`
- **Capstone module:** `formal/GaloisForLFunctions/HTGeometry/NonrealFactorialSlopeHT.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`

## Closed formal theorem

```text
GaloisForLFunctions.HTGeometry.aeval_formalJets_ne_zero
```

```lean
theorem aeval_formalJets_ne_zero (hyp : FactorialSlope a α Λ Cc c) (him : α.im ≠ 0)
    (m : ℕ) (P : MvPolynomial (Fin (m + 2)) ℂ) (hP : P ≠ 0) :
    aeval (formalJetsOver m (PowerSeries.mk a)) P ≠ 0
```

A formal power series whose coefficients follow a factorial ray of **nonreal** slope satisfies no
nonzero algebraic differential equation over `ℂ(z)`.  The `MvPolynomial (Fin (m+2)) ℂ` form is the
card's conclusion after clearing a rational denominator and a power of `z`: the slots are the
variable and the jets `F, F', …, F^{(m)}`.

`FactorialSlope a α Λ Cc c` is the card's hypothesis `(2)` — the defining property of the class of
series considered (`0 < Re α`, `Cc ≠ 0`, `Λ ≠ 0`, `0 < c`, and the exponentially small relative
approximation of `a n` by `Cc·Λⁿ·Γ(1 + αn)`).  It is not an unproved analytic input: no analytic
hypothesis is assumed anywhere in the chain.

`#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]`.

## Supporting layer

All twenty-five modules are present, umbrella-wired, and free of `sorry`, `admit`, added `axiom`,
`opaque`, and `unsafe`:

```text
DigammaHalfPlaneAsymptotic      GammaComplexShiftIntegral     GammaRayShiftAsymptotic
GammaRayRealEnvelope            FactorialRayEnvelope          FactorialCompositionBound
TruncatedJetCoeffBound          FactorialSlopeCoeffRatio      PowerSeriesJetCoeff
ChirpSumIndependence            EndpointChirpGlue             EndpointChirpTerm
FactorialSlopeEnvelope          FacEnvShiftBound              RemainderRatioVanishing
EndpointJetSum                  EndpointChirpData             NormalisedEndpointIdentity
JetCoeffEnvelope                UnivariateShadow              JetFreeNonvanishing
JetsEnvelope                    EndpointRemainderBound        NonrealFactorialSlopeHT
PolynomialShiftHT
```

The proof needs no Stirling series: the two-sided envelope `‖Γ(1+αn)‖ ≍ n^{±B}(n!)^r Λⁿ` with a
fixed polynomial weight is enough, because the endpoint lemma absorbs polynomial factors into its
exponent.  The entropy core is the elementary binomial inequality
`(∏ nᵢ!)·M^R ≤ 2^R·R!·M!`, and the transcendence input is chirp independence: the endpoint sum is a
finite combination `∑ Aᵢ N^{ρᵢ} e^{i t kᵢ log N} εᵢ(N)` whose normalised limit forces every
top-layer coefficient to vanish — which is where `Im α ≠ 0` enters, and the only place it does.
