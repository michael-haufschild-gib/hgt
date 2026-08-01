# Stationary point-spectrum scaling law

- **ID:** `stationary-point-spectrum-scaling-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / UNIVERSAL STATIONARY RECURRENCE DECOMPOSITION
- **Parent:** `time-return-duality-law`
- **Target paper:** `universal-quantum-recurrence-anatomy`
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [NOVELTY AUDIT OPEN]`

## Question

For an arbitrary probability energy law, does the continuous spectral
sector merely have zero mean return, or does it disappear from the complete
stationary return distribution?

## Candidate exact law

Let

\[
 A_\mu=\{E:\mu(\{E\})>0\},\qquad
 \mu_{\rm pp}=\mu|_{A_\mu},\qquad
 p_{\rm pp}=\mu_{\rm pp}(\mathbb R).
\]

If `p_pp > 0`, let `alpha_pp = mu_pp / p_pp`.  For the canonical
centered-time stationary survival-fidelity law `R_infty`, one has

\[
 \boxed{
 R_\infty(\mu)
 = (x\mapsto p_{\rm pp}^2x)_*R_\infty(\alpha_{\rm pp}).
 }
 \tag{PS}
\]

If `p_pp = 0`, then `R_infty(mu) = delta_0`.

Equivalent all-order form:

\[
 \int x^n\,dR_\infty(\mu)
 =p_{\rm pp}^{2n}
   \int x^n\,dR_\infty(\alpha_{\rm pp})
 \qquad(n\ge 0).
\]

Thus every absolutely continuous and singular-continuous component is
absent from every stationary return statistic.  It survives only through
the missing total point-spectrum weight, which contracts fidelity by
`p_pp^2`.

## Proof route

1. The atom set of every finite real measure is countable.
2. Restriction to that atom set has exactly the same singleton masses as
   the original measure.
3. Singleton masses of difference measures and all convolution powers
   depend only on singleton masses of the factors.
4. Normalizing the restricted finite measure by mass `p_pp` scales its
   difference measure by `p_pp^2`, hence its `n`-fold collision mass by
   `p_pp^(2n)`.
5. Stationary recurrence moments are exactly those zero-collision masses.
6. Moment determinacy on `[0,1]` identifies the complete pushforward law.

## Why this is stronger than the present paper

The draft states only the atomless endpoint and a forward same-point-mass
invariance.  `(PS)` is an exact decomposition for every mixed spectrum.  It
turns the arbitrary-spectrum branch into one law: stationary recurrence is
the normalized pure-point return law with one universal amplitude scale.

## Hostile boundaries

1. This is a stationary centered-time distribution theorem, not pointwise
   decay of the continuous spectral amplitude.
2. It does not identify the original spectrum from return data; survival
   recurrence sees only the energy-difference quotient.
3. It does not say continuous spectrum is physically absent.  It says that
   it contributes no completed-time survival-fidelity statistic.
4. External priority must be checked against Wiener, RAGE, spectral
   decomposition and almost-periodic quantum recurrence literature.

## Gates

- [x] exact candidate statement
- [x] dependency-closed proof route
- [x] paper proof
- [x] Lean formalization
- [x] axiom audit
- [ ] external priority audit
- [ ] hostile Nature significance review

## Formal verification

- Module:
  `formal/GaloisForLFunctions/RHTower/StationaryRecurrencePointSpectrumScalingLaw.lean`
- Capstone:
  `stationarySpectralReturnProbabilityMeasure_eq_scaledPointSpectrum`
- Direct foreground check:
  `lake env lean GaloisForLFunctions/RHTower/StationaryRecurrencePointSpectrumScalingLaw.lean`
- Axiom audit of the point-mass restriction, convolution scaling, moment scaling,
  and probability-law identity uses only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Umbrella import: `GaloisForLFunctions.RHTower`.
