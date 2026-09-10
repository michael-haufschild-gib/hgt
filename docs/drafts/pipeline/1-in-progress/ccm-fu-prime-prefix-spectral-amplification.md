# CCM-FU: prime-prefix spectral amplification

- **ID:** `ccm-fu-prime-prefix-spectral-amplification`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / source growth estimate
- **Status:** Unproved candidate, not selected for further formalization. Existing source theorems already exclude the intended increasing-order ceiling. No new route retired.
- **Goal chain:** Actual divisor source → bounded cutoff-dependent signed energy → bounded normalized Abel head → CCM-FU → RH.

## Question

Can a bound uniform in the processed prime core be obtained by bounding its
normalized Mellin product? Test the concrete increasing prime prefix, retaining
the squarefree density. This is a source calculation, not a numerical experiment.

For a finite prime core P, define

```text
E_P(s) = product_(p in P) (1 - p^(1/2-s)),
L_P(t) = product_(p in P) [1 - 2 sqrt(p)/(p+1) cos(t log p)].
```

The existing Mellin formula implies the elementary identity

```text
L_P(t) = product_(p in P) [p/(p+1)] * |E_P(1+it)|².
```

All factors are positive, but their mass against the literal unit-head Mellin
weight still needs control. The density cannot be omitted: it changes with P.

## Candidate quantitative bound

Let `P_N` contain every prime at most `N^4`, and consider the full interval

```text
pi/(4 log N) <= t <= pi/(3 log N),       N > 1.
```

For every prime `N^3 < p <= N^4`, the phase lies in
`[3*pi/4, 4*pi/3]`, so its cosine is at most `-1/2`. With
`a_p=2 sqrt(p)/(p+1)`, elementary inequalities give

```text
1/sqrt(p) <= a_p <= 2/sqrt(p),  a_p <= 19/20,
log(1-a_p*cos(t*log(p))) >= -40/sqrt(p)       for every real t,
log(1-a_p*cos(t*log(p))) >= 1/(4*N²)         on the large-prime band.
```

Summing the first bound over all integers through `N^3` bounds the possible
small-prime loss by `80*N^(3/2)`. A proved prime-count lower bound on
`(N^3,N^4]` should therefore give a constant `c>0` and, eventually, uniformly
throughout the displayed t interval,

```text
log L_(P_N)(t) >= c*N²/log N - 80*N^(3/2).
```

The right side tends to positive infinity. The interval has length
`pi/(12 log N)`. Any continuous weight positive at zero consequently has
diverging weighted mass on this shrinking interval. For the actual unit head,
the required positivity must be obtained from its proved positive source moment
and the exact physical Mellin identity.

## Proof obligations

1. Check the factor estimates and cosine interval in Lean without numerical evidence.
2. Derive the prime-band count from the actual corpus PNT/counting theorem.
3. Prove the uniform product lower bound and its shrinking-interval mass consequence.
4. Identify the literal unit-head spectral weight and its positive value at zero.
5. Relate the full weighted product mass to the existing fixed-core coefficient
   `kappa_P`; the fixed-core energy card still marks this one-head integral
   identification as an optional unformalized step. Do not assume it.
6. Only then assess the precise consequence for a single increasing prime order
   used at every physical cutoff. Orders depending on the cutoff are a separate
   question and are not excluded by this candidate.

## Positive survivor sought

The quantitative source statement is a full shrinking frequency band with a
specified amplification rate and retained density. This would identify where
the growing-core mass sits, rather than merely negate a uniform estimate.
The original finite-cutoff energy remains the intended target; a fixed-core
limit cannot replace that joint problem.

## Evidence and scope

Prior research already proves terminal-block resonance on
`[pi/log y, 4*pi/(3*log y)]`, together with an exact positive-weight interval
lower bound, in `MobiusCriticalPrimeBlockGammaBand.lean`.
`MobiusCriticalPrimeBlockResonance.lean` also supplies the terminal-window
Chebyshev cardinality budget. Thus the band mechanism itself is already in
the corpus. The additional assertion here would have to pay every earlier
prime factor and retain the changing squarefree density before identifying
the literal fixed-core energy.

More decisively, the [actual increasing-order obstruction](../5-failed/ccm-fu-prime-pair-energy.md)
already excludes every fixed original-diagonal ceiling in increasing prime
order; its [source head asymptotic](../3-formalized/ccm-fu-late-prime-head-asymptotic.md)
is formal. The proposed spectral calculation is therefore not a new proof
of that route obstruction. Its possible additional content is localization
of growing-core mass, not closure of the adaptive source estimate. No further
Lean work on this candidate is justified merely to reprove that obstruction.

Source definitions and identities inspected in `DivisorContinuousHeadMellin`,
`DivisorCoreMellinBoundary`, `MobiusDivisorDilationMean`,
`MobiusDivisorFixedCoreEnergyLimit`, and `EulerTransitionSelector`.
The algebraic normalization and the analytic plan above have not yet been
certified as a new Lean theorem. No computational experiment is appropriate:
the proposed effect follows from the displayed inequalities if those obligations
close. The frontier map remains read only.
