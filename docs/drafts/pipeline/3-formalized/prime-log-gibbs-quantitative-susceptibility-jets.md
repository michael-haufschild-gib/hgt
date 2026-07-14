# Prime-log Gibbs quantitative susceptibility jets

- **ID:** `prime-log-gibbs-quantitative-susceptibility-jets`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[BRIDGE]`
- **Source:** Gapped low-temperature Lehmann response and spectral response sum rules; Essler--Konik, arXiv:0907.0779; Bradlyn--Abbamonte, arXiv:2404.16144
- **Statement:** Every holomorphic susceptibility jet of the exact finite Hermitian prime-log Gibbs response has a subsystem-independent Boltzmann error bound on each upper strip, and the entire jet family converges locally uniformly in the simultaneous cold/thermodynamic limit.

## Goal

Strengthen the qualitative compact-open Gibbs limit into an explicit all-order value estimate that finite-order analytic consumers can use directly.  The target must control the exact Hermitian KMS response, not only the directed carrier, and must retain the genuine product filter on finite prime subsystems and inverse temperature.

## Candidate relation

For `eta > 0`, `eta <= Im z`, derivative order `m`, and `beta >= 0`, prove

```text
norm (D^m G_(P,beta)(z) - D^m H_P(z))
  <= m! * exp (-beta * log 2) * eta^(-(m+1)) * M(u).
```

The Lehmann mirror term is a finite sum of resolvents at negative prime-log energies.  Its `m`th derivative is exactly `(-1)^m m!` times the `(m+1)`st resolvent power.  Causality gives `norm (log p + z)^(-1) <= eta^(-1)`, while the subsystem-independent gap gives `exp(-beta log p) <= exp(-beta log 2)`.

## Intended corpus consumers

- the exact finite Hermitian Gibbs response via its proved carrier identity;
- the prime-log Cauchy-jet packet through the finite directed carrier;
- locally uniform convergence of every iterated derivative, strengthening the existing pointwise jet-return theorem;
- the universal prime orientation and canonical constraint-orientation specializations.

## Gates

- [x] 0 -> 1: exact source-pure identity and direct consumer identified
- [x] 1 -> 2: paper proof complete
- [x] 2 -> 3: Lean theorem, target/full builds, axiom audit, lint

## Proof

`[PROVED HERE]` For a real frequency `t` and `Im z > 0`, repeated differentiation gives

```text
D^m (t + z)^(-1) = (-1)^m m! (t + z)^(-(m+1)).
```

Subtracting the finite directed carrier from the finite Hermitian Gibbs carrier leaves exactly the negative-frequency Lehmann mirror sum.  Termwise differentiation is valid because the sum is finite and every pole is real.  Therefore

```text
D^m (G_(P,beta) - H_P)(z)
  = -(-1)^m m! * sum_(p in P)
      w_p exp(-beta log p) (log p + z)^(-(m+1)).
```

On `eta <= Im z`, the causal resolvent estimate gives `norm (log p + z)^(-1) <= eta^(-1)`.  For `beta >= 0`, the uniform prime gap gives `exp(-beta log p) <= exp(-beta log 2)`.  Taking norms, summing, and bounding the finite prime mass by the complete summable mass proves

```text
norm (D^m G_(P,beta)(z) - D^m H_P(z))
  <= m! exp(-beta log 2) eta^(-(m+1)) M(u).
```

The previously proved exact Hermitian Gibbs response identity transports this estimate verbatim to the physical response.

For the compact-open conclusion, local uniform convergence of holomorphic functions is stable under one derivative.  Induction on `m`, using holomorphy of every finite Gibbs carrier on the upper half-plane, proves local uniform convergence of every derivative function in the unchanged product filter `atTop` on `Finset Nat.Primes x Real`.

## Lean certificate

- `iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform`
- `iteratedDeriv_add_real_inv`
- `iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_sub_eq`
- `norm_iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_sub_le`
- `norm_iteratedDeriv_finiteHermitianGibbsResponse_sub_le`
- `iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_tendstoLocallyUniformlyOn_joint`
- `iteratedDeriv_finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint`
- `universalFacetOrbitGauge_iteratedDeriv_finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint`

## Log

- 2026-07-14 -- Selected after rejecting reversible-network and Fisher/Hellinger candidates that did not discharge a live source hypothesis, and after confirming that reflection positivity and complete-monotonicity bridges are already saturated in the corpus.
- 2026-07-14 -- Proved the sharp all-order factorial/resolvent identity, the subsystem-independent upper-strip Boltzmann estimate, its exact Hermitian response form, and locally uniform convergence of every derivative function.  Target build passed with 8,555 jobs; full `HTGeometry` build passed with 9,127 jobs.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; formal lint passed.
