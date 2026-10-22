# Hedenmalm theta prime quantile Haar carrier

- **ID:** `hedenmalm-theta-prime-quantile-haar-carrier`
- **Stage:** 1-in-progress
- **Label:** `P-G106`
- **Type:** `[CONJECTURE LOOP] [ROUTE-P CARRIER CLASSIFICATION] [NO COMPUTATION]`
- **Parents:** `HedenmalmThetaPrimeTranslationQuantileFlow.lean`,
  `HedenmalmThetaPrimeTranslationFixedFibre.lean`,
  `HedenmalmThetaPrimeTranslationHaarCarrier.lean`

## Frozen conjecture

Let `F` be the theta source CDF, `Q=F⁻¹`, and

```text
Phi_n(t) = F(Q(t) + log n).
```

Push additive Haar measure on `R` through `F`:

```text
nu_theta = F_* dx.
```

Prove:

1. `Phi_n` preserves `nu_theta` for every positive integer `n`; `[LEAN-PROVED]`
2. `nu_theta` is supported on `(0,1)` and has infinite total mass; `[LEAN-PROVED]`
3. in the natural sigma-finite regular carrier class, invariance under the completed
   prime-translation group forces a scalar multiple of `nu_theta`;
4. consequently no nonzero finite invariant measure can carry the full prime flow.

In density coordinates, `d nu_theta = q(t) dt`, where `q=Q'` is quantile speed. Thus the same
blow-up that prevents fixed reciprocal-source admission in P-G104 is the Jacobian forced by prime
covariance, not a removable analytic defect.

## Conjecture loop audit

- Centered-CDF boundary-window decomposition was rejected: corpus already proves that moving
  boundary is an exact flat projection coboundary.
- Haar-`L2` injectivity does not identify reflected responses: they have distinct resolvent
  eigenvalues even though their forcing agrees.
- Haar-core virial detects horizontal displacement but does not annihilate it; it is a receiver.
- Invariant-carrier classification survives these failures because it concerns source flow before
  divisor specialization and makes no zero-location hypothesis.

## Significance gate

This theorem would rule out every finite stationary prime fibre at once and force Route P into a
sigma-finite/rigged completion. It would also give a literal continuous carrier comparison with
the bilateral Deninger translation representation. It does not prove RH by itself; progress is the
classification of the only covariant carrier on which the P-G103 anomaly is admitted.

## Falsifiers

- If `F_* dx` is not invariant under `Phi_n`, the proposed carrier is wrong.
- If a nonzero finite regular measure is invariant under the completed prime group, the finite-
  fibre no-go fails.
- If uniqueness needs divisor values or RH, it is circular and must be retired.

## Gates

- [x] prior Route P and failed-boundary corpus audited
- [x] conjecture frozen
- [x] invariance proved on paper and in Lean
- [x] support, compact-interval quantile-length law, and infinite-mass theorem proved in Lean
- [x] every finite supported invariant measure excluded already by one genuine integer flow
- [ ] sigma-finite regular uniqueness up to scale proved
- [ ] bilateral Deninger comparison constructed

## Lean status

Umbrella-wired module
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaPrimeQuantileHaarCarrier.lean` proves
`measurePreserving_thetaIntegerQuantileFlow`, `thetaQuantileHaarMeasure_Icc`,
`thetaQuantileHaarMeasure_compl_Ioo`, `thetaQuantileHaarMeasure_Ioo`, and
`finiteMeasure_eq_zero_of_map_thetaIntegerQuantileFlow_eq_self`. Direct Lean check and exact module
build pass.
