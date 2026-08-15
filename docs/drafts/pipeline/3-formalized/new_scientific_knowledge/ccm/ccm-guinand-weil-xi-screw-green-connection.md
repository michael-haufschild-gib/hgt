# CCM completed third grade as Xi-screw Green curvature

- **ID:** `ccm-guinand-weil-xi-screw-green-connection`
- **Stage:** 3-formalized
- **Route:** CCM-FU
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [CORPUS-NEW] [NO EXACT EXTERNAL COLLISION FOUND]`
- **RH used:** no
- **Computation used:** no
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilXiScrewGreenConnection.lean`

## Claim

Suzuki's positive-time screw splits exactly into smooth polar--Gamma part minus prime hinges. Its
canonical right slope satisfies

```text
screwRightSlope(h)
 = E(h) + screwLinearCoeff/2 - screwLerchTail1(h),        (C71.1)
```

and its affine codiagonal is the Green primitive of the literal completed source. Two integrations
by parts give, for the forced inverse-cubic weight, an exact identity

```text
completedThirdGradeRate(b,H) = xiScrewThirdGradeGreen(b,H). (C71.2)
```

Therefore Xi-screw Green convergence, completed third-grade convergence, and C70's completed-error
flux convergence are equivalent.

## Proof and significance

The prime-hinge Green identity and smooth Green identity are proved separately and then sewn
without a zero-location or RH assumption. The codiagonal is also identified with the literal Xi
zero divisor after affine base-wall normalization.

This closes the previously open “identify with Suzuki and Xi Ward” task. The route is no longer
missing a target bridge; it is missing a tail theorem for one explicitly identified divisor Green
functional.

## Novelty audit

Suzuki's papers provide the screw function and RH criteria. External search found no inverse-cubic
finite-window Green identity or three-way convergence equivalence matching C71.

## Lean audit

Direct Lean check and targeted module build pass. Axiom audit reports only standard Lean axioms.
