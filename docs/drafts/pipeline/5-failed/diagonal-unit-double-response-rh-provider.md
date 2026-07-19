# Diagonal unit--double response as an RH provider

- **ID:** `diagonal-unit-double-response-rh-provider`
- **Stage:** `5-failed`
- **Type:** no-go / positive survivor / response-lift classification
- **Scientific status:** `[ROUTE RETIRED] [POSITIVE SURVIVOR LEAN-PROVED]`
  `[NOT RH] [NOVELTY UNVERIFIED]`
- **Sources:** `XiAperturePhysicalEndpointResponseRenormalization.lean`,
  `XiPhysicalPrimeLogApertureHilbertMetric.lean`, and the corrected `(AC25)` frontier
- **Consumer:** source-defined off-diagonal prime--Gamma response lift

## Candidate and exact cancellation

For every ordinary prime put

```text
w_p = log(p)/p,
j_p = log(p)[F_2(p)-F_1(p)] = -log(p)/(p+1),
e_p = log(p)/(p(p+1)).                                  (DS1)
```

Complete unit--double valuation fusion already proves

```text
w_p+j_p=e_p.                                             (DS2)
```

Let `E` be any real module, let `P` be any finite prime packet, and assign completely arbitrary
features `v_p in E`.  Linearity upgrades `(DS2)` before any norm, Gram compression, clipping, or
prime joining:

```text
sum_(p in P) w_p v_p + sum_(p in P) j_p v_p
  = sum_(p in P) e_p v_p.                                (DS3)
```

In particular `(DS3)` holds for the actual centered clipped-aperture vectors `kappa_p`.  Since
`e_p>0` and `e_p<=log(p)/p^2`, the completed carrier is trace class and, on a physical packet
`p>M exp(-A)`, has the required inverse-square scale independently of the arrangement of the
prime-log locations.

## Killing theorem

The candidate identification

```text
actual joined AC25 response current = sum_p j_p kappa_p   (DS4)
```

cannot be the missing RH theorem.  Equation `(DS3)` would then produce the target aperture bound
for every arbitrary finite support, including supports with no prime-distribution law at all.
The cancellation is diagonal in the prime label and occurs coefficientwise.  It therefore cannot
encode the RH-equivalent cross-prime response saturation exposed by `(HGS29)`.

This is stronger than saying that `(DS2)` is elementary.  It classifies the failure: the exact
linearization is admissible, but any response which stops at that diagonal linearization is blind
to the ratio-knot joining measured by the true aperture Hilbert metric.

## Positive survivor: constrained off-diagonal lift

The unit--double current is not discarded.  It fixes the linear part of the only remaining
response shape.  A viable completed response `R` must satisfy all of the following:

1. its one-prime linearization is the source-forced coefficient `j_p` in `(DS1)`;
2. it is genuinely off-diagonal in prime labels before Hilbert/Gram compression;
3. its quadratic prime-pair part retains the filtered-Xi coefficient
   `log(p)log(q)(1-p^(-2))(1-q^(-2))/(pq)` up to the already controlled inverse-cubic correction;
4. it couples different logarithmic ratio knots, rather than cancelling each prime coordinate;
5. after the complete `h,p,a,r` joining it equals the corrected response in `(AC28)`, not a newly
   defined replacement response.

The next conjecture is therefore an **off-diagonal response-lift identity**, not a diagonal
estimate: construct the completed prime--Gamma operator whose linear trace is `(j_p)` and whose
regularized quadratic correlation is the actual joined `(AC25)` response.  Only then can the
inverse-square remainder in `(DS3)` legitimately transfer to the RH carrier.

## No-go closure

- **Exact killing mechanism:** universal module identity `(DS3)` makes the proposed cancellation
  support-blind.
- **Strongest positive statement:** unit--double fusion uniquely fixes the linear countercurrent
  of every viable off-diagonal response lift.
- **What not to try again:** do not identify the diagonal current carrier itself with the joined
  response, and do not advertise its unconditional inverse-square residual as an RH estimate.
- **Lean:** `XiDiagonalFusedResponseSupportBlindness.lean` proves `(DS3)` for an arbitrary real
  module, specializes it to the true physical aperture Hilbert carrier, and proves the exact
  norm-square residual identity.  The direct leaf, exact target build, and axiom audit pass; the
  public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- **Remaining open core:** construct and identify the source-defined off-diagonal completed
  prime--Gamma response operator.
