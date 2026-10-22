# CCM-FU third-grade Cesàro completeness

- **ID:** `ccm-fu-c74-third-grade-cesaro-completeness`
- **Stage:** 3-formalized
- **Label:** `C74`
- **Source:** `rh-current-frontier-map.md`, CCM-FU; C72 cubic Abel completeness; C73
  subcubic grade--growth completeness
- **Statement:** Linear growth of one Cesàro primitive of the literal third-grade
  prime-minus-polar cumulative source gives a second Abel continuation of the regularized critical
  Mellin defect and therefore implies RH. Contrapositively, non-RH forces superlinear Cesàro
  excursions beyond every positive wall.

## Conjecture loop

The first conjecture was that the unconditional square-root-scale completed-error estimate might
feed C73 after the inverse-cubic grade. It fails: the known envelope remains exponential and does
not imply any fixed subcubic pointwise estimate.

The second conjecture was that bounded Xi-screw values should control the literal source slope. It
fails without a new variation or monotonicity theorem: a bounded primitive need not control its
pointwise derivative, and the source is signed.

The third conjecture was to replace the moving endpoint current by a triangular reporter. That
remains a possible producer, but proving its forward source estimate first would add an unnecessary
dependency to the analytic endpoint.

The successful pivot integrates the literal cumulative source once before taking its Abel
transform. Put

```text
q_b(H) = ccmGuinandWeilThirdGradeCumulativeMeasurable b H,
Q_b(H) = integral_b^H q_b(h) dh.
```

Conjecture C74 asserts that

```text
there exist C>=0 and b>0 such that |Q_b(H)| <= C(H+1) for every H>b       (1)
```

is already RH-complete. This passed a dependency-closed paper proof and exact Lean formalization.
It is strictly broader than C72 boundedness of `q_b` and C73's fixed pointwise subcubic envelopes:
`q_b` may have arbitrarily large oscillatory excursions while its signed primitive obeys `(1)`.

## Theorem C74

For `b>0`, define

```text
B2_b(u) = u^2 integral_(b,infinity) exp(-uH) Q_b(H) dH.               (2)
```

If `(1)` holds, then:

1. the integral in `(2)` and `B2_b` are analytic on `Re(u)>0`;
2. on the safe real ray `r>1`, finite-interval absolute-continuity integration by parts, followed
   by endpoint damping, gives

   ```text
   integral_(b,infinity) exp(-rH) q_b(H) dH
     = r integral_(b,infinity) exp(-rH) Q_b(H) dH;                    (3)
   ```

3. both sides have analytic continuations on `Re(u)>1`, so the identity theorem extends `(3)` to
   that half-plane and identifies `B2_b` with C72's first Abel source continuation;
4. three complex derivatives recover the same literal prime-minus-polar tail Mellin defect;
5. after the shift `u=s+1/2` and addition of the entire wall head, the resulting critical Mellin
   extension is analytic on `Re(s)>-1/2` and equals the regularized critical Mellin defect on
   `Re(s)>0`;
6. the existing continuation-to-zero-location theorem yields `RiemannHypothesis`.

Consequently,

```text
not RH -> for every b>0 and C>=0, some H>b has
          C(H+1) < |Q_b(H)|.                                       (4)
```

The proof introduces no estimate on zeta zeros and no zero list. The only unresolved premise is
the literal source-side average cancellation `(1)`.

## New knowledge and route consequence

C72 and C73 made pointwise source size the apparent boundary. C74 shows that boundary was an
artifact of taking absolute values before exploiting cancellation. One source primitive lowers the
growth order seen by exponential damping: linear primitive growth becomes an analytic Laplace
tail, while integration by parts returns the original spectral source on the safe half-plane.

This exposes a higher principle for the route:

```text
source primitive order <-> admissible cancellation order <-> half-plane gained by Abel tilt.
```

Earlier failures of scalar damping and separate prime/polar estimates are shadows of ignoring this
order-lowering operation. CCM-FU's first open theorem is now the averaged source law `(1)`, not a
pointwise subcubic completed-error estimate. A triangular reporter or another arithmetic
cancellation device is useful only if it proves `(1)` or a genuinely weaker continuation premise.

## Hostile novelty and theatre audit

Corpus search found first-Abel cubic completeness, pointwise subcubic completeness, and generic
summation-by-parts infrastructure, but no theorem converting linear growth of this literal
third-grade Cesàro primitive into the critical Mellin continuation or the superlinear non-RH law
`(4)`. The route literature exchange found no external theorem supplying either this
prime-minus-polar estimate or this corpus-specific second-Abel weld.

This is significant but not RH itself. It weakens the exact source producer from pointwise control
to signed average control and proves that non-RH must defeat every linear Cesàro budget. It does not
assume or prove `(1)` unconditionally, so RH and its negation remain open.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/CCM/CCMGuinandWeilThirdGradeCesaroCompleteness.lean
```

Main declarations:

- `ccmCesaroPrimitive`;
- `analyticOnNhd_ccmSecondAbelLaplaceTail_of_linear`;
- `intervalIntegral_exp_mul_thirdGradeCumulative_eq_boundary_add`;
- `integral_Ioi_exp_mul_thirdGradeCumulative_eq_cesaro`;
- `ccmSecondAbelCumulativeSourceContinuation_eq_first`;
- `iteratedDeriv_three_ccmSecondAbelCumulativeSourceContinuation_eq_tailDefect`;
- `ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension_eq_regularized_of_linear`;
- `riemannHypothesis_of_ccmGuinandWeilThirdGradeCesaroLinearBound`;
- `ccmGuinandWeilThirdGradeCesaroPrimitive_superlinear_of_not_riemannHypothesis`.

Verification:

- direct check passed: `lake env lean GaloisForLFunctions/RHTower/CCM/CCMGuinandWeilThirdGradeCesaroCompleteness.lean`;
- exact leaf build passed;
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- umbrella import wired; umbrella not built.

## Gates

- [x] dependency-closed paper theorem
- [x] exact Lean formalization without `sorry`, `admit`, project axiom, `opaque`, or `unsafe`
- [x] direct-file verification
- [x] exact leaf build
- [x] axiom audit
- [x] umbrella wired without umbrella build
- [ ] unconditional literal source-side Cesàro-linear producer
- [ ] unconditional RH
