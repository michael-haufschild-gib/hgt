# Arithmetic tail charge of completed unit-Riesz coherent response

- **ID:** `ccm-unit-riesz-coherent-arithmetic-tail-charge`
- **Stage:** 3-formalized
- **Type:** EXACT SOURCE CLASSIFICATION / DIRECT-HG NO-GO / ARITHMETIC INVARIANT
- **Scientific status:** `[UNCONDITIONALLY PROVED IN LEAN]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [EXTERNAL PRIORITY UNVERIFIED] [NOT AN RH PROOF]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/CCMUnitRieszCoherentTailCharge.lean`
- **Parent modules:**
  `CCMUnitRieszExponentialCoherentTrace.lean` and
  `CCMUnitRieszCoherentGraphHankelWeld.lean`.

## Result

The exponential increment kernel has exact right-tail decomposition

```text
K(p,u) = (1-exp(-p/2)) + exp(-u/2)(exp(p/2)-1),   p<=u.
```

Hence finite coherent packet `sum c_p K(p,u)` has constant tail charge

```text
A(c,p)=sum c_p(1-exp(-p/2)).
```

For literal unit-Riesz prime frame at integer aperture `N`, Lean proves

```text
A_prime(N) = E_prime(N)/2.
```

For matching polar continuum it constructs and evaluates actual lag integral

```text
P_N(u)=sqrt(N) integral_0^infinity exp(-p) K(p,u) dp
      =sqrt(N)(1/3+exp(-u/2)-(4/3)exp(-u)).
```

Thus polar constant tail charge is `sqrt(N)/3=E_polar(N)/2`. Completed response

```text
C_N(u)=primeResponse_N(u)-P_N(u)
```

has exact large-lag formula

```text
C_N(u)
 = R_1(log N)/2
   + exp(-u/2)(B_prime(N)-sqrt(N))
   + (4/3)sqrt(N)exp(-u),                 u>=log N,
```

and therefore

```text
lim_(u->infinity) C_N(u) = R_1(log N)/2.
```

Lean proves `C_N(u)->0` iff `R_1(log N)=0`. If this resolvent is nonzero, `C_N^2` is not
integrable on any right ray and direct complex amplitude profile is not an HG `LeakProfile`.

## Scientific consequence

Graph-Hankel weld from preceding result cannot be applied directly to literal completed coherent
response. Failure is not missing estimate: exact obstruction is arithmetic tail charge equal to
half completed unit-Riesz resolvent. Direct HG embedding would require pointwise resolvent
vanishing at every integer aperture, far stronger and differently oriented than needed RH bound.

Therefore source-faithful codiagonal/aperture differencing is forced. It must cancel constant charge
without deleting `R_1`; deleted charge must reappear as boundary counterterm or discrete flux. This
identifies literal object next theorem must construct and rules out treating tail subtraction as
harmless normalization.

## Claim-to-Lean closure

| Claim | Declaration |
|---|---|
| finite-kernel right-tail law | `unitExponentialIncrementKernel_eq_rightTail` |
| finite packet charge/mode decomposition | `unitExponentialFiniteKernelResponse_eq_rightTail` |
| prime tail charge equals half energy | `unitRieszCoherentPrimeKernelTailCharge_eq` |
| exact prime response tail | `unitRieszCoherentPrimeKernelResponse_eq_rightTail` |
| actual polar lag response | `unitExponentialPolarKernelResponse`, `unitRieszCoherentPolarKernelResponse` |
| polar integral closed form | `unitExponentialPolarKernelResponse_eq`, `unitRieszCoherentPolarKernelResponse_eq` |
| completed response tail | `unitRieszCoherentCompletedKernelResponse_eq_rightTail` |
| completed tail limit | `tendsto_unitRieszCoherentCompletedKernelResponse` |
| decay iff resolvent zero | `tendsto_unitRieszCoherentCompletedKernelResponse_zero_iff` |
| nonzero tail implies square nonintegrability | `not_integrableOn_sq_of_tendsto_atTop_ne_zero`, `not_integrableOn_sq_unitRieszCoherentCompletedKernelResponse` |
| direct HG amplitude rejected | `not_leakProfile_unitRieszCoherentCompletedAmplitudeProfile` |

## Theatre and novelty audit

Tail expansion of one exponential kernel and elementary exponential integration are classical and
not claimed as new. Candidate novelty is exact arithmetic composition:

```text
coherent constant tail charge
 = (prime coherent energy - polar coherent energy)/2
 = completed Chebyshev resolvent/2,
```

together with formal nonintegrability/no-HG consequence. Targeted corpus and primary-source arXiv
searches around Connes--Consani semi-local trace formulas, Weil positivity, unit-Riesz criteria,
Hankel boundary traces, and exponential-kernel graph norms found no exact statement. External
priority remains unverified.

## Open core

Canonical charge-cancelling codiagonal and no-loss boundary reconstruction are now closed by
`CCMUnitRieszCoherentRelativeCarrier.lean`. Remaining core is prove its graph energy/boundary slope
admits a source-specific summable-dual or four-unit law strong enough to control reconstructed
charge. Generic HG integrability cannot bound unweighted translation series.

## Gates

- [x] finite packet tail classification
- [x] prime tail charge identified
- [x] polar continuum integrated exactly
- [x] completed tail identified with literal resolvent
- [x] nonintegrability and direct-HG no-go formalized
- [x] unconditional Lean proof
- [ ] independent mathematical audit
- [ ] external priority audit
- [x] canonical source-faithful charge codiagonal
- [x] exact reconstruction of removed charge from bulk translates
- [ ] four-unit boundary flux bound
- [ ] RH endpoint

## References

- A. Connes, C. Consani, M. Marcolli, *The Weil proof and the geometry of the adeles class space*,
  arXiv:math/0703392.
- A. Connes, C. Consani, *The Scaling Hamiltonian*, arXiv:1910.14368.
- A. Connes, C. Consani, *Weil positivity and Trace formula, the archimedean place*,
  arXiv:2006.13771.

## Log

- 2026-08-16 -- Derived finite coherent right-tail charge/mode decomposition.
- 2026-08-16 -- Computed actual polar lag response and exact prime/polar charges in Lean.
- 2026-08-16 -- Proved completed tail equals half literal unit-Riesz resolvent.
- 2026-08-16 -- Proved square nonintegrability and direct-HG leak rejection away from zero
  resolvent.
- 2026-08-16 -- Follow-up relative-carrier module closed canonical codiagonal, HG admission, and
  exact boundary-charge reconstruction.
