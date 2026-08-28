# FCRJ theta--Abel rank-one provider

- **ID:** fcrj-theta-abel-rank-one-provider
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/critical-multiplicative-compensated-cancellation-rh.md
- **Statement:** Complete fixed-support physical FCRJ energy is exactly raw `L²` mass of an explicit normalized Chebyshev-theta Abel response minus its rank-one aperture mean.

## Goal

Remove every coefficient, clipping, Hilbert-realization, and centering ambiguity from fixed-ratio
FCRJ. Leave one source-pure analytic provider: an `L²` estimate for normalized theta error after
the exact two-endpoint Abel transform.

## Gates

- [x] 0 → 1  in-progress: exact corpus definitions and support packet fixed
- [x] 1 → 2  fully-proven: dependency-closed paper proof and Lean proof
- [x] 2 → 3 formalized: direct check, targeted build, and axiom audit pass; global lint blocked by unrelated unwired modules
- [ ] 3 → 4  publication-ready: standalone exposition and external novelty review

## Statement

Let

```text
P(A,m,k)={p prime : m-A < log p <= k},
q(h)=[theta(exp h)-exp h] exp(-h),
R(m,k;u)=q(k-u)-q(m-u)+integral_(m-u)^(k-u) q(h) dh.
```

For `0<A` and `m<=k`, Abel summation gives pointwise

```text
sum_(m-u<log p<=k-u) log p/p -(k-m)=R(m,k;u).
```

Weighted clipping correction is exactly response mean:

```text
L(P,A,m,k)/A-(k-m)=(1/A) integral_0^A R(m,k;u) du.
```

Consequently complete fusion energy obeys exact rank-one decomposition

```text
Energy(P,A,m,k)
 = integral_0^A R(m,k;u)^2 du
   -(1/A)(integral_0^A R(m,k;u) du)^2
 <= integral_0^A R(m,k;u)^2 du.
```

Thus any uniform `|R|<=B` on aperture gives `Energy<=A B^2`.

## Proof

1. Map floor-defined natural-prime log window bijectively to prime-subtype packet.
2. Prove exact support restriction for every aperture position.
3. Specialize corpus prime-window Abel formula to `G(h)=exp(-h)`; continuum integrand is exactly
   one and derivative contributes normalized theta error.
4. Integrate raw moving flux to weighted clipped length, proving correction equals response mean.
5. Use scalar representative of complex Hilbert carrier and expand square about exact mean.
6. Integrability follows from finite indicator sums and a uniform finite-sum norm bound.

No inequality occurs before final rank-one projection bound.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelVariance.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Targeted build: PASS
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- Capstones:
  - `sum_primeLogWindow_log_div_sub_width_eq_thetaDiscrepancy`
  - `xiPhysicalPrimeLogApertureWeightedLengthMass_div_sub_width_eq_mean_thetaAbelResponse`
  - `xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_eq_thetaAbelRaw_sub_meanSq`
  - `xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_le_mul_sq_of_response_bound`

## Novelty audit

Abel summation, variance decomposition, and Chebyshev-theta discrepancy are classical. Targeted
corpus and primary-literature audit found adjacent Selberg-integral and short-interval variance
work, but no coefficient-exact synthesis with this clipped physical packet, `log p/p` weight,
Hilbert carrier, and rank-one clipping correction. Candidate-new content is restricted to that
source-specific exact identification and provider reduction. It is not an RH proof.

## Log

- 2026-08-27 — paper proof, Lean proof, targeted build, umbrella wiring, and axiom audit complete
