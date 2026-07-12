# Gamma damping carries the complete finite prime-log Cauchy core

- **ID:** `gamma-damped-prime-log-cauchy-domain`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Source:** `GammaDampedPrimeLogCauchyDomain.lean`, `PrimeLogCauchySeamRank.lean`, and
  `SoninSemilocalTwoPlaceAssociation.lean`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`

## Exact positive carrier theorem

Put

```text
phi(t)=(cosh t)^(-1/2)
```

and, for a finite Cauchy packet with nodes `z_j` and coefficients `c_j`, define

```text
G_(z,c)(p)=phi(2 log p)
  * |sum_j c_j/(z_j-log p)|^2.                            (1)
```

Lean proves unconditionally

```text
sum_p G_(z,c)(p)<infinity                                (2)
```

for every finite packet whose nodes avoid the prime-log support, in particular for every packet in
the upper half-plane. The Lean summability theorem is stated for arbitrary complex nodes because
Lean's field inverse is total; the analytic route uses the upper-half-plane specialization, where
no pole collision occurs.

For distinct upper-half-plane nodes, the theorem is paired with the exact prime-only statement at
the critical half-weight:

```text
sum_p |sum_j c_j/(z_j-log p)|^2<infinity
  iff c=0.                                                (3)
```

Thus Gamma sewing changes the domain of the entire finite Cauchy core, not only one normalized
feature.

## Proof

The canonical Gamma diagonal satisfies

```text
phi(2t)<=sqrt(2) exp(-t).                                 (4)
```

For fixed finite packet data, the reverse triangle inequality gives, eventually in `t`,

```text
|sum_j c_j/(z_j-t)|
  <=2(sum_j |c_j|)/t.                                    (5)
```

At `t=log p`, equations `(4)`--`(5)` yield

```text
G_(z,c)(p)
  <=4 sqrt(2)(sum_j |c_j|)^2/(p(log p)^2).                (6)
```

The natural-number majorant

```text
sum_(n>=2) 1/(n(log n)^2)
```

is summable by the Cauchy condensation test, so its restriction to the primes is summable. This
proves `(2)`. Equation `(3)` is the already formalized finite-packet independence theorem from
`PrimeLogCauchySeamRank.lean`.

## Positive CCM consequence

The line-211 all-finite-order wall and the present theorem together identify an exact carrier
transition:

```text
prime positive Cauchy carrier at the critical half-weight
  + canonical doubled-frequency Gamma diagonal
  -> complete finite Cauchy Hilbert domain.               (7)
```

The required resource is therefore not merely "more decay." It is one full inverse-prime
archimedean order sewn before completion. The Gamma diagonal supplies exactly that order and
repairs every finite resolvent packet simultaneously.

This does not identify the Gamma-damped norm with the Xi Weil polarization. Its coherent Gram has
positive off-diagonal prime covariance, whereas the Euler logarithmic source is additive. The live
CCM theorem remains a source-selected relative-trace or Schur-complement identity that retains the
domain repair `(7)` while converting the covariance into the completed Weil form.

## Lean declarations

```text
RHTower.summable_invNatLogSq
RHTower.summable_prime_invNatLogSq
RHTower.gammaDampedPrimeLogCauchyPacketEnergy
RHTower.eventually_gammaDampedPrimeLogCauchyPacketEnergy_le
RHTower.summable_gammaDampedPrimeLogCauchyPacketEnergy
RHTower.gammaDampedPrimeLogCauchyPacket_critical_carrierTransition
```

## Verification

- `lake env lean GaloisForLFunctions/RHTower/GammaDampedPrimeLogCauchyDomain.lean` -- pass
- `lake build GaloisForLFunctions.RHTower.GammaDampedPrimeLogCauchyDomain` -- pass
- capstone axioms: `[propext, Classical.choice, Quot.sound]`
- aggregate `RHTower.lean` check is presently blocked by unrelated pre-existing failures in the
  concurrently modified `SummableEulerCalkinInjectivity.lean`; the new module and all of its direct
  dependencies build independently

## Gates

- [x] all finite Gamma-damped Cauchy packets proved summable
- [x] exact prime-only versus Gamma-sewn critical carrier transition formalized
- [x] positive inverse-prime resource stated
- [ ] derive this diagonal from the actual Gauss-paired Hardy--Titchmarsh/Sonin source operator
- [ ] identify the resulting relative covariance with the Xi Weil polarization
- [ ] prove cofinal positivity / RH
