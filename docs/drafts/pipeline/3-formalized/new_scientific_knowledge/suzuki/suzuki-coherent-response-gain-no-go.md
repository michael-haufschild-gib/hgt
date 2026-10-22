# Suzuki coherent response vanishing-gain law

- **ID:** `suzuki-coherent-response-gain-no-go`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-coherent-response-gain-no-go-formalized.md`
- **Type:** SOURCE-SPECIFIC NO-GO / SHARP BOUNDARY LAW
- **Scientific status:** `[PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCoherentResponseGainNoGo.lean`

## Result

For fixed `h>0`, actual causal valuation-depth fusion obeys

```text
|R_(a,t,p)| <= C_h B_p/(p+1),
C_h=(h sqrt(h))^(-1)(1-exp(-(log 2)/4))^(-1),
```

where `B_p` is observer-free depth-zero critical wall amplitude. At moving-wall aperture

```text
a_p=(log p+1)/2,
```

unit-width sharp rectangular gate is exactly one for `log p>=1`, so sharp wall diagonal is exactly
`B_p^2`. Therefore, for every finite inverse gain `M>=0` and every height `t`, some prime satisfies

```text
M |R_(a_p,t,p)| < B_p.
```

The coherent causal response is not uniformly bounded below on exact sharp wall source.

## Proof dependencies

1. Exact observer factorization:
   `EndpointAmplitude = BareAmplitude * CubicInnovation`.
2. At depth zero, cubic innovation contains exact factor `1/(p+1)`.
3. Exact causal Möbius law and uniform disk-radius cap below one.
4. Exact four-tent rectangular autocorrelation at moving-wall center.
5. Unboundedness of primes.

No Xi zero, RH premise, Weil sign, zeta estimate, or numerical computation occurs.

## Frontier consequence

Bounded/frame-preserving reading of `SUZUKI-COHERENT-FUSION-GAMMA-WELD` is false. Cross-prime
coherent covariance exists, but cannot restore lost sharp-source scale through bounded inverse.
Surviving Suzuki mechanism must construct closed unbounded relative observation with at least
linear prime gain, absorb it into cutoff-dependent prime--Burnol completion, and then prove
cutoff-uniform completed lower floor.

This kills one implementation class, not Suzuki's full operator program and not RH.

## Lean status

Direct module check passes. Capstone axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

